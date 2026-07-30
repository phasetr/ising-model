#!/usr/bin/env python3
"""Validate completion-claim evidence against an offline pull-request snapshot.

The supplied context is the trusted boundary.  Pull-request Markdown is
untrusted input.  This module deliberately performs no repository discovery,
process execution, network access, or credential handling.
"""

from __future__ import annotations

import argparse
import hashlib
import html
import json
import re
import sys
import unicodedata
from pathlib import Path, PurePosixPath
from typing import Any
from urllib.parse import urlsplit

SCHEMA_VERSION = 1
BLOCK_INFO = "completion-claims-v1"
BLOCK_FENCE = "```completion-claims-v1"
PENDING = "PENDING"
PASS = "PASS"
FAIL = "FAIL"
DRAFT_INCOMPLETE = "DRAFT_INCOMPLETE"
HUMAN_REVIEW_REQUIRED = "HUMAN_REVIEW_REQUIRED"

EXIT_PASS = 0
EXIT_FAIL = 1
EXIT_DRAFT_INCOMPLETE = 2

MAX_CONTEXT_BYTES = 512 * 1024
MAX_BODY_BYTES = 1024 * 1024
MAX_CHANGED_PATHS = 10_000
MAX_PATH_BYTES = 4_096
MAX_REVIEW_RECORDS = 16
MAX_SEMANTIC_CLAIMS = 1_000
MAX_HISTORY_FACTS = 10_000
MAX_TEXT_BYTES = 16_384

SHA_RE = re.compile(r"[0-9a-f]{40}\Z")
DIGEST_RE = re.compile(r"sha256:[0-9a-f]{64}\Z")
NON_CLOSING_RE = re.compile(r"(Refs|Part of) #([1-9][0-9]*)\Z")
OFFICIAL_CLOSE_KEYWORDS = (
    "close",
    "closes",
    "closed",
    "fix",
    "fixes",
    "fixed",
    "resolve",
    "resolves",
    "resolved",
)
CLOSE_KEYWORD_PATTERN = r"(?:" + "|".join(OFFICIAL_CLOSE_KEYWORDS) + r")"
OWNER_REPO_PATTERN = r"[A-Za-z0-9](?:[A-Za-z0-9-]{0,38})/[A-Za-z0-9_.-]+"
ISSUE_URL_PATTERN = (
    r"https?://github\.com/" + OWNER_REPO_PATTERN + r"/(?:issues|pull)/[1-9][0-9]*"
)
ISSUE_REFERENCE_PATTERN = (
    r"(?:#[1-9][0-9]*|"
    + OWNER_REPO_PATTERN
    + r"#[1-9][0-9]*|"
    + ISSUE_URL_PATTERN
    + r")"
)
MARKDOWN_SEPARATOR_PATTERN = r"""[\s:;,.\-–—!?()[\]{}*_~`'"<>|/\\]{0,64}"""
CLOSING_RE = re.compile(
    r"\b"
    + CLOSE_KEYWORD_PATTERN
    + r"\b"
    + MARKDOWN_SEPARATOR_PATTERN
    + ISSUE_REFERENCE_PATTERN,
    re.IGNORECASE,
)
NON_CLOSING_BODY_RE = re.compile(
    r"\b(?:Refs|Part\s+of)\b"
    + MARKDOWN_SEPARATOR_PATTERN
    + r"(?P<reference>"
    + ISSUE_REFERENCE_PATTERN
    + r")",
    re.IGNORECASE,
)
ISSUE_MENTION_RE = re.compile(ISSUE_REFERENCE_PATTERN, re.IGNORECASE)
FUTURE_PLAN_RE = re.compile(
    r"\b(?:future|later|next\s+phase|phase\s+[0-9]+|plan(?:ned)?|"
    r"remain(?:s|ing)?|todo|follow[- ]?up|will)\b",
    re.IGNORECASE,
)
FENCE_OPEN_RE = re.compile(r"^( {0,3})(`{3,}|~{3,})([^\r\n]*)$")
HISTORY_ACTIONS = frozenset({"added", "modified", "deleted"})

CLAIM_LEVELS = frozenset(
    {
        "build_health",
        "source_axiom_health",
        "exact_candidate_diff",
        "bounded_tracker_completion",
        "theorem_api_contract",
        "repository_wide_completion",
    }
)
SEMANTIC_CLAIM_LEVELS = frozenset(
    {
        "bounded_tracker_completion",
        "theorem_api_contract",
        "repository_wide_completion",
    }
)
REVIEW_KINDS = frozenset({"source_review", "issue_resolution_audit"})
SEMANTIC_KINDS = frozenset({"source", "theorem", "provenance"})

CONTEXT_KEYS = frozenset(
    {
        "schema_version",
        "is_draft",
        "delivery",
        "base_sha",
        "head_sha",
        "changed_paths",
        "allowed_issue_refs",
        "history_facts",
    }
)
PAYLOAD_KEYS = frozenset(
    {
        "schema_version",
        "candidate",
        "claim_levels",
        "review_records",
        "references",
        "semantic_claims",
        "history_claims",
    }
)
CANDIDATE_KEYS = frozenset(
    {"base_sha", "head_sha", "changed_file_count", "sorted_path_digest"}
)
REVIEW_KEYS = frozenset({"kind", "head_sha", "url"})
REFERENCE_KEYS = frozenset({"non_closing", "closing"})
SEMANTIC_KEYS = frozenset({"id", "kind", "statement", "evidence_urls"})
HISTORY_KEYS = frozenset({"commit_sha", "path", "action"})


class GateInputError(ValueError):
    """A deterministic fail-closed input error with a stable diagnostic code."""

    def __init__(self, code: str, message: str) -> None:
        super().__init__(message)
        self.code = code
        self.message = message


def _duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise GateInputError("DUPLICATE_JSON_KEY", f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _parse_json(text: str, label: str) -> Any:
    try:
        return json.loads(text, object_pairs_hook=_duplicate_keys)
    except GateInputError:
        raise
    except (json.JSONDecodeError, RecursionError) as error:
        raise GateInputError("MALFORMED_JSON", f"{label}: {error}") from error


def _read_utf8(path: Path, limit: int, label: str) -> str:
    try:
        raw = path.read_bytes()
    except OSError as error:
        raise GateInputError("INPUT_READ_ERROR", f"{label}: {error}") from error
    if len(raw) > limit:
        raise GateInputError("INPUT_TOO_LARGE", f"{label} exceeds {limit} bytes")
    try:
        return raw.decode("utf-8")
    except UnicodeDecodeError as error:
        raise GateInputError("INVALID_UTF8", f"{label}: {error}") from error


def _object(value: Any, where: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise GateInputError("INVALID_TYPE", f"{where} must be an object")
    return value


def _array(value: Any, where: str, limit: int) -> list[Any]:
    if not isinstance(value, list):
        raise GateInputError("INVALID_TYPE", f"{where} must be an array")
    if len(value) > limit:
        raise GateInputError("INPUT_TOO_LARGE", f"{where} has too many entries")
    return value


def _string(value: Any, where: str, *, allow_pending: bool = False) -> str:
    if not isinstance(value, str):
        raise GateInputError("INVALID_TYPE", f"{where} must be a string")
    if value == PENDING and allow_pending:
        return value
    if not value or len(value.encode("utf-8")) > MAX_TEXT_BYTES:
        raise GateInputError("INVALID_TEXT", f"{where} must be nonempty and bounded")
    return value


def _exact_keys(value: dict[str, Any], expected: frozenset[str], where: str) -> None:
    unknown = sorted(set(value) - expected)
    missing = sorted(expected - set(value))
    if unknown:
        raise GateInputError("UNKNOWN_KEY", f"{where} has unknown keys: {unknown}")
    if missing:
        raise GateInputError("MISSING_KEY", f"{where} is missing keys: {missing}")


def _sha(value: Any, where: str, *, allow_pending: bool = False) -> str:
    text = _string(value, where, allow_pending=allow_pending)
    if text == PENDING and allow_pending:
        return text
    if SHA_RE.fullmatch(text) is None:
        raise GateInputError("INVALID_SHA", f"{where} must be a full lowercase SHA")
    return text


def _url(value: Any, where: str, *, allow_pending: bool = False) -> str:
    text = _string(value, where, allow_pending=allow_pending)
    if text == PENDING and allow_pending:
        return text
    try:
        parsed = urlsplit(text)
        hostname = parsed.hostname
        port = parsed.port
    except (UnicodeError, ValueError) as error:
        raise GateInputError("INVALID_URL", f"{where} is not a valid URL") from error
    if (
        parsed.scheme != "https"
        or not parsed.netloc
        or hostname is None
        or port is not None and not 1 <= port <= 65535
        or parsed.username is not None
        or parsed.password is not None
        or any(char.isspace() or unicodedata.category(char) == "Cc" for char in text)
    ):
        raise GateInputError("INVALID_URL", f"{where} must be an HTTPS URL")
    return text


def _path_bytes(path: Any, where: str) -> bytes:
    text = _string(path, where)
    encoded = text.encode("utf-8")
    pure = PurePosixPath(text)
    raw_parts = text.split("/")
    if (
        len(encoded) > MAX_PATH_BYTES
        or "\x00" in text
        or "\n" in text
        or "\r" in text
        or "\\" in text
        or text.startswith("/")
        or text.startswith("./")
        or text.endswith("/")
        or "//" in text
        or any(part in {"", ".", ".."} for part in raw_parts)
        or str(pure) != text
    ):
        raise GateInputError("INVALID_PATH", f"{where} is not a repository-relative path")
    return encoded


def sorted_path_digest(paths: list[str]) -> str:
    """Return the canonical byte-sorted, length-framed changed-path digest."""
    if not paths:
        raise GateInputError("EMPTY_CHANGED_PATHS", "changed_paths must be nonempty")
    if len(paths) > MAX_CHANGED_PATHS:
        raise GateInputError("INPUT_TOO_LARGE", "changed_paths has too many entries")
    encoded_paths = [
        _path_bytes(path, f"changed_paths[{index}]")
        for index, path in enumerate(paths)
    ]
    if len(set(encoded_paths)) != len(encoded_paths):
        raise GateInputError("DUPLICATE_PATH", "changed_paths must not contain duplicates")
    digest = hashlib.sha256()
    for encoded in sorted(encoded_paths):
        digest.update(str(len(encoded)).encode("ascii"))
        digest.update(b":")
        digest.update(encoded)
    return f"sha256:{digest.hexdigest()}"


def _fence(line: str) -> tuple[str, int, str] | None:
    match = FENCE_OPEN_RE.fullmatch(line.removesuffix("\r"))
    if match is None:
        return None
    marker = match.group(2)
    info = match.group(3).strip()
    if marker[0] == "`" and "`" in info:
        return None
    return marker[0], len(marker), info


def _fence_closes(line: str, marker: str, minimum: int) -> bool:
    stripped = line.removesuffix("\r")
    match = re.fullmatch(r" {0,3}(" + re.escape(marker) + r"{3,})[ \t]*", stripped)
    return match is not None and len(match.group(1)) >= minimum


def extract_managed_document(body: str) -> tuple[str, str]:
    """Return one managed JSON block and all Markdown outside that block."""
    lines = body.split("\n")
    active: tuple[str, int, int, bool] | None = None
    blocks: list[tuple[int, int, str]] = []
    for index, line in enumerate(lines):
        if active is not None:
            marker, minimum, opening, managed = active
            if _fence_closes(line, marker, minimum):
                if managed:
                    blocks.append((opening, index, "\n".join(lines[opening + 1 : index])))
                active = None
                continue
            nested = _fence(line)
            if nested is not None and nested[2].startswith(BLOCK_INFO):
                raise GateInputError(
                    "NESTED_MANAGED_BLOCK",
                    "managed evidence block is nested inside another fence",
                )
            continue
        opening_fence = _fence(line)
        if opening_fence is None:
            continue
        marker, minimum, info = opening_fence
        if info == BLOCK_INFO:
            active = (marker, minimum, index, True)
        elif info.startswith(BLOCK_INFO):
            raise GateInputError(
                "AMBIGUOUS_MANAGED_BLOCK",
                "managed fence info must be exactly completion-claims-v1",
            )
        else:
            active = (marker, minimum, index, False)
    if active is not None and active[3]:
        raise GateInputError("MALFORMED_MANAGED_BLOCK", "managed evidence block is unclosed")
    if not blocks:
        raise GateInputError("MISSING_MANAGED_BLOCK", "managed evidence block is missing")
    if len(blocks) != 1:
        raise GateInputError("DUPLICATE_MANAGED_BLOCK", "exactly one managed block is required")
    opening, closing, content = blocks[0]
    unmanaged = "\n".join(lines[:opening] + lines[closing + 1 :])
    return content, unmanaged


def extract_managed_block(body: str) -> str:
    """Compatibility helper returning the JSON text from the managed document."""
    return extract_managed_document(body)[0]


def _markdown_projection(body: str) -> str:
    normalized = unicodedata.normalize("NFKC", html.unescape(body))
    normalized = "".join(
        char for char in normalized if unicodedata.category(char) != "Cf"
    )
    normalized = re.sub(
        r"\[(" + CLOSE_KEYWORD_PATTERN + r")\]\([^)\n]{0,512}\)",
        r"\1",
        normalized,
        flags=re.IGNORECASE,
    )
    normalized = re.sub(
        r"</?[A-Za-z][A-Za-z0-9-]*(?:\s[^>\n]{0,512})?>",
        " ",
        normalized,
    )
    return re.sub(r"\\([#*_[\](){}~`<>:;,.!?-])", r"\1", normalized)


def _issue_number(reference: str) -> int:
    normalized = unicodedata.normalize("NFKC", reference)
    match = re.search(r"(?:#|/(?:issues|pull)/)([1-9][0-9]*)\Z", normalized)
    if match is None:
        raise GateInputError("INVALID_ISSUE_REF", f"invalid issue reference: {reference}")
    return int(match.group(1))


def _diagnostic(code: str, message: str) -> dict[str, str]:
    return {"code": code, "message": message}


def _human_review(kind: str, identifier: str) -> dict[str, str]:
    return {"kind": kind, "id": identifier, "status": HUMAN_REVIEW_REQUIRED}


def _schema_version(value: Any, where: str) -> None:
    if type(value) is not int:
        raise GateInputError("INVALID_TYPE", f"{where} must be an integer")
    if value != SCHEMA_VERSION:
        raise GateInputError("UNSUPPORTED_SCHEMA", f"unsupported {where}")


def _history_tuple(value: Any, where: str) -> tuple[str, str, str]:
    record = _object(value, where)
    _exact_keys(record, HISTORY_KEYS, where)
    commit_sha = _sha(record["commit_sha"], f"{where}.commit_sha")
    path = _string(record["path"], f"{where}.path")
    _path_bytes(path, f"{where}.path")
    action = _string(record["action"], f"{where}.action")
    if action not in HISTORY_ACTIONS:
        raise GateInputError("UNKNOWN_HISTORY_ACTION", f"{where}.action is unsupported")
    return commit_sha, path, action


def _history_tuples(raw: Any, where: str) -> list[tuple[str, str, str]]:
    values = _array(raw, where, MAX_HISTORY_FACTS)
    tuples = [_history_tuple(value, f"{where}[{index}]") for index, value in enumerate(values)]
    if len(set(tuples)) != len(tuples):
        raise GateInputError("DUPLICATE_HISTORY_TUPLE", f"{where} contains duplicates")
    return tuples


def _validate_context(raw: Any) -> dict[str, Any]:
    context = dict(_object(raw, "context"))
    _exact_keys(context, CONTEXT_KEYS, "context")
    _schema_version(context["schema_version"], "context.schema_version")
    if type(context["is_draft"]) is not bool:
        raise GateInputError("INVALID_TYPE", "context.is_draft must be a boolean")
    if context["delivery"] != "pull_request":
        raise GateInputError("INVALID_DELIVERY", "context.delivery must be pull_request")
    context["base_sha"] = _sha(context["base_sha"], "context.base_sha")
    context["head_sha"] = _sha(context["head_sha"], "context.head_sha")
    paths = _array(context["changed_paths"], "context.changed_paths", MAX_CHANGED_PATHS)
    context["changed_paths"] = [
        _string(path, f"context.changed_paths[{index}]") for index, path in enumerate(paths)
    ]
    context["computed_digest"] = sorted_path_digest(context["changed_paths"])
    allowed = _array(context["allowed_issue_refs"], "context.allowed_issue_refs", 1_000)
    if any(type(number) is not int or number <= 0 for number in allowed):
        raise GateInputError(
            "INVALID_ISSUE_REF", "context.allowed_issue_refs must contain positive integers"
        )
    if len(set(allowed)) != len(allowed):
        raise GateInputError("DUPLICATE_ISSUE_REF", "allowed_issue_refs contains duplicates")
    if not allowed:
        raise GateInputError("INVALID_ISSUE_REF", "allowed_issue_refs must be nonempty")
    context["history_facts"] = _history_tuples(
        context["history_facts"], "context.history_facts"
    )
    return context


def _check_candidate(
    candidate_raw: Any,
    context: dict[str, Any],
    errors: list[dict[str, str]],
    incomplete: list[dict[str, str]],
) -> None:
    candidate = _object(candidate_raw, "candidate")
    _exact_keys(candidate, CANDIDATE_KEYS, "candidate")
    draft = context["is_draft"]
    base = _sha(candidate["base_sha"], "candidate.base_sha", allow_pending=True)
    head = _sha(candidate["head_sha"], "candidate.head_sha", allow_pending=True)
    count = candidate["changed_file_count"]
    digest = _string(
        candidate["sorted_path_digest"],
        "candidate.sorted_path_digest",
        allow_pending=True,
    )
    values = {
        "base_sha": (base, context["base_sha"], "BASE_SHA_MISMATCH"),
        "head_sha": (head, context["head_sha"], "HEAD_SHA_MISMATCH"),
        "sorted_path_digest": (
            digest,
            context["computed_digest"],
            "PATH_DIGEST_MISMATCH",
        ),
    }
    if digest != PENDING and DIGEST_RE.fullmatch(digest) is None:
        raise GateInputError(
            "INVALID_DIGEST", "candidate.sorted_path_digest must be sha256 lowercase hex"
        )
    if count != PENDING:
        if type(count) is not int or count < 0:
            raise GateInputError(
                "INVALID_TYPE", "candidate.changed_file_count must be a nonnegative integer"
            )
        if count != len(context["changed_paths"]):
            errors.append(
                _diagnostic("FILE_COUNT_MISMATCH", "candidate changed-file count differs")
            )
    elif not draft:
        errors.append(_diagnostic("READY_PLACEHOLDER", "ready candidate contains PENDING"))
    else:
        incomplete.append(_diagnostic("PENDING_FILE_COUNT", "changed-file count is pending"))
    for field, (actual, expected, code) in values.items():
        if actual == PENDING:
            if draft:
                incomplete.append(_diagnostic(f"PENDING_{field.upper()}", f"{field} is pending"))
            else:
                errors.append(_diagnostic("READY_PLACEHOLDER", f"ready {field} is pending"))
        elif actual != expected:
            errors.append(_diagnostic(code, f"candidate {field} differs from context"))


def _check_claim_levels(
    raw: Any, human_reviews: list[dict[str, str]]
) -> None:
    levels = _array(raw, "claim_levels", len(CLAIM_LEVELS))
    if not levels:
        raise GateInputError("EMPTY_CLAIM_LEVELS", "claim_levels must be nonempty")
    if any(not isinstance(level, str) or level not in CLAIM_LEVELS for level in levels):
        raise GateInputError("UNKNOWN_CLAIM_LEVEL", "claim_levels contains an unknown value")
    if len(set(levels)) != len(levels):
        raise GateInputError("DUPLICATE_CLAIM_LEVEL", "claim_levels contains duplicates")
    for level in levels:
        if level != "exact_candidate_diff":
            human_reviews.append(_human_review("claim_level", level))


def _check_review_records(
    raw: Any,
    context: dict[str, Any],
    errors: list[dict[str, str]],
    incomplete: list[dict[str, str]],
    human_reviews: list[dict[str, str]],
) -> None:
    records = _array(raw, "review_records", MAX_REVIEW_RECORDS)
    draft = context["is_draft"]
    seen: set[str] = set()
    for index, raw_record in enumerate(records):
        record = _object(raw_record, f"review_records[{index}]")
        _exact_keys(record, REVIEW_KEYS, f"review_records[{index}]")
        kind = _string(record["kind"], f"review_records[{index}].kind")
        if kind not in REVIEW_KINDS:
            raise GateInputError("UNKNOWN_REVIEW_KIND", f"unknown review kind: {kind}")
        if kind in seen:
            raise GateInputError("DUPLICATE_REVIEW_KIND", f"duplicate review kind: {kind}")
        seen.add(kind)
        human_reviews.append(_human_review("review_record", kind))
        head = _sha(
            record["head_sha"],
            f"review_records[{index}].head_sha",
            allow_pending=True,
        )
        url = _url(record["url"], f"review_records[{index}].url", allow_pending=True)
        if head == PENDING or url == PENDING:
            if draft:
                incomplete.append(_diagnostic("PENDING_REVIEW", f"{kind} is pending"))
            else:
                errors.append(_diagnostic("READY_PLACEHOLDER", f"ready {kind} is pending"))
        elif head != context["head_sha"]:
            errors.append(_diagnostic("REVIEW_HEAD_MISMATCH", f"{kind} records a stale head"))
    missing = sorted(REVIEW_KINDS - seen)
    if missing:
        if draft:
            incomplete.append(
                _diagnostic("MISSING_REVIEW_RECORDS", f"review records missing: {missing}")
            )
        else:
            errors.append(
                _diagnostic("MISSING_REVIEW_RECORDS", f"review records missing: {missing}")
            )


def _check_history_claims(
    raw: Any,
    context: dict[str, Any],
    errors: list[dict[str, str]],
) -> None:
    claims = _history_tuples(raw, "history_claims")
    facts = context["history_facts"]
    if len(claims) != len(facts):
        errors.append(
            _diagnostic(
                "HISTORY_COUNT_MISMATCH",
                "history_claims count differs from trusted history_facts",
            )
        )
        return
    for index, (claim, fact) in enumerate(zip(claims, facts)):
        if claim[0] != fact[0]:
            errors.append(
                _diagnostic(
                    "HISTORY_COMMIT_MISMATCH",
                    f"history_claims[{index}] commit_sha differs",
                )
            )
        if claim[1] != fact[1]:
            errors.append(
                _diagnostic(
                    "HISTORY_PATH_MISMATCH",
                    f"history_claims[{index}] path differs",
                )
            )
        if claim[2] != fact[2]:
            errors.append(
                _diagnostic(
                    "HISTORY_ACTION_MISMATCH",
                    f"history_claims[{index}] action differs",
                )
            )


def _check_references(raw: Any, context: dict[str, Any], body: str) -> None:
    references = _object(raw, "references")
    _exact_keys(references, REFERENCE_KEYS, "references")
    non_closing = _array(references["non_closing"], "references.non_closing", 1_000)
    closing = _array(references["closing"], "references.closing", 1_000)
    if closing:
        raise GateInputError("CLOSING_REFERENCES_NOT_EMPTY", "references.closing must be empty")
    projected = _markdown_projection(body)
    if CLOSING_RE.search(projected) is not None:
        raise GateInputError("AUTOCLOSE_REFERENCE", "body contains an auto-closing issue reference")
    if not non_closing:
        raise GateInputError("MISSING_NON_CLOSING_REF", "at least one non-closing ref is required")
    if len(set(map(str, non_closing))) != len(non_closing):
        raise GateInputError("DUPLICATE_ISSUE_REF", "non-closing references contain duplicates")
    allowed = set(context["allowed_issue_refs"])
    for index, raw_reference in enumerate(non_closing):
        reference = _string(raw_reference, f"references.non_closing[{index}]")
        match = NON_CLOSING_RE.fullmatch(reference)
        if match is None or int(match.group(2)) not in allowed:
            raise GateInputError("INVALID_ISSUE_REF", f"disallowed non-closing ref: {reference}")
    for match in NON_CLOSING_BODY_RE.finditer(projected):
        reference = match.group("reference")
        if _issue_number(reference) not in allowed:
            raise GateInputError(
                "UNMANAGED_ISSUE_REF",
                f"body has a disallowed non-closing reference: {reference}",
            )


def _charge_unmanaged_prose(
    unmanaged: str, human_reviews: list[dict[str, str]]
) -> None:
    if not unmanaged.strip():
        return
    human_reviews.append(_human_review("unmanaged_prose", "body-outside-managed-block"))
    projected = _markdown_projection(unmanaged)
    if ISSUE_MENTION_RE.search(projected) is not None:
        human_reviews.append(
            _human_review("unmanaged_issue_reference", "body-issue-reference")
        )
    if FUTURE_PLAN_RE.search(projected) is not None:
        human_reviews.append(_human_review("future_plan", "body-future-plan"))


def _check_semantic_claims(
    raw: Any,
    context: dict[str, Any],
    errors: list[dict[str, str]],
    incomplete: list[dict[str, str]],
    human_reviews: list[dict[str, str]],
) -> None:
    claims = _array(raw, "semantic_claims", MAX_SEMANTIC_CLAIMS)
    draft = context["is_draft"]
    seen: set[str] = set()
    for index, raw_claim in enumerate(claims):
        claim = _object(raw_claim, f"semantic_claims[{index}]")
        _exact_keys(claim, SEMANTIC_KEYS, f"semantic_claims[{index}]")
        identifier = _string(claim["id"], f"semantic_claims[{index}].id")
        if identifier in seen:
            raise GateInputError("DUPLICATE_SEMANTIC_ID", f"duplicate semantic id: {identifier}")
        seen.add(identifier)
        kind = _string(claim["kind"], f"semantic_claims[{index}].kind")
        if kind not in SEMANTIC_KINDS:
            raise GateInputError("UNKNOWN_SEMANTIC_KIND", f"unknown semantic kind: {kind}")
        _string(claim["statement"], f"semantic_claims[{index}].statement")
        urls = _array(
            claim["evidence_urls"],
            f"semantic_claims[{index}].evidence_urls",
            1_000,
        )
        if not urls:
            raise GateInputError("MISSING_EVIDENCE_URL", f"{identifier} has no evidence URL")
        for url_index, value in enumerate(urls):
            url = _url(
                value,
                f"semantic_claims[{index}].evidence_urls[{url_index}]",
                allow_pending=True,
            )
            if url == PENDING:
                if draft:
                    incomplete.append(
                        _diagnostic("PENDING_SEMANTIC_EVIDENCE", f"{identifier} is pending")
                    )
                else:
                    errors.append(
                        _diagnostic("READY_PLACEHOLDER", f"ready {identifier} is pending")
                    )
        human_reviews.append(_human_review(kind, identifier))


def evaluate(context_raw: Any, body: str) -> tuple[int, dict[str, Any]]:
    """Evaluate parsed context and Markdown; return ``(exit_code, report)``."""
    try:
        context = _validate_context(context_raw)
        managed, unmanaged = extract_managed_document(body)
        payload = _object(_parse_json(managed, "managed block"), "payload")
        _exact_keys(payload, PAYLOAD_KEYS, "payload")
        _schema_version(payload["schema_version"], "payload.schema_version")

        errors: list[dict[str, str]] = []
        incomplete: list[dict[str, str]] = []
        human_reviews: list[dict[str, str]] = []
        _check_candidate(payload["candidate"], context, errors, incomplete)
        _check_claim_levels(payload["claim_levels"], human_reviews)
        _check_review_records(
            payload["review_records"],
            context,
            errors,
            incomplete,
            human_reviews,
        )
        _check_history_claims(payload["history_claims"], context, errors)
        _check_references(payload["references"], context, body)
        _check_semantic_claims(
            payload["semantic_claims"],
            context,
            errors,
            incomplete,
            human_reviews,
        )
        _charge_unmanaged_prose(unmanaged, human_reviews)
        if errors:
            status = FAIL
            code = EXIT_FAIL
            diagnostics = errors
        elif incomplete:
            status = DRAFT_INCOMPLETE
            code = EXIT_DRAFT_INCOMPLETE
            diagnostics = incomplete
        else:
            status = PASS
            code = EXIT_PASS
            diagnostics = []
        report = {
            "schema_version": SCHEMA_VERSION,
            "machine_status": status,
            "diagnostics": diagnostics,
            "human_reviews": human_reviews,
        }
        return code, report
    except GateInputError as error:
        return (
            EXIT_FAIL,
            {
                "schema_version": SCHEMA_VERSION,
                "machine_status": FAIL,
                "diagnostics": [_diagnostic(error.code, error.message)],
                "human_reviews": [],
            },
        )


def run(context_path: Path, body_path: Path) -> tuple[int, dict[str, Any]]:
    """Read bounded UTF-8 inputs and evaluate them."""
    try:
        context_text = _read_utf8(context_path, MAX_CONTEXT_BYTES, "context")
        body = _read_utf8(body_path, MAX_BODY_BYTES, "body")
        context = _parse_json(context_text, "context")
    except GateInputError as error:
        return (
            EXIT_FAIL,
            {
                "schema_version": SCHEMA_VERSION,
                "machine_status": FAIL,
                "diagnostics": [_diagnostic(error.code, error.message)],
                "human_reviews": [],
            },
        )
    return evaluate(context, body)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--context", required=True, type=Path)
    parser.add_argument("--body", required=True, type=Path)
    args = parser.parse_args(argv)
    code, report = run(args.context, args.body)
    print(json.dumps(report, indent=2, sort_keys=True))
    return code


if __name__ == "__main__":
    sys.exit(main())

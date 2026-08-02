#!/usr/bin/env python3
"""Trusted GitHub adapter for the offline completion-claim gate.

The adapter treats every pull-request field as data. It reads only fixed
GitHub REST endpoints, never fetches candidate content, and publishes one
stable exact-head commit-status context.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import time
from typing import Any, Callable, Protocol
from urllib import error, parse, request

import completion_claim_gate as offline

API_BASE = "https://api.github.com"
STATUS_CONTEXT = "completion-claim/live"
PR_EVENT_TYPES = (
    "opened",
    "reopened",
    "synchronize",
    "edited",
    "ready_for_review",
    "converted_to_draft",
)
MAX_BODY_BYTES = 1024 * 1024
MAX_CONTEXT_BYTES = 1024 * 1024
MAX_EVENT_BYTES = 1024 * 1024
MAX_API_RESPONSE_BYTES = 2 * 1024 * 1024
MAX_DIAGNOSTIC_BYTES = 8192
MAX_CHANGED_FILES = 3000
FILES_PER_PAGE = 100
MAX_FILE_PAGES = 30
MAX_STRUCTURED_REFERENCES = 16
MAX_ISSUES = 64
MAX_ISSUE_DEPTH = 8
MAX_HISTORY_FACTS = 128
MAX_HISTORY_FILE_PAGES = 3
MAX_BACKFILL_PRS = 100
MAX_BACKFILL_PAGES = 2
REQUEST_TIMEOUT_SECONDS = 10
REQUEST_RETRIES = 2
MAX_STATUS_DESCRIPTION = 140
WORKFLOW_SHA256 = "f5a9633578e3c3506d89cb6f6eff17dcb15a3cf31674fb8247d9241bd57ce6b2"

SHA_RE = re.compile(r"[0-9a-f]{40}\Z")
REPOSITORY_RE = re.compile(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+\Z")
PR_NUMBER_RE = re.compile(r"[1-9][0-9]*\Z")
STRUCTURED_REF_RE = re.compile(r"(Refs|Part of) #([1-9][0-9]*)\Z")
# Only these kinds seed the hierarchy walk; `Part of` must prove itself an
# ancestor of a seed instead of granting itself authority.
SEED_KINDS = frozenset({"Refs", "Closes"})


class LiveGateError(Exception):
    """Stable fail-shut adapter error."""

    def __init__(self, code: str) -> None:
        super().__init__(code)
        self.code = code


class Transport(Protocol):
    """Minimal injectable REST transport."""

    def get(self, path: str, *, allow_not_found: bool = False) -> object:
        """Read one fixed repository REST path."""

    def post(self, path: str, payload: dict[str, object]) -> object:
        """Write one fixed repository REST path."""


Checker = Callable[[object, str], tuple[int, dict[str, Any]]]


@dataclass(frozen=True)
class Snapshot:
    """Exact pull-request fields compared across P1 and P2."""

    number: int
    state: str
    draft: bool
    base_sha: str
    head_sha: str
    body: str
    body_digest: str
    changed_file_count: int
    changed_paths: tuple[str, ...]
    path_digest: str
    repository: str
    head_repository: str
    head_actor: str

    def comparison_key(self) -> tuple[object, ...]:
        """Return the exact P1/P2 race-comparison tuple."""
        return (
            self.state,
            self.draft,
            self.base_sha,
            self.head_sha,
            self.body_digest,
            self.changed_file_count,
            self.path_digest,
        )


@dataclass(frozen=True)
class BasicSnapshot:
    """Validated fresh PR metadata available before fact endpoint reads."""

    number: int
    state: str
    draft: bool
    base_sha: str
    head_sha: str
    body: str
    body_digest: str
    changed_file_count: int
    repository: str
    head_repository: str
    head_actor: str


@dataclass(frozen=True)
class IssueFacts:
    """Validated same-repository facts about one referenced issue."""

    number: int
    is_open: bool
    is_pull_request: bool


@dataclass(frozen=True)
class PendingIdentity:
    """Minimal trusted identity required before writing exact-head pending."""

    pr: dict[str, object]
    number: int
    state: str
    base_sha: str
    head_sha: str
    repository: str


def _object(value: object, code: str) -> dict[str, object]:
    if not isinstance(value, dict):
        raise LiveGateError(code)
    return value


def _array(value: object, code: str) -> list[object]:
    if not isinstance(value, list):
        raise LiveGateError(code)
    return value


def _string(value: object, code: str) -> str:
    if not isinstance(value, str):
        raise LiveGateError(code)
    return value


def _integer(value: object, code: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise LiveGateError(code)
    return value


def _sha(value: object, code: str) -> str:
    text = _string(value, code)
    if SHA_RE.fullmatch(text) is None:
        raise LiveGateError(code)
    return text


def _repository(value: object) -> str:
    text = _string(value, "INVALID_REPOSITORY")
    if REPOSITORY_RE.fullmatch(text) is None:
        raise LiveGateError("INVALID_REPOSITORY")
    return text


def _duplicate_rejecting_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise LiveGateError("DUPLICATE_MANAGED_KEY")
        result[key] = value
    return result


def structured_payload(body: str) -> dict[str, object]:
    """Parse only the canonical managed JSON, never unrestricted prose."""
    try:
        managed = offline.extract_managed_block(body)
        value = json.loads(managed, object_pairs_hook=_duplicate_rejecting_object)
    except LiveGateError:
        raise
    except (json.JSONDecodeError, offline.GateInputError) as exc:
        raise LiveGateError("INVALID_MANAGED_PAYLOAD") from exc
    return _object(value, "INVALID_MANAGED_PAYLOAD")


def optional_structured_payload(body: str) -> dict[str, object] | None:
    """Parse the managed JSON only when the body opts into the managed contract."""
    if offline.managed_marker_count(body) == 0:
        return None
    return structured_payload(body)


def structured_references(payload: dict[str, object]) -> list[tuple[str, int]]:
    """Return exact non-closing references from the managed payload."""
    references = _object(payload.get("references"), "INVALID_STRUCTURED_REFERENCES")
    raw = _array(references.get("non_closing"), "INVALID_STRUCTURED_REFERENCES")
    if len(raw) > MAX_STRUCTURED_REFERENCES:
        raise LiveGateError("STRUCTURED_REFERENCE_LIMIT_EXCEEDED")
    result: list[tuple[str, int]] = []
    texts: set[str] = set()
    numbers: set[int] = set()
    for value in raw:
        text = _string(value, "INVALID_STRUCTURED_REFERENCES")
        match = STRUCTURED_REF_RE.fullmatch(text)
        if match is None:
            raise LiveGateError("INVALID_STRUCTURED_REFERENCES")
        number = int(match.group(2))
        if text in texts:
            raise LiveGateError("DUPLICATE_STRUCTURED_REFERENCE")
        if number in numbers:
            raise LiveGateError("DUPLICATE_STRUCTURED_ISSUE")
        texts.add(text)
        numbers.add(number)
        result.append((match.group(1), number))
    if not result or not any(kind == "Refs" for kind, _ in result):
        raise LiveGateError("MISSING_STRUCTURED_REFERENCE")
    return result


def prose_references(body: str) -> list[tuple[str, int]]:
    """Return anchored prose references, keeping the offline diagnostic code."""
    try:
        anchored, _ = offline.parse_body_references(body)
    except offline.GateInputError as exc:
        raise LiveGateError(exc.code) from exc
    return list(anchored)


def body_references(
    body: str,
) -> tuple[dict[str, object] | None, list[tuple[str, int]]]:
    """Return the managed payload, if any, plus the references to verify live."""
    payload = optional_structured_payload(body)
    if payload is None:
        return None, prose_references(body)
    return payload, structured_references(payload)


def structured_history(payload: dict[str, object]) -> list[dict[str, object]]:
    """Return bounded history claims for primary-evidence derivation."""
    raw = _array(payload.get("history_claims"), "INVALID_HISTORY_CLAIMS")
    if len(raw) > MAX_HISTORY_FACTS:
        raise LiveGateError("HISTORY_LIMIT_EXCEEDED")
    result: list[dict[str, object]] = []
    for value in raw:
        claim = _object(value, "INVALID_HISTORY_CLAIMS")
        if set(claim) != {"commit_sha", "path", "action"}:
            raise LiveGateError("INVALID_HISTORY_CLAIMS")
        sha = _sha(claim["commit_sha"], "INVALID_HISTORY_COMMIT")
        path = _string(claim["path"], "INVALID_HISTORY_PATH")
        action = _string(claim["action"], "INVALID_HISTORY_ACTION")
        if action not in {"added", "modified", "deleted"}:
            raise LiveGateError("INVALID_HISTORY_ACTION")
        try:
            offline.sorted_path_digest([path])
        except offline.GateInputError as exc:
            raise LiveGateError("INVALID_HISTORY_PATH") from exc
        result.append({"commit_sha": sha, "path": path, "action": action})
    return result


def collect_changed_paths(
    transport: Transport,
    repository: str,
    pr_number: int,
    expected_count: int,
) -> list[str]:
    """Collect the complete fixed-page changed-file set plus an empty sentinel."""
    _repository(repository)
    if expected_count < 0:
        raise LiveGateError("INVALID_CHANGED_COUNT")
    if expected_count > MAX_CHANGED_FILES:
        raise LiveGateError("FILE_LIMIT_EXCEEDED")
    page_count = (expected_count + FILES_PER_PAGE - 1) // FILES_PER_PAGE
    if page_count > MAX_FILE_PAGES:
        raise LiveGateError("FILE_LIMIT_EXCEEDED")
    paths: list[str] = []
    for page in range(1, page_count + 1):
        endpoint = (
            f"/repos/{repository}/pulls/{pr_number}/files"
            f"?per_page={FILES_PER_PAGE}&page={page}"
        )
        raw_page = _array(transport.get(endpoint), "INVALID_FILES_RESPONSE")
        expected_page_size = min(
            FILES_PER_PAGE,
            expected_count - len(paths),
        )
        if len(raw_page) != expected_page_size:
            raise LiveGateError("FILE_COUNT_MISMATCH")
        for raw_file in raw_page:
            file_data = _object(raw_file, "INVALID_FILE_ENTRY")
            paths.append(_string(file_data.get("filename"), "INVALID_FILE_ENTRY"))
    sentinel_endpoint = (
        f"/repos/{repository}/pulls/{pr_number}/files"
        f"?per_page={FILES_PER_PAGE}&page={page_count + 1}"
    )
    sentinel = _array(
        transport.get(sentinel_endpoint),
        "INVALID_FILES_RESPONSE",
    )
    if sentinel:
        raise LiveGateError("EXTRA_CHANGED_PATHS")
    if len(paths) != expected_count:
        raise LiveGateError("FILE_COUNT_MISMATCH")
    if len(set(paths)) != len(paths):
        raise LiveGateError("DUPLICATE_CHANGED_PATH")
    try:
        offline.sorted_path_digest(paths)
    except offline.GateInputError as exc:
        raise LiveGateError("INVALID_CHANGED_PATH") from exc
    return paths


def _validated_issue(
    value: object,
    repository: str,
    expected_number: int | None,
    code: str,
    *,
    allow_pull_request: bool = False,
) -> IssueFacts:
    """Validate one same-repository issue; open state is judged in aggregate."""
    issue = _object(value, code)
    is_pull_request = "pull_request" in issue
    if is_pull_request and not allow_pull_request:
        raise LiveGateError("ISSUE_IS_PULL_REQUEST")
    number = _integer(issue.get("number"), code)
    if number < 1:
        raise LiveGateError(code)
    if expected_number is not None and number != expected_number:
        raise LiveGateError("ISSUE_NUMBER_MISMATCH")
    state = issue.get("state")
    if state not in {"open", "closed"}:
        raise LiveGateError("INVALID_ISSUE_STATE")
    expected_repository_url = f"{API_BASE}/repos/{repository}"
    if issue.get("repository_url") != expected_repository_url:
        raise LiveGateError("ISSUE_REPOSITORY_MISMATCH")
    return IssueFacts(
        number=number,
        is_open=state == "open",
        is_pull_request=is_pull_request,
    )


def _read_issue(
    transport: Transport,
    repository: str,
    number: int,
    cache: dict[int, IssueFacts],
    *,
    allow_pull_request: bool,
) -> IssueFacts:
    """Read one memoized issue, mapping absence to a stable diagnostic."""
    if number not in cache:
        raw_issue = transport.get(
            f"/repos/{repository}/issues/{number}",
            allow_not_found=True,
        )
        if raw_issue is None:
            raise LiveGateError("ISSUE_NOT_FOUND")
        cache[number] = _validated_issue(
            raw_issue,
            repository,
            number,
            "INVALID_ISSUE_RESPONSE",
            allow_pull_request=allow_pull_request,
        )
    return cache[number]


def _derive_allowed_issue_refs(
    transport: Transport,
    repository: str,
    references: list[tuple[str, int]],
) -> list[int]:
    """Derive declared issue authority through structural parent chains."""
    declared = {number for _, number in references}
    seeds = [(kind, number) for kind, number in references if kind in SEED_KINDS]
    allowed: set[int] = set()
    issue_cache: dict[int, IssueFacts] = {}
    parent_cache: dict[int, int | None] = {}
    open_seed = False
    for kind, seed in seeds:
        current: int | None = seed
        chain_seen: set[int] = set()
        depth = 0
        while current is not None:
            if current in chain_seen:
                raise LiveGateError("ISSUE_HIERARCHY_CYCLE")
            if depth >= MAX_ISSUE_DEPTH:
                raise LiveGateError("ISSUE_DEPTH_EXCEEDED")
            if len(allowed) >= MAX_ISSUES and current not in allowed:
                raise LiveGateError("ISSUE_LIMIT_EXCEEDED")
            chain_seen.add(current)
            allowed.add(current)
            facts = _read_issue(
                transport,
                repository,
                current,
                issue_cache,
                allow_pull_request=kind == "Refs" and current == seed,
            )
            if current == seed and facts.is_open and not facts.is_pull_request:
                open_seed = True
            if facts.is_pull_request:
                break
            if current not in parent_cache:
                parent_endpoint = (
                    f"/repos/{repository}/issues/{current}/parent"
                )
                raw_parent = transport.get(
                    parent_endpoint,
                    allow_not_found=True,
                )
                if raw_parent is None:
                    parent_cache[current] = None
                else:
                    parent_facts = _validated_issue(
                        raw_parent,
                        repository,
                        None,
                        "INVALID_ISSUE_PARENT",
                    )
                    parent_cache[current] = parent_facts.number
                    issue_cache.setdefault(parent_facts.number, parent_facts)
            current = parent_cache[current]
            depth += 1
    if not declared.issubset(allowed):
        raise LiveGateError("ISSUE_OUTSIDE_HIERARCHY")
    if not open_seed:
        raise LiveGateError("MISSING_OPEN_ISSUE_REFERENCE")
    return sorted(allowed)


def derive_allowed_issue_refs(
    transport: Transport,
    repository: str,
    body: str,
) -> list[int]:
    """Parse references first, then derive their bounded structural graph."""
    return _derive_allowed_issue_refs(transport, repository, body_references(body)[1])


def _content_blob_sha(
    transport: Transport,
    repository: str,
    sha: str,
    path: str,
) -> str | None:
    encoded = parse.quote(path, safe="/")
    endpoint = f"/repos/{repository}/contents/{encoded}?ref={sha}"
    raw = transport.get(endpoint, allow_not_found=True)
    if raw is None:
        return None
    content = _object(raw, "INVALID_CONTENT_RESPONSE")
    if content.get("type") != "file":
        raise LiveGateError("INVALID_CONTENT_RESPONSE")
    return _sha(content.get("sha"), "INVALID_CONTENT_BLOB")


def _commit_parent_shas(commit: dict[str, object]) -> tuple[str, ...]:
    parents = _array(commit.get("parents"), "INVALID_COMMIT_RESPONSE")
    if len(parents) > 1:
        raise LiveGateError("HISTORY_MERGE_UNSUPPORTED")
    return tuple(
        _sha(
            _object(parent, "INVALID_COMMIT_PARENT").get("sha"),
            "INVALID_COMMIT_PARENT",
        )
        for parent in parents
    )


def _collect_commit_files(
    transport: Transport,
    repository: str,
    commit_sha: str,
) -> tuple[tuple[str, ...], dict[str, tuple[str, str]]]:
    """Read bounded commit-file pages through an explicit empty sentinel."""
    parent_shas: tuple[str, ...] | None = None
    files: dict[str, tuple[str, str]] = {}
    for page in range(1, MAX_HISTORY_FILE_PAGES + 2):
        endpoint = (
            f"/repos/{repository}/commits/{commit_sha}"
            f"?per_page={FILES_PER_PAGE}&page={page}"
        )
        commit = _object(
            transport.get(endpoint),
            "INVALID_COMMIT_RESPONSE",
        )
        if _sha(commit.get("sha"), "INVALID_COMMIT_RESPONSE") != commit_sha:
            raise LiveGateError("HISTORY_COMMIT_MISMATCH")
        current_parents = _commit_parent_shas(commit)
        if parent_shas is None:
            parent_shas = current_parents
        elif current_parents != parent_shas:
            raise LiveGateError("HISTORY_COMMIT_PAGE_MISMATCH")
        raw_files = _array(commit.get("files"), "INVALID_COMMIT_FILES")
        if len(raw_files) > FILES_PER_PAGE:
            raise LiveGateError("HISTORY_FILE_PAGE_SIZE")
        if page == MAX_HISTORY_FILE_PAGES + 1:
            if raw_files:
                raise LiveGateError("HISTORY_FILE_LIMIT_EXCEEDED")
            break
        for raw_file in raw_files:
            file_data = _object(raw_file, "INVALID_COMMIT_FILE")
            filename = _string(
                file_data.get("filename"),
                "INVALID_COMMIT_FILE",
            )
            try:
                offline.sorted_path_digest([filename])
            except offline.GateInputError as exc:
                raise LiveGateError("INVALID_COMMIT_FILE") from exc
            status = _string(file_data.get("status"), "INVALID_COMMIT_FILE")
            if status not in {"added", "modified", "removed"}:
                raise LiveGateError("UNSUPPORTED_COMMIT_FILE_STATUS")
            blob_sha = _sha(file_data.get("sha"), "INVALID_COMMIT_FILE_BLOB")
            if filename in files:
                raise LiveGateError("DUPLICATE_COMMIT_FILE")
            files[filename] = (status, blob_sha)
        if not raw_files:
            break
    if parent_shas is None:
        raise LiveGateError("INVALID_COMMIT_RESPONSE")
    return parent_shas, files


def _validate_parent_commit(
    transport: Transport,
    repository: str,
    parent_sha: str,
) -> None:
    endpoint = (
        f"/repos/{repository}/commits/{parent_sha}"
        f"?per_page=1&page=1"
    )
    parent = _object(transport.get(endpoint), "INVALID_COMMIT_PARENT")
    if _sha(parent.get("sha"), "INVALID_COMMIT_PARENT") != parent_sha:
        raise LiveGateError("HISTORY_PARENT_MISMATCH")


def derive_history_facts(
    transport: Transport,
    repository: str,
    head_sha: str,
    claims: list[dict[str, object]],
) -> list[dict[str, object]]:
    """Verify history tuples against commit, ancestry, and content evidence."""
    if len(claims) > MAX_HISTORY_FACTS:
        raise LiveGateError("HISTORY_LIMIT_EXCEEDED")
    facts: list[dict[str, object]] = []
    commit_cache: dict[
        str,
        tuple[tuple[str, ...], dict[str, tuple[str, str]]],
    ] = {}
    for raw_claim in claims:
        claim = _object(raw_claim, "INVALID_HISTORY_CLAIMS")
        commit_sha = _sha(claim.get("commit_sha"), "INVALID_HISTORY_COMMIT")
        path = _string(claim.get("path"), "INVALID_HISTORY_PATH")
        action = _string(claim.get("action"), "INVALID_HISTORY_ACTION")
        if commit_sha not in commit_cache:
            commit_cache[commit_sha] = _collect_commit_files(
                transport,
                repository,
                commit_sha,
            )
        parent_shas, commit_files = commit_cache[commit_sha]
        expected_file_status = {
            "added": "added",
            "modified": "modified",
            "deleted": "removed",
        }
        if action not in expected_file_status:
            raise LiveGateError("INVALID_HISTORY_ACTION")
        file_evidence = commit_files.get(path)
        if file_evidence is None:
            raise LiveGateError("HISTORY_PATH_NOT_IN_COMMIT")
        file_status, file_blob_sha = file_evidence
        if file_status != expected_file_status[action]:
            raise LiveGateError("HISTORY_COMMIT_STATUS_MISMATCH")
        if commit_sha != head_sha:
            compare_endpoint = (
                f"/repos/{repository}/compare/{commit_sha}...{head_sha}"
            )
            comparison = _object(
                transport.get(compare_endpoint),
                "INVALID_COMPARE_RESPONSE",
            )
            if comparison.get("status") not in {"ahead", "identical"}:
                raise LiveGateError("HISTORY_UNREACHABLE")
        commit_blob_sha = _content_blob_sha(
            transport,
            repository,
            commit_sha,
            path,
        )
        if not parent_shas:
            if action != "added":
                raise LiveGateError("HISTORY_ROOT_ACTION")
            parent_blob_sha = None
        else:
            parent_sha = parent_shas[0]
            _validate_parent_commit(transport, repository, parent_sha)
            parent_blob_sha = _content_blob_sha(
                transport,
                repository,
                parent_sha,
                path,
            )
        expected_existence = {
            "added": (False, True),
            "modified": (True, True),
            "deleted": (True, False),
        }[action]
        actual_existence = (
            parent_blob_sha is not None,
            commit_blob_sha is not None,
        )
        if actual_existence != expected_existence:
            raise LiveGateError("HISTORY_ACTION_MISMATCH")
        if action == "modified" and parent_blob_sha == commit_blob_sha:
            raise LiveGateError("HISTORY_BLOB_UNCHANGED")
        observed_blob = (
            parent_blob_sha if action == "deleted" else commit_blob_sha
        )
        if observed_blob != file_blob_sha:
            raise LiveGateError("HISTORY_FILE_BLOB_MISMATCH")
        facts.append(
            {"commit_sha": commit_sha, "path": path, "action": action}
        )
    return facts


def _nested_repository_name(pr: dict[str, object], side: str) -> str:
    side_data = _object(pr.get(side), "INVALID_PR_RESPONSE")
    repo_data = _object(side_data.get("repo"), "INVALID_PR_RESPONSE")
    return _repository(repo_data.get("full_name"))


def _base_repository_name(pr: dict[str, object]) -> str:
    base = _object(pr.get("base"), "INVALID_PR_RESPONSE")
    repo = base.get("repo")
    if repo is not None:
        return _repository(_object(repo, "INVALID_PR_RESPONSE").get("full_name"))
    fallback = _object(pr.get("base_repo"), "INVALID_PR_RESPONSE")
    return _repository(fallback.get("full_name"))


def read_pr_metadata(
    transport: Transport,
    repository: str,
    pr_number: int,
) -> tuple[dict[str, object], str]:
    """Read and minimally validate one fresh PR response."""
    endpoint = f"/repos/{repository}/pulls/{pr_number}"
    raw = transport.get(endpoint)
    pr = _object(raw, "INVALID_PR_RESPONSE")
    head = _sha(
        _object(pr.get("head"), "INVALID_PR_RESPONSE").get("sha"),
        "INVALID_HEAD_SHA",
    )
    return pr, head


def validate_pending_identity(
    repository: str,
    pr_number: int,
    metadata: tuple[dict[str, object], str],
) -> PendingIdentity:
    """Validate only immutable routing identity needed for exact-head pending."""
    pr, head_sha = metadata
    if _integer(pr.get("number"), "INVALID_PR_NUMBER") != pr_number:
        raise LiveGateError("PR_NUMBER_MISMATCH")
    state = _string(pr.get("state"), "INVALID_PR_STATE")
    if state not in {"open", "closed"}:
        raise LiveGateError("INVALID_PR_STATE")
    base = _object(pr.get("base"), "INVALID_PR_RESPONSE")
    base_sha = _sha(base.get("sha"), "INVALID_BASE_SHA")
    if base.get("ref") != "main":
        raise LiveGateError("PR_BASE_NOT_MAIN")
    base_repository = _base_repository_name(pr)
    if base_repository != repository:
        raise LiveGateError("CROSS_REPOSITORY_PR")
    return PendingIdentity(
        pr=pr,
        number=pr_number,
        state=state,
        base_sha=base_sha,
        head_sha=head_sha,
        repository=repository,
    )


def validate_basic_snapshot(identity: PendingIdentity) -> BasicSnapshot:
    """Validate mutable PR fields immediately after pending."""
    pr = identity.pr
    draft = pr.get("draft")
    if not isinstance(draft, bool):
        raise LiveGateError("INVALID_PR_DRAFT")
    body_value = pr.get("body")
    body = "" if body_value is None else _string(body_value, "INVALID_PR_BODY")
    body_bytes = body.encode("utf-8")
    if len(body_bytes) > MAX_BODY_BYTES:
        raise LiveGateError("BODY_LIMIT_EXCEEDED")
    changed_count = _integer(pr.get("changed_files"), "INVALID_CHANGED_COUNT")
    if changed_count < 0:
        raise LiveGateError("INVALID_CHANGED_COUNT")
    if changed_count > MAX_CHANGED_FILES:
        raise LiveGateError("FILE_LIMIT_EXCEEDED")
    head_repository = _nested_repository_name(pr, "head")
    head_data = _object(pr.get("head"), "INVALID_PR_RESPONSE")
    actor_data = _object(head_data.get("user"), "INVALID_PR_RESPONSE")
    actor = _string(actor_data.get("login"), "INVALID_PR_RESPONSE")
    return BasicSnapshot(
        number=identity.number,
        state=identity.state,
        draft=draft,
        base_sha=identity.base_sha,
        head_sha=identity.head_sha,
        body=body,
        body_digest="sha256:" + hashlib.sha256(body_bytes).hexdigest(),
        changed_file_count=changed_count,
        repository=identity.repository,
        head_repository=head_repository,
        head_actor=actor,
    )


def snapshot_pr(
    transport: Transport,
    repository: str,
    pr_number: int,
    basic: BasicSnapshot | None = None,
) -> Snapshot:
    """Read one complete bounded PR snapshot."""
    current = (
        validate_basic_snapshot(
            validate_pending_identity(
                repository,
                pr_number,
                read_pr_metadata(transport, repository, pr_number),
            )
        )
        if basic is None
        else basic
    )
    paths = collect_changed_paths(
        transport,
        repository,
        pr_number,
        current.changed_file_count,
    )
    return Snapshot(
        number=pr_number,
        state=current.state,
        draft=current.draft,
        base_sha=current.base_sha,
        head_sha=current.head_sha,
        body=current.body,
        body_digest=current.body_digest,
        changed_file_count=current.changed_file_count,
        changed_paths=tuple(paths),
        path_digest=offline.sorted_path_digest(paths),
        repository=current.repository,
        head_repository=current.head_repository,
        head_actor=current.head_actor,
    )


def build_offline_context(
    snapshot: Snapshot,
    allowed_issue_refs: list[int],
    history_facts: list[dict[str, object]],
) -> dict[str, object]:
    """Build the bounded phase-1 context from primary facts."""
    context: dict[str, object] = {
        "schema_version": 1,
        "is_draft": snapshot.draft,
        "delivery": "pull_request",
        "base_sha": snapshot.base_sha,
        "head_sha": snapshot.head_sha,
        "changed_paths": list(snapshot.changed_paths),
        "allowed_issue_refs": allowed_issue_refs,
        "history_facts": history_facts,
    }
    encoded = json.dumps(
        context,
        ensure_ascii=False,
        separators=(",", ":"),
        sort_keys=True,
    ).encode("utf-8")
    if len(encoded) > MAX_CONTEXT_BYTES:
        raise LiveGateError("CONTEXT_LIMIT_EXCEEDED")
    return context


def sanitize_diagnostic(value: str) -> str:
    """Return a bounded one-line diagnostic without raw API or PR prose."""
    encoded = value.encode("utf-8")
    if len(encoded) > MAX_DIAGNOSTIC_BYTES:
        raise LiveGateError("DIAGNOSTIC_LIMIT_EXCEEDED")
    cleaned = "".join(
        char if char.isascii() and (char.isalnum() or char in "_-") else "_"
        for char in value
    ).strip("_")
    return cleaned or "LIVE_GATE_FAILURE"


def status_payload(state: str, code: str) -> dict[str, object]:
    """Return the exact stable commit-status payload."""
    descriptions = {
        "pending": "Completion claim evaluation pending",
        "success": "Completion claim evidence matches trusted snapshot",
        "failure": f"Completion claim evaluation failed: {sanitize_diagnostic(code)}",
    }
    if state not in descriptions:
        raise LiveGateError("INVALID_STATUS_STATE")
    description = descriptions[state]
    if len(description.encode("utf-8")) > MAX_STATUS_DESCRIPTION:
        raise LiveGateError("STATUS_DESCRIPTION_LIMIT_EXCEEDED")
    return {
        "state": state,
        "context": STATUS_CONTEXT,
        "description": description,
    }


def _write_status(
    transport: Transport,
    repository: str,
    head_sha: str,
    state: str,
    code: str,
) -> None:
    endpoint = f"/repos/{repository}/statuses/{head_sha}"
    response = transport.post(endpoint, status_payload(state, code))
    if not isinstance(response, dict):
        raise LiveGateError("STATUS_WRITE_FAILED")


def _valid_success_report(exit_code: int, report: object) -> bool:
    if exit_code != offline.EXIT_PASS or not isinstance(report, dict):
        return False
    return (
        report.get("schema_version") == 1
        and report.get("machine_status") == offline.PASS
        and report.get("diagnostics") == []
    )


def evaluate_pr(
    transport: Transport,
    repository: str,
    pr_number: int,
    checker: Checker = offline.evaluate,
) -> int:
    """Evaluate one PR and publish pending plus an exact-head terminal state."""
    head_sha: str | None = None
    pending_written = False
    failure_code = "LIVE_GATE_FAILURE"
    try:
        p1_metadata = read_pr_metadata(transport, repository, pr_number)
        head_sha = p1_metadata[1]
        p1_identity = validate_pending_identity(
            repository,
            pr_number,
            p1_metadata,
        )
        if p1_identity.state != "open":
            raise LiveGateError("PR_NOT_OPEN")
        _write_status(
            transport,
            repository,
            p1_identity.head_sha,
            "pending",
            "PENDING",
        )
        pending_written = True
        p1_basic = validate_basic_snapshot(p1_identity)
        payload, references = body_references(p1_basic.body)
        p1 = snapshot_pr(
            transport,
            repository,
            pr_number,
            p1_basic,
        )
        allowed_refs = _derive_allowed_issue_refs(
            transport,
            repository,
            references,
        )
        claims = [] if payload is None else structured_history(payload)
        history_facts = derive_history_facts(
            transport,
            repository,
            p1.head_sha,
            claims,
        )
        context = build_offline_context(p1, allowed_refs, history_facts)
        exit_code, report = checker(context, p1.body)
        p2_basic = validate_basic_snapshot(
            validate_pending_identity(
                repository,
                pr_number,
                read_pr_metadata(transport, repository, pr_number),
            )
        )
        body_references(p2_basic.body)
        p2 = snapshot_pr(
            transport,
            repository,
            pr_number,
            p2_basic,
        )
        if p1.comparison_key() != p2.comparison_key():
            raise LiveGateError("SNAPSHOT_MISMATCH")
        if not _valid_success_report(exit_code, report):
            raise LiveGateError("OFFLINE_CHECK_FAILED")
        _write_status(
            transport,
            repository,
            p1.head_sha,
            "success",
            "PASS",
        )
        return 0
    except LiveGateError as exc:
        failure_code = exc.code
    except Exception:
        failure_code = "UNEXPECTED_ADAPTER_ERROR"
    if head_sha is not None and pending_written:
        try:
            _write_status(
                transport,
                repository,
                head_sha,
                "failure",
                failure_code,
            )
        except LiveGateError:
            return 1
    return 1


def _event_pr_number(event: dict[str, object]) -> int:
    pull_request = _object(event.get("pull_request"), "INVALID_EVENT")
    number = _integer(pull_request.get("number"), "INVALID_PR_NUMBER")
    if number < 1:
        raise LiveGateError("INVALID_PR_NUMBER")
    return number


def _list_backfill_prs(transport: Transport, repository: str) -> list[int]:
    numbers: list[int] = []
    for page in range(1, MAX_BACKFILL_PAGES + 1):
        endpoint = (
            f"/repos/{repository}/pulls?state=open&base=main"
            f"&per_page=100&page={page}"
        )
        response = _array(transport.get(endpoint), "INVALID_BACKFILL_RESPONSE")
        for raw in response:
            entry = _object(raw, "INVALID_BACKFILL_RESPONSE")
            number = _integer(entry.get("number"), "INVALID_BACKFILL_RESPONSE")
            if number < 1:
                raise LiveGateError("INVALID_BACKFILL_RESPONSE")
            numbers.append(number)
            if len(numbers) > MAX_BACKFILL_PRS:
                raise LiveGateError("BACKFILL_LIMIT_EXCEEDED")
        if len(response) < FILES_PER_PAGE:
            break
    if len(set(numbers)) != len(numbers):
        raise LiveGateError("DUPLICATE_BACKFILL_PR")
    return numbers


def select_pr_numbers(
    event_name: str,
    event: dict[str, object],
    transport: Transport,
    repository: str,
) -> list[int]:
    """Select a bounded PR set from one exact workflow event."""
    _repository(repository)
    if event_name == "pull_request_target":
        action = _string(event.get("action"), "UNSUPPORTED_EVENT")
        if action not in PR_EVENT_TYPES:
            raise LiveGateError("UNSUPPORTED_EVENT")
        return [_event_pr_number(event)]
    if event_name == "repository_dispatch":
        if event.get("action") != "completion_claim_replay":
            raise LiveGateError("UNSUPPORTED_EVENT")
        payload = _object(event.get("client_payload"), "INVALID_PR_NUMBER")
        number = _integer(payload.get("pr_number"), "INVALID_PR_NUMBER")
        if number < 1:
            raise LiveGateError("INVALID_PR_NUMBER")
        return [number]
    if event_name == "push":
        if event.get("ref") != "refs/heads/main":
            raise LiveGateError("UNSUPPORTED_EVENT")
        return _list_backfill_prs(transport, repository)
    raise LiveGateError("UNSUPPORTED_EVENT")


def process_pr(
    transport: Transport,
    repository: str,
    pr_number: int,
    checker: Checker = offline.evaluate,
) -> int:
    """Evaluate exactly one matrix-selected pull request."""
    if isinstance(pr_number, bool) or not isinstance(pr_number, int):
        raise LiveGateError("INVALID_PR_NUMBER")
    if pr_number < 1:
        raise LiveGateError("INVALID_PR_NUMBER")
    return evaluate_pr(transport, repository, pr_number, checker)


def canonical_workflow_text() -> str:
    """Return the one reviewed UTF-8 workflow text, including its final LF."""
    return "\n".join(
        (
            "name: Completion Claim Live",
            "",
            "on:",
            "  pull_request_target:",
            "    types: [opened, reopened, synchronize, edited, "
            "ready_for_review, converted_to_draft]",
            "  push:",
            "    branches: [main]",
            "  repository_dispatch:",
            "    types: [completion_claim_replay]",
            "",
            "permissions: {}",
            "",
            "jobs:",
            "  discover:",
            "    runs-on: ubuntu-latest",
            "    timeout-minutes: 5",
            "    permissions:",
            "      contents: read",
            "      pull-requests: read",
            "    outputs:",
            "      pr_numbers: ${{ steps.select.outputs.pr_numbers }}",
            "    env:",
            "      GITHUB_TOKEN: ${{ secrets.GITHUB_TOKEN }}",
            "    steps:",
            "      - name: Checkout trusted workflow revision",
            "        uses: actions/checkout@"
            "fbc6f3992d24b796d5a048ff273f7fcc4a7b6c09",
            "        with:",
            "          ref: ${{ github.workflow_sha }}",
            "          persist-credentials: false",
            "          fetch-depth: 1",
            "      - name: Select bounded pull requests",
            "        id: select",
            '        run: python3 scripts/completion_claim_live.py select >> "$GITHUB_OUTPUT"',
            "",
            "  evaluate:",
            "    needs: discover",
            "    if: needs.discover.outputs.pr_numbers != '[]'",
            "    strategy:",
            "      fail-fast: false",
            "      matrix:",
            "        pr_number: ${{ fromJSON(needs.discover.outputs.pr_numbers) }}",
            "    concurrency:",
            "      group: completion-claim-live-${{ github.repository_id }}-"
            "${{ matrix.pr_number }}",
            "      cancel-in-progress: true",
            "    runs-on: ubuntu-latest",
            "    timeout-minutes: 5",
            "    permissions:",
            "      contents: read",
            "      pull-requests: read",
            "      issues: read",
            "      statuses: write",
            "    env:",
            "      GITHUB_TOKEN: ${{ secrets.GITHUB_TOKEN }}",
            "      COMPLETION_CLAIM_PR_NUMBER: ${{ matrix.pr_number }}",
            "    steps:",
            "      - name: Checkout trusted workflow revision",
            "        uses: actions/checkout@"
            "fbc6f3992d24b796d5a048ff273f7fcc4a7b6c09",
            "        with:",
            "          ref: ${{ github.workflow_sha }}",
            "          persist-credentials: false",
            "          fetch-depth: 1",
            "      - name: Evaluate one bounded live completion claim",
            "        run: python3 scripts/completion_claim_live.py process",
        )
    ) + "\n"


def _workflow_step_records(
    text: str,
) -> list[
    tuple[
        str,
        tuple[tuple[str, str], ...],
        tuple[tuple[str, str], ...],
    ]
]:
    """Parse exact step records without accepting YAML execution shorthand."""
    if "\t" in text:
        raise LiveGateError("WORKFLOW_STEP_STRUCTURE_MISMATCH")
    lines = text.splitlines()
    try:
        jobs_index = lines.index("jobs:")
    except ValueError as exc:
        raise LiveGateError("WORKFLOW_STEP_STRUCTURE_MISMATCH") from exc
    job_headers: list[tuple[int, str]] = []
    for index in range(jobs_index + 1, len(lines)):
        match = re.fullmatch(r"  ([a-z][a-z0-9_-]*):", lines[index])
        if match is not None:
            job_headers.append((index, match.group(1)))
    if [name for _, name in job_headers] != ["discover", "evaluate"]:
        raise LiveGateError("WORKFLOW_STEP_STRUCTURE_MISMATCH")

    records: list[
        tuple[
            str,
            tuple[tuple[str, str], ...],
            tuple[tuple[str, str], ...],
        ]
    ] = []
    for job_position, (job_start, job_name) in enumerate(job_headers):
        job_end = (
            job_headers[job_position + 1][0]
            if job_position + 1 < len(job_headers)
            else len(lines)
        )
        step_headers = [
            index
            for index in range(job_start + 1, job_end)
            if lines[index] == "    steps:"
        ]
        if len(step_headers) != 1:
            raise LiveGateError("WORKFLOW_STEP_STRUCTURE_MISMATCH")
        index = step_headers[0] + 1
        current_fields: list[tuple[str, str]] | None = None
        current_with: list[tuple[str, str]] = []

        def finish_current() -> None:
            nonlocal current_fields, current_with
            if current_fields is None:
                return
            records.append(
                (
                    job_name,
                    tuple(current_fields),
                    tuple(current_with),
                )
            )
            current_fields = None
            current_with = []

        while index < job_end:
            line = lines[index]
            if not line.strip():
                index += 1
                continue
            indent = len(line) - len(line.lstrip(" "))
            if indent <= 4:
                finish_current()
                break
            stripped = line[indent:]
            if indent == 6 and stripped.startswith("- "):
                finish_current()
                item = stripped[2:]
                if ":" not in item:
                    raise LiveGateError("WORKFLOW_STEP_STRUCTURE_MISMATCH")
                key, value = item.split(":", 1)
                current_fields = [(key, value.lstrip(" "))]
            elif indent == 8 and current_fields is not None:
                if stripped.startswith("- ") or ":" not in stripped:
                    raise LiveGateError("WORKFLOW_STEP_STRUCTURE_MISMATCH")
                key, value = stripped.split(":", 1)
                if any(existing == key for existing, _ in current_fields):
                    raise LiveGateError("WORKFLOW_STEP_STRUCTURE_MISMATCH")
                current_fields.append((key, value.lstrip(" ")))
            elif (
                indent == 10
                and current_fields is not None
                and current_fields[-1] == ("with", "")
            ):
                if stripped.startswith("- ") or ":" not in stripped:
                    raise LiveGateError("WORKFLOW_STEP_STRUCTURE_MISMATCH")
                key, value = stripped.split(":", 1)
                if any(existing == key for existing, _ in current_with):
                    raise LiveGateError("WORKFLOW_STEP_STRUCTURE_MISMATCH")
                current_with.append((key, value.lstrip(" ")))
            else:
                raise LiveGateError("WORKFLOW_STEP_STRUCTURE_MISMATCH")
            index += 1
        else:
            finish_current()

    all_execution = re.findall(
        r"(?m)^[ ]*(?:-[ ]+)?(uses|run):[ ]*([^\r\n]*)$",
        text,
    )
    parsed_execution = [
        (key, value)
        for _, fields, _ in records
        for key, value in fields
        if key in {"uses", "run"}
    ]
    if all_execution != parsed_execution:
        raise LiveGateError("WORKFLOW_STEP_STRUCTURE_MISMATCH")
    return records


def validate_workflow_text(text: str) -> None:
    """Fail if the trusted workflow's static security contract is weakened."""
    if text != canonical_workflow_text():
        raise LiveGateError("WORKFLOW_CANONICAL_TEXT_MISMATCH")
    checkout = (
        "actions/checkout@"
        "fbc6f3992d24b796d5a048ff273f7fcc4a7b6c09"
    )
    checkout_fields = (
        ("name", "Checkout trusted workflow revision"),
        ("uses", checkout),
        ("with", ""),
    )
    checkout_with = (
        ("ref", "${{ github.workflow_sha }}"),
        ("persist-credentials", "false"),
        ("fetch-depth", "1"),
    )
    expected_records = [
        ("discover", checkout_fields, checkout_with),
        (
            "discover",
            (
                ("name", "Select bounded pull requests"),
                ("id", "select"),
                (
                    "run",
                    "python3 scripts/completion_claim_live.py select"
                    ' >> "$GITHUB_OUTPUT"',
                ),
            ),
            (),
        ),
        ("evaluate", checkout_fields, checkout_with),
        (
            "evaluate",
            (
                ("name", "Evaluate one bounded live completion claim"),
                ("run", "python3 scripts/completion_claim_live.py process"),
            ),
            (),
        ),
    ]
    if _workflow_step_records(text) != expected_records:
        raise LiveGateError("WORKFLOW_STEP_STRUCTURE_MISMATCH")
    required = (
        "pull_request_target:",
        "types: [opened, reopened, synchronize, edited, ready_for_review, converted_to_draft]",
        "push:",
        "branches: [main]",
        "repository_dispatch:",
        "types: [completion_claim_replay]",
        "permissions: {}",
        "  discover:",
        "  evaluate:",
        "needs: discover",
        "if: needs.discover.outputs.pr_numbers != '[]'",
        "pr_number: ${{ fromJSON(needs.discover.outputs.pr_numbers) }}",
        "group: completion-claim-live-${{ github.repository_id }}-${{ matrix.pr_number }}",
        "cancel-in-progress: true",
        "timeout-minutes: 5",
        "ref: ${{ github.workflow_sha }}",
        "persist-credentials: false",
        "fetch-depth: 1",
        'python3 scripts/completion_claim_live.py select >> "$GITHUB_OUTPUT"',
        "python3 scripts/completion_claim_live.py process",
    )
    for token in required:
        if token not in text:
            raise LiveGateError("WORKFLOW_CONTRACT_MISMATCH")
    checkout_pins = re.findall(r"actions/checkout@([0-9a-f]{40})", text)
    if len(checkout_pins) != 2 or len(set(checkout_pins)) != 1:
        raise LiveGateError("WORKFLOW_CHECKOUT_NOT_PINNED")
    forbidden = (
        "workflow_dispatch",
        "github.event",
        "github.head_ref",
        "github.ref",
        "github.event.pull_request.head",
        "github.event.pull_request.merge",
        "actions/cache",
        "download-artifact",
        "upload-artifact",
        "persist-credentials: true",
        "statuses: read",
        "permissions: write-all",
        "permissions: read-all",
    )
    if any(token in text for token in forbidden):
        raise LiveGateError("WORKFLOW_FORBIDDEN_CAPABILITY")
    if text.count("ref: ${{ github.workflow_sha }}") != 2:
        raise LiveGateError("WORKFLOW_CONTRACT_MISMATCH")
    if text.count("persist-credentials: false") != 2:
        raise LiveGateError("WORKFLOW_CONTRACT_MISMATCH")
    if text.count("fetch-depth: 1") != 2:
        raise LiveGateError("WORKFLOW_CONTRACT_MISMATCH")
    if text.count("cancel-in-progress: true") != 1:
        raise LiveGateError("WORKFLOW_CONTRACT_MISMATCH")

    permission_headers = list(
        re.finditer(r"(?m)^([ ]*)permissions:(.*)$", text)
    )
    if len(permission_headers) != 3:
        raise LiveGateError("WORKFLOW_PERMISSION_MISMATCH")
    if permission_headers[0].group(1) != "" or permission_headers[0].group(2) != " {}":
        raise LiveGateError("WORKFLOW_PERMISSION_MISMATCH")

    def permission_block(header: re.Match[str]) -> set[str]:
        indent = len(header.group(1))
        if header.group(2) != "":
            raise LiveGateError("WORKFLOW_PERMISSION_MISMATCH")
        entries: set[str] = set()
        following = text[header.end() :].splitlines()
        for line in following[1:]:
            if not line.strip():
                continue
            line_indent = len(line) - len(line.lstrip(" "))
            if line_indent <= indent:
                break
            if line_indent != indent + 2:
                raise LiveGateError("WORKFLOW_PERMISSION_MISMATCH")
            stripped = line.strip()
            if re.fullmatch(r"[a-z-]+: (?:read|write)", stripped) is None:
                raise LiveGateError("WORKFLOW_PERMISSION_MISMATCH")
            entries.add(stripped)
        return entries

    if permission_headers[1].group(1) != "    ":
        raise LiveGateError("WORKFLOW_PERMISSION_MISMATCH")
    if permission_headers[2].group(1) != "    ":
        raise LiveGateError("WORKFLOW_PERMISSION_MISMATCH")
    if permission_block(permission_headers[1]) != {
        "contents: read",
        "pull-requests: read",
    }:
        raise LiveGateError("WORKFLOW_PERMISSION_MISMATCH")
    if permission_block(permission_headers[2]) != {
        "contents: read",
        "pull-requests: read",
        "issues: read",
        "statuses: write",
    }:
        raise LiveGateError("WORKFLOW_PERMISSION_MISMATCH")

    expressions = re.findall(r"\${{\s*(.*?)\s*}}", text, flags=re.DOTALL)
    if text.count("${{") != len(expressions):
        raise LiveGateError("WORKFLOW_EXPRESSION_MALFORMED")
    allowed_expressions = {
        "steps.select.outputs.pr_numbers",
        "secrets.GITHUB_TOKEN",
        "github.workflow_sha",
        "needs.discover.outputs.pr_numbers != '[]'",
        "fromJSON(needs.discover.outputs.pr_numbers)",
        "github.repository_id",
        "matrix.pr_number",
    }
    if any(expression not in allowed_expressions for expression in expressions):
        raise LiveGateError("UNTRUSTED_WORKFLOW_EXPRESSION")
    digest = hashlib.sha256(text.encode("utf-8")).hexdigest()
    if digest != WORKFLOW_SHA256:
        raise LiveGateError("WORKFLOW_DIGEST_MISMATCH")


class GitHubTransport:
    """Bounded stdlib REST transport for fixed GitHub repository endpoints."""

    def __init__(self, token: str, repository: str) -> None:
        if not token:
            raise LiveGateError("MISSING_TOKEN")
        self._token = token
        self._repository = _repository(repository)
        self._prefix = f"/repos/{self._repository}/"
        sha = r"[0-9a-f]{40}"
        number = r"[1-9][0-9]*"
        self._trusted_get = re.compile(
            rf"(?:pulls/{number}|"
            rf"pulls/{number}/files\?per_page=100&page={number}|"
            rf"issues/{number}|issues/{number}/parent|"
            rf"commits/{sha}(?:\?per_page=(?:1|100)&page={number})?|"
            rf"compare/{sha}\.\.\.{sha}|"
            rf"contents/[A-Za-z0-9%._~!$&'()*+,;=:@/-]+\?ref={sha}|"
            rf"pulls\?state=open&base=main&per_page=100&page={number})\Z"
        )

    def _request(
        self,
        method: str,
        path: str,
        payload: dict[str, object] | None,
        allow_not_found: bool,
    ) -> object:
        if not path.startswith(self._prefix):
            raise LiveGateError("UNTRUSTED_API_PATH")
        if any(char in path for char in "\r\n\x00"):
            raise LiveGateError("UNTRUSTED_API_PATH")
        body = None
        if payload is not None:
            body = json.dumps(
                payload,
                separators=(",", ":"),
                sort_keys=True,
            ).encode("utf-8")
            if len(body) > MAX_CONTEXT_BYTES:
                raise LiveGateError("REQUEST_LIMIT_EXCEEDED")
        headers = {
            "Accept": "application/vnd.github+json",
            "Authorization": f"Bearer {self._token}",
            "User-Agent": "ising-model-completion-claim-live",
            "X-GitHub-Api-Version": "2022-11-28",
        }
        url = API_BASE + path
        for attempt in range(REQUEST_RETRIES + 1):
            req = request.Request(url, data=body, headers=headers, method=method)
            try:
                with request.urlopen(
                    req,
                    timeout=REQUEST_TIMEOUT_SECONDS,
                ) as response:
                    raw = response.read(MAX_API_RESPONSE_BYTES + 1)
                if len(raw) > MAX_API_RESPONSE_BYTES:
                    raise LiveGateError("API_RESPONSE_LIMIT_EXCEEDED")
                try:
                    return json.loads(raw)
                except (json.JSONDecodeError, UnicodeDecodeError) as exc:
                    raise LiveGateError("MALFORMED_API_RESPONSE") from exc
            except error.HTTPError as exc:
                if exc.code == 404 and allow_not_found:
                    return None
                if exc.code in {429, 403}:
                    raise LiveGateError("API_RATE_LIMIT") from exc
                if exc.code < 500 or attempt >= REQUEST_RETRIES:
                    raise LiveGateError("API_HTTP_ERROR") from exc
            except (error.URLError, TimeoutError, OSError) as exc:
                if attempt >= REQUEST_RETRIES:
                    raise LiveGateError("API_TIMEOUT") from exc
            time.sleep(0.25 * (attempt + 1))
        raise LiveGateError("API_RETRY_EXHAUSTED")

    def get(self, path: str, *, allow_not_found: bool = False) -> object:
        """Read one fixed endpoint."""
        if not path.startswith(self._prefix):
            raise LiveGateError("UNTRUSTED_API_PATH")
        if self._trusted_get.fullmatch(path[len(self._prefix) :]) is None:
            raise LiveGateError("UNTRUSTED_API_PATH")
        return self._request("GET", path, None, allow_not_found)

    def post(self, path: str, payload: dict[str, object]) -> object:
        """Write one fixed status endpoint."""
        expected = f"/repos/{self._repository}/statuses/"
        if not path.startswith(expected) or SHA_RE.fullmatch(path[len(expected) :]) is None:
            raise LiveGateError("UNTRUSTED_STATUS_PATH")
        return self._request("POST", path, payload, False)


def _read_event(path: Path) -> dict[str, object]:
    with path.open("rb") as handle:
        raw = handle.read(MAX_EVENT_BYTES + 1)
    if len(raw) > MAX_EVENT_BYTES:
        raise LiveGateError("EVENT_LIMIT_EXCEEDED")
    try:
        value = json.loads(raw)
    except (json.JSONDecodeError, UnicodeDecodeError) as exc:
        raise LiveGateError("INVALID_EVENT") from exc
    return _object(value, "INVALID_EVENT")


def main(argv: list[str] | None = None) -> int:
    """Run from the trusted workflow environment."""
    try:
        arguments = sys.argv[1:] if argv is None else argv
        if arguments not in (["select"], ["process"]):
            raise LiveGateError("INVALID_MODE")
        mode = arguments[0]
        repository = _repository(os.environ.get("GITHUB_REPOSITORY"))
        token = _string(os.environ.get("GITHUB_TOKEN"), "MISSING_TOKEN")
        transport = GitHubTransport(token, repository)
        if mode == "select":
            event_name = _string(
                os.environ.get("GITHUB_EVENT_NAME"),
                "INVALID_EVENT",
            )
            event_path = Path(
                _string(os.environ.get("GITHUB_EVENT_PATH"), "INVALID_EVENT")
            )
            event = _read_event(event_path)
            numbers = select_pr_numbers(
                event_name,
                event,
                transport,
                repository,
            )
            print(
                "pr_numbers="
                + json.dumps(numbers, separators=(",", ":"))
            )
            return 0
        raw_number = _string(
            os.environ.get("COMPLETION_CLAIM_PR_NUMBER"),
            "INVALID_PR_NUMBER",
        )
        if PR_NUMBER_RE.fullmatch(raw_number) is None:
            raise LiveGateError("INVALID_PR_NUMBER")
        return process_pr(
            transport,
            repository,
            int(raw_number),
        )
    except LiveGateError as exc:
        code = sanitize_diagnostic(exc.code)
        print(json.dumps({"code": code, "status": "failure"}, sort_keys=True))
        return 1


if __name__ == "__main__":
    sys.exit(main())

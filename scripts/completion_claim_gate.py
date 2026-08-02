#!/usr/bin/env python3
"""Validate completion-claim evidence against an offline pull-request snapshot.

The supplied context is the trusted boundary.  Pull-request Markdown is
untrusted input.  This module deliberately performs no repository discovery,
process execution, network access, or credential handling.
"""

from __future__ import annotations

import argparse
import bisect
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
MAX_ANCHORED_REFERENCES = 16
MAX_CLOSING_TRAILERS = 8
MAX_BARE_MENTIONS = 64
MAX_DIRECTIVE_SCAN_REFERENCES = 1_000
# No trailer paragraph can carry more anchored references than both caps allow,
# so a longer run of trailer-shaped lines is refused before it is buffered.
MAX_TRAILER_PARAGRAPH_LINES = MAX_ANCHORED_REFERENCES + MAX_CLOSING_TRAILERS
# One trailer line carries at most MAX_ANCHORED_REFERENCES numbers after one
# keyword.  Thirty-two characters per number is far beyond any real issue
# number, so a longer line cannot be a trailer and is never handed to the
# multi-number grammar, whose match state grows with the run it accepts.
MAX_TRAILER_LINE_CHARS = 32 * (MAX_ANCHORED_REFERENCES + 1)

SHA_RE = re.compile(r"[0-9a-f]{40}\Z")
DIGEST_RE = re.compile(r"sha256:[0-9a-f]{64}\Z")
NON_CLOSING_RE = re.compile(r"(Refs|Part of) #([1-9][0-9]*)\Z")
# One raw trailer line may carry several space-separated non-closing references
# (`Refs #4850 #4851 #4830`), the shape this repository already writes.  The
# closing keywords keep the one-per-line rule: several numbers on a line GitHub
# acts on would be a real ambiguity, while these numbers close nothing.
NON_CLOSING_TRAILER_RE = re.compile(r"(Refs|Part of)((?: #[1-9][0-9]*)+)\Z")
CANONICAL_CLOSING_RE = re.compile(r"(?:Closes|Fixes|Resolves) #([1-9][0-9]*)")
BARE_REF_RE = re.compile(r"#([1-9][0-9]*)")
GH_REF_RE = re.compile(r"\bGH-([1-9][0-9]*)", re.IGNORECASE)
RAW_HTML_RE = re.compile(r"<[A-Za-z!/?]")
# CommonMark email autolinks whose local part starts with a digit or symbol are
# not tag-shaped, so the delimiter scan above cannot see them.  The local part
# stops at the first "@" so the scan stays backtracking-free.
EMAIL_AUTOLINK_RE = re.compile(r"<[^\s<>@]*@[^\s<>]*>")
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
CLOSE_KEYWORDS = tuple(
    sorted((keyword.lower() for keyword in OFFICIAL_CLOSE_KEYWORDS), key=len, reverse=True)
)
NON_CLOSING_DIRECTIVES = ("part of", "refs")
ISSUE_REFERENCE_AT_RE = re.compile(ISSUE_REFERENCE_PATTERN, re.IGNORECASE)
ISSUE_MENTION_RE = re.compile(ISSUE_REFERENCE_PATTERN, re.IGNORECASE)
MARKDOWN_SEPARATOR_CHARS = frozenset(""":;,.-–—!?()[]{}*_~`'"<>|/\\""")
FUTURE_PLAN_RE = re.compile(
    r"\b(?:future|later|next\s+phase|phase\s+[0-9]+|plan(?:ned)?|"
    r"remain(?:s|ing)?|todo|follow[- ]?up|will)\b",
    re.IGNORECASE,
)
FENCE_OPEN_RE = re.compile(r"^( {0,3})(`{3,}|~{3,})([^\r\n]*)$")
# The two closers are precompiled per marker: the fence scan runs once per body
# line, and rebuilding one pattern string per line is pure overhead.
FENCE_CLOSE_RE = {
    "`": re.compile(r" {0,3}(`{3,})[ \t]*"),
    "~": re.compile(r" {0,3}(~{3,})[ \t]*"),
}
# CommonMark code-span delimiters: a run of N backticks is closed by the next run
# of exactly N backticks.  The blank-line shape below bounds that search to one
# paragraph, because inline parsing never crosses a block boundary.
BACKTICK_RUN_RE = re.compile(r"`+")
BLANK_LINE_RE = re.compile(r"\n[ \t]*(?=\n)")
NON_NEWLINE_RE = re.compile(r"[^\n]")
# Masked code stands in as a character that is neither alphanumeric nor a
# Markdown separator, so a directive scan stops at it instead of stepping over
# the removed text onto a reference that never followed the keyword.
MASK_FILLER = "\ufffd"
HISTORY_ACTIONS = frozenset({"added", "modified", "deleted"})
MANAGED_MODE = "managed"
PROSE_MODE = "prose"
UNKNOWN_MODE = "unknown"
# Claim families a managed block can state and prose cannot; prose mode reports
# them as unverified instead of silently dropping them.
UNVERIFIED_CLAIM_FAMILIES = (
    "candidate_diff",
    "review_records",
    "semantic_claims",
    "history_claims",
)

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


def _validate_unicode_text(text: str, where: str) -> bytes:
    for char in text:
        category = unicodedata.category(char)
        if category == "Cs" or category == "Cc" and char not in "\t\n\r":
            raise GateInputError(
                "INVALID_UNICODE",
                f"{where} contains a surrogate or invalid control character",
            )
    try:
        return text.encode("utf-8")
    except UnicodeEncodeError as error:
        raise GateInputError("INVALID_UNICODE", f"{where} is not valid Unicode") from error


def _validate_json_unicode(value: Any, label: str) -> None:
    stack: list[tuple[Any, str]] = [(value, label)]
    while stack:
        current, where = stack.pop()
        if isinstance(current, str):
            _validate_unicode_text(current, where)
        elif isinstance(current, dict):
            for key, child in current.items():
                if isinstance(key, str):
                    _validate_unicode_text(key, f"{where} key")
                stack.append((child, f"{where}.{key!r}"))
        elif isinstance(current, list):
            stack.extend(
                (child, f"{where}[{index}]")
                for index, child in enumerate(current)
            )


def _duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise GateInputError("DUPLICATE_JSON_KEY", f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _parse_json(text: str, label: str) -> Any:
    try:
        value = json.loads(text, object_pairs_hook=_duplicate_keys)
        _validate_json_unicode(value, label)
        return value
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
    encoded = _validate_unicode_text(value, where)
    if value == PENDING and allow_pending:
        return value
    if not value or len(encoded) > MAX_TEXT_BYTES:
        raise GateInputError("INVALID_TEXT", f"{where} must be nonempty and bounded")
    return value


def _exact_keys(value: dict[str, Any], expected: frozenset[str], where: str) -> None:
    for key in value:
        _string(key, f"{where} key")
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
    pattern = FENCE_CLOSE_RE.get(marker)
    if pattern is None:
        return False
    match = pattern.fullmatch(line.removesuffix("\r"))
    return match is not None and len(match.group(1)) >= minimum


def _fenced_spans(text: str) -> list[tuple[int, int]]:
    """Return the character spans of fenced code blocks, delimiters included.

    The fence bookkeeping is the one :func:`extract_managed_document` uses, so a
    reference scan and the managed-block parser agree on what a fence is.  An
    unclosed fence runs to the end of the document, as CommonMark specifies.
    """
    spans: list[tuple[int, int]] = []
    offset = 0
    opening: tuple[str, int, int] | None = None
    for line in text.split("\n"):
        start = offset
        offset = min(offset + len(line) + 1, len(text))
        if opening is None:
            fence = _fence(line)
            if fence is not None:
                marker, minimum, _ = fence
                opening = (marker, minimum, start)
            continue
        marker, minimum, fence_start = opening
        if _fence_closes(line, marker, minimum):
            spans.append((fence_start, offset))
            opening = None
    if opening is not None:
        spans.append((opening[2], len(text)))
    return spans


def _blank_line_between(breaks: list[tuple[int, int]], start: int, end: int) -> bool:
    index = bisect.bisect_left(breaks, (start, start))
    return index < len(breaks) and breaks[index][1] <= end


def _code_span_spans(text: str, base: int) -> list[tuple[int, int]]:
    """Return the code-span character spans of one fence-free region.

    Openers are matched left to right against the next backtick run of the same
    length, which is CommonMark's rule; a candidate closer beyond a blank line
    belongs to another block and therefore closes nothing.
    """
    runs = [match.span() for match in BACKTICK_RUN_RE.finditer(text)]
    breaks = [
        (match.start(), match.end() + 1) for match in BLANK_LINE_RE.finditer(text)
    ]
    by_length: dict[int, list[int]] = {}
    for index, (start, end) in enumerate(runs):
        by_length.setdefault(end - start, []).append(index)
    spans: list[tuple[int, int]] = []
    index = 0
    while index < len(runs):
        start, end = runs[index]
        candidates = by_length[end - start]
        position = bisect.bisect_right(candidates, index)
        if position < len(candidates):
            closing_start, closing_end = runs[candidates[position]]
            if not _blank_line_between(breaks, end, closing_start):
                spans.append((base + start, base + closing_end))
                index = candidates[position] + 1
                continue
        index += 1
    return spans


def masked_code_containers(text: str) -> str:
    """Return ``text`` with code containers masked out, offsets preserved.

    GitHub resolves no issue reference inside a fenced block or an inline code
    span, so neither may anchor one here.  Every masked character becomes
    :data:`MASK_FILLER` and every newline survives, which keeps character
    offsets and line numbering identical to the input: the raw trailer scan and
    the normalized keyword scan can therefore both read this view and still be
    compared.  Fences are masked first, so a stray backtick inside a fence
    cannot open a code span and a code span cannot swallow a fence.

    One filler serves both containers, and it is deliberately neither
    alphanumeric, nor a Markdown separator, nor blank-line shaped.  A separator
    would let a keyword reach across the removed words onto a later reference
    (``closed `note` (#4822)``) and invent a pairing the body does not have.
    Whitespace would be worse: a masked region spanning a line ending would
    leave lines that look empty and fake the paragraph break that makes a
    trailer standalone.

    That last property is what makes an imprecise fence harmless rather than
    exploitable.  :func:`_fenced_spans` matches fence indentation against the
    document, while CommonMark measures it against the enclosing container and
    closes a container's fences when the container ends, so a fence opened
    inside a list item and closed at column 0 desynchronizes the two.  With no
    blank-line-shaped filler anywhere, such a disagreement can only mask the
    wrong characters; it can never manufacture the paragraph boundary that
    would let code-block text pass for an isolated trailer.
    """
    fenced = _fenced_spans(text)
    inline: list[tuple[int, int]] = []
    cursor = 0
    for start, end in fenced:
        inline.extend(_code_span_spans(text[cursor:start], cursor))
        cursor = end
    inline.extend(_code_span_spans(text[cursor:], cursor))
    if not fenced and not inline:
        return text
    parts: list[str] = []
    cursor = 0
    # Fenced and inline spans are disjoint by construction: the code spans are
    # read from the gaps between fences, so one sorted merge walks them all.
    for start, end in sorted(fenced + inline):
        parts.append(text[cursor:start])
        parts.append(NON_NEWLINE_RE.sub(MASK_FILLER, text[start:end]))
        cursor = end
    parts.append(text[cursor:])
    return "".join(parts)


def extract_managed_document(body: str) -> tuple[str, str]:
    """Return the sole canonical top-level JSON block and all other text."""
    lines = body.split("\n")
    ordinary_fence: tuple[str, int] | None = None
    managed_opening: int | None = None
    canonical_openings: list[int] = []
    blocks: list[tuple[int, int, str]] = []
    for index, line in enumerate(lines):
        if managed_opening is not None:
            if line.removesuffix("\r") == "```":
                blocks.append(
                    (
                        managed_opening,
                        index,
                        "\n".join(lines[managed_opening + 1 : index]),
                    )
                )
                managed_opening = None
            continue
        if ordinary_fence is not None:
            marker, minimum = ordinary_fence
            if _fence_closes(line, marker, minimum):
                ordinary_fence = None
            continue
        if line.removesuffix("\r") == BLOCK_FENCE:
            canonical_openings.append(index)
            managed_opening = index
            continue
        opening_fence = _fence(line)
        if opening_fence is not None:
            marker, minimum, _ = opening_fence
            ordinary_fence = (marker, minimum)

    normalized_marker_count = _normalized_marker_count(body)
    if len(canonical_openings) != 1:
        if normalized_marker_count:
            raise GateInputError(
                "AMBIGUOUS_MANAGED_BLOCK",
                "managed label is not one canonical top-level opener",
            )
        raise GateInputError("MISSING_MANAGED_BLOCK", "managed evidence block is missing")
    if normalized_marker_count != 1:
        raise GateInputError(
            "AMBIGUOUS_MANAGED_BLOCK",
            "normalized managed marker count must equal one canonical opener",
        )
    opening = canonical_openings[0]
    matching = [block for block in blocks if block[0] == opening]
    if not matching:
        raise GateInputError(
            "MALFORMED_MANAGED_BLOCK",
            "canonical managed evidence block is unclosed",
        )
    if len(blocks) != 1:
        raise GateInputError(
            "AMBIGUOUS_MANAGED_BLOCK",
            "exactly one canonical managed block is required",
        )
    opening, closing, content = matching[0]
    unmanaged = "\n".join(lines[:opening] + lines[closing + 1 :])
    return content, unmanaged


def extract_managed_block(body: str) -> str:
    """Compatibility helper returning the JSON text from the managed document."""
    return extract_managed_document(body)[0]


def _normalized_body_text(body: str) -> str:
    normalized = unicodedata.normalize("NFKC", html.unescape(body))
    return "".join(
        char for char in normalized if unicodedata.category(char) != "Cf"
    )


def _normalized_marker_count(body: str) -> int:
    return _normalized_body_text(body).count(BLOCK_INFO)


def managed_marker_count(body: str) -> int:
    """Return the normalized managed-marker count that selects the body mode."""
    return _normalized_marker_count(body)


def _issue_number(reference: str) -> int:
    normalized = unicodedata.normalize("NFKC", reference)
    match = re.search(r"(?:#|/(?:issues|pull)/)([1-9][0-9]*)\Z", normalized)
    if match is None:
        raise GateInputError("INVALID_ISSUE_REF", f"invalid issue reference: {reference}")
    return int(match.group(1))


def _is_markdown_separator(char: str) -> bool:
    return char.isspace() or char in MARKDOWN_SEPARATOR_CHARS


def _ascii_alnum(char: str) -> bool:
    return char.isascii() and char.isalnum()


def _keyword_spans(projected: str, keywords: tuple[str, ...]) -> list[tuple[int, int]]:
    spans: list[tuple[int, int]] = []
    cursor = 0
    while cursor < len(projected):
        matched = False
        for keyword in keywords:
            end = cursor + len(keyword)
            if projected[cursor:end].lower() != keyword:
                continue
            before_ok = cursor == 0 or not _ascii_alnum(projected[cursor - 1])
            after_ok = end == len(projected) or not _ascii_alnum(projected[end])
            if before_ok and after_ok:
                spans.append((cursor, end))
                cursor = end
                matched = True
                break
        if not matched:
            cursor += 1
    return spans


def _too_many_references(message: str) -> GateInputError:
    return GateInputError("TOO_MANY_ISSUE_REFERENCES", message)


def _directive_references(
    projected: str, keywords: tuple[str, ...], *, multi: bool = False, limit: int
) -> list[tuple[str, int, str]]:
    """Return ``(keyword, reference offset, reference)`` for anchored mentions.

    With ``multi`` the scan keeps following a run of single-space-separated bare
    references after one keyword, exactly the shape :data:`NON_CLOSING_TRAILER_RE`
    accepts.  The scan must count every number the trailer grammar counts, or the
    multiset comparison in :func:`parse_body_references` would reject the very
    ``Refs #1 #2`` line it is meant to allow.  Any wider separator stops the run,
    so a decorated or wrapped list still fails that comparison.

    ``limit`` is enforced while the run is being followed rather than after it is
    materialized: a body may hold a reference run far longer than any cap, and
    parsing all of it before rejecting it is a needless memory and time cost.
    """
    references: list[tuple[str, int, str]] = []
    for keyword_start, keyword_end in _keyword_spans(projected, keywords):
        cursor = keyword_end
        while cursor < len(projected) and _is_markdown_separator(projected[cursor]):
            cursor += 1
        reference = ISSUE_REFERENCE_AT_RE.match(projected, cursor)
        if reference is None:
            continue
        keyword = projected[keyword_start:keyword_end].lower()
        references.append((keyword, reference.start(), reference.group(0)))
        if len(references) > limit:
            raise _too_many_references("body has too many issue directives")
        cursor = reference.end()
        while multi and projected.startswith(" #", cursor):
            follower = BARE_REF_RE.match(projected, cursor + 1)
            if follower is None:
                break
            references.append((keyword, follower.start(), follower.group(0)))
            if len(references) > limit:
                raise _too_many_references("body has too many issue directives")
            cursor = follower.end()
    return references


def _references_after(projected: str, keywords: tuple[str, ...]) -> list[str]:
    return [
        reference
        for _, _, reference in _directive_references(
            projected, keywords, multi=True, limit=MAX_DIRECTIVE_SCAN_REFERENCES
        )
    ]


def _is_trailer_line(line: str) -> bool:
    """Return whether one line is shaped like a canonical trailer of either kind.

    The length guard runs first: a line no trailer can be that long is refused
    before the multi-number grammar walks it, which keeps a pathological run of
    references cheap to reject instead of expensive to parse.
    """
    return len(line) <= MAX_TRAILER_LINE_CHARS and (
        CANONICAL_CLOSING_RE.fullmatch(line) is not None
        or NON_CLOSING_TRAILER_RE.fullmatch(line) is not None
    )


def _trailer_lines(masked_body: str) -> list[str]:
    """Return the lines of every paragraph that contains nothing but trailers.

    A canonical trailer stands alone, so its paragraph — the maximal run of
    non-blank lines around it — may hold trailer lines and nothing else.  Reading
    a line on its own cannot see the prose bleeding into it from the neighbouring
    line, which is how ``This PR does not\\nRefs #4801\\n.`` and a blockquote's
    lazy continuation (``> Quoted evidence:\\nRefs #4801``) both look like
    standalone trailers to a per-line scan while GitHub renders them as one
    paragraph.  No masked container reads as blank here, so neither a fence nor
    an inline span crossing a line ending can fake that separation: a trailer
    directly below a closing fence needs the blank line every other paragraph
    needs, and a fence this scanner places wrongly cannot invent one.
    """
    lines: list[str] = []
    paragraph: list[str] = []
    isolated = True
    for raw in masked_body.split("\n"):
        line = raw.removesuffix("\r")
        # CommonMark's blank line is spaces and tabs only.  Python's `strip`
        # would also swallow a no-break or ideographic space, and a line of
        # those separates no paragraph GitHub renders.
        if not line.strip(" \t"):
            if isolated:
                lines.extend(paragraph)
            paragraph = []
            isolated = True
            continue
        if not isolated:
            continue
        if not _is_trailer_line(line):
            paragraph = []
            isolated = False
            continue
        paragraph.append(line)
        if len(paragraph) > MAX_TRAILER_PARAGRAPH_LINES:
            raise _too_many_references("body has too many anchored issue references")
    if isolated:
        lines.extend(paragraph)
    return lines


def _closing_trailer_numbers(trailer_lines: list[str]) -> list[int]:
    """Return issue numbers from raw standalone ``Closes #N`` trailer lines."""
    numbers: list[int] = []
    for line in trailer_lines:
        match = CANONICAL_CLOSING_RE.fullmatch(line)
        if match is None:
            continue
        numbers.append(int(match.group(1)))
        if len(numbers) > MAX_CLOSING_TRAILERS:
            raise _too_many_references("body has too many closing trailers")
    return numbers


def _non_closing_kind(keyword: str) -> str:
    """Return the canonical spelling of a scanned non-closing directive keyword."""
    return "Refs" if keyword == "refs" else "Part of"


def _non_closing_trailers(trailer_lines: list[str]) -> list[tuple[str, int]]:
    """Return ``(kind, number)`` from raw standalone ``Refs``/``Part of`` lines.

    A line may list several references after one keyword; each number is returned
    separately, so the caller compares numbers rather than lines.  The cap is
    applied per number, so an unbounded run is refused before it is built.
    """
    references: list[tuple[str, int]] = []
    for line in trailer_lines:
        match = NON_CLOSING_TRAILER_RE.fullmatch(line)
        if match is None:
            continue
        for number in BARE_REF_RE.finditer(match.group(2)):
            references.append((match.group(1), int(number.group(1))))
            if len(references) > MAX_ANCHORED_REFERENCES:
                raise _too_many_references(
                    "body has too many anchored issue references"
                )
    return references


def parse_body_references(
    body: str,
) -> tuple[tuple[tuple[str, int], ...], tuple[int, ...]]:
    """Return prose-mode ``(anchored, mentions)`` references, failing closed.

    ``anchored`` holds ``(kind, number)`` for every ``Refs``/``Part of``/``Closes``
    directive; ``mentions`` holds the remaining bare ``#N`` and ``GH-N`` numbers,
    which carry no authority.  Every anchored reference must appear as a standalone
    canonical trailer line, so a negated or decorated sentence such as "This does
    not Closes #4801." is rejected rather than silently honoured.  The rule covers
    the non-closing directives too: their numbers widen issue authority here (they
    seed the live hierarchy walk), so a quoted, fenced, wrapped, or line-split
    ``Refs #4801`` must not pass for the reference it only looks like.

    Both halves of that comparison read one masked view of the body, in which
    fenced blocks and inline code spans are masked out, and both accept a trailer
    line only inside a paragraph of trailers.  A per-line scan is otherwise blind
    to Markdown containers: it would anchor a reference from inside a code fence,
    from a multi-line code span or link label, or from a line the surrounding
    paragraph negates.  Masking both halves at once keeps them consistent, so a
    fenced reference is simply not a candidate rather than a spurious mismatch;
    it stays visible as an unverified mention.

    A non-closing trailer may list several references (``Refs #4850 #4851``); a
    closing trailer may not, because GitHub acts on the numbers it carries.
    """
    normalized = _normalized_body_text(body)
    masked = masked_code_containers(normalized)
    trailer_lines = _trailer_lines(masked_code_containers(body))
    closing = _directive_references(masked, CLOSE_KEYWORDS, limit=MAX_CLOSING_TRAILERS)
    trailers = _closing_trailer_numbers(trailer_lines)
    if sorted(_issue_number(reference) for _, _, reference in closing) != sorted(trailers):
        raise GateInputError(
            "AMBIGUOUS_CLOSING_DIRECTIVE",
            "closing keywords must appear only as standalone canonical trailers",
        )
    anchored: list[tuple[str, int]] = [("Closes", number) for number in trailers]
    anchored_starts = {start for _, start, _ in closing}
    scanned = _directive_references(
        masked, NON_CLOSING_DIRECTIVES, multi=True, limit=MAX_ANCHORED_REFERENCES
    )
    for _, _, reference in scanned:
        if BARE_REF_RE.fullmatch(reference) is None:
            raise GateInputError(
                "UNSUPPORTED_ISSUE_REF_FORM",
                f"only bare same-repository references are supported: {reference}",
            )
    non_closing = _non_closing_trailers(trailer_lines)
    scanned_pairs = sorted(
        (_non_closing_kind(keyword), int(reference[1:]))
        for keyword, _, reference in scanned
    )
    if scanned_pairs != sorted(non_closing):
        raise GateInputError(
            "AMBIGUOUS_NON_CLOSING_DIRECTIVE",
            "non-closing keywords must appear only as standalone canonical trailers",
        )
    anchored.extend(non_closing)
    anchored_starts.update(start for _, start, _ in scanned)
    if len(anchored) > MAX_ANCHORED_REFERENCES:
        raise GateInputError(
            "TOO_MANY_ISSUE_REFERENCES", "body has too many anchored issue references"
        )
    numbers = [number for _, number in anchored]
    if len(set(numbers)) != len(numbers):
        raise GateInputError(
            "DUPLICATE_ISSUE_REF", "anchored issue references contain duplicates"
        )
    if not anchored:
        raise GateInputError(
            "MISSING_ISSUE_REFERENCE",
            "body needs at least one Refs, Part of, or Closes reference",
        )
    numbered = {
        int(match.group(1))
        for match in BARE_REF_RE.finditer(normalized)
        if match.start() not in anchored_starts
    }
    # GitHub also resolves the "GH-N" shorthand.  It is never anchored here, but
    # reporting it keeps it visible instead of dropping it from the body silently.
    numbered.update(int(match.group(1)) for match in GH_REF_RE.finditer(normalized))
    mentions = sorted(numbered)
    if len(mentions) > MAX_BARE_MENTIONS:
        raise GateInputError(
            "TOO_MANY_ISSUE_REFERENCES", "body has too many bare issue mentions"
        )
    return tuple(anchored), tuple(mentions)


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


def _reject_directive_keywords(normalized: str) -> None:
    if _keyword_spans(normalized, CLOSE_KEYWORDS):
        raise GateInputError(
            "DIRECTIVE_KEYWORD_FORBIDDEN",
            "body contains a forbidden closing directive token",
        )


def _reject_raw_html(normalized: str, *, strict: bool = True) -> None:
    """Reject HTML; ``strict`` bans every less-than, otherwise markup shapes.

    The relaxed scan keeps a comparison such as ``value < bound`` legal, so it
    matches tag openers by shape.  An email autolink whose local part starts with
    a digit or a symbol is angle-delimited without being tag-shaped, hence the
    second scan; both report ``RAW_HTML_FORBIDDEN``.
    """
    if strict:
        if "<" in normalized:
            raise GateInputError(
                "RAW_HTML_FORBIDDEN",
                "body contains a forbidden less-than delimiter",
            )
    elif RAW_HTML_RE.search(normalized) is not None:
        raise GateInputError(
            "RAW_HTML_FORBIDDEN",
            "body contains a forbidden markup delimiter",
        )
    elif EMAIL_AUTOLINK_RE.search(normalized) is not None:
        raise GateInputError(
            "RAW_HTML_FORBIDDEN",
            "body contains a forbidden autolink delimiter",
        )


def _check_references(
    raw: Any,
    context: dict[str, Any],
    normalized: str,
) -> None:
    references = _object(raw, "references")
    _exact_keys(references, REFERENCE_KEYS, "references")
    non_closing = _array(references["non_closing"], "references.non_closing", 1_000)
    closing = _array(references["closing"], "references.closing", 1_000)
    if closing:
        raise GateInputError("CLOSING_REFERENCES_NOT_EMPTY", "references.closing must be empty")
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
    for reference in _references_after(normalized, NON_CLOSING_DIRECTIVES):
        if _issue_number(reference) not in allowed:
            raise GateInputError(
                "UNMANAGED_ISSUE_REF",
                f"body has a disallowed non-closing reference: {reference}",
            )


def _check_prose_references(
    anchored: tuple[tuple[str, int], ...],
    context: dict[str, Any],
) -> None:
    """Bind every non-closing prose reference to the trusted issue allowlist."""
    allowed = set(context["allowed_issue_refs"])
    for kind, number in anchored:
        if kind != "Closes" and number not in allowed:
            raise GateInputError(
                "UNMANAGED_ISSUE_REF",
                f"body has a disallowed non-closing reference: #{number}",
            )


def _charge_unmanaged_prose(
    unmanaged: str, human_reviews: list[dict[str, str]]
) -> None:
    if not unmanaged.strip():
        return
    human_reviews.append(_human_review("unmanaged_prose", "body-outside-managed-block"))
    normalized = _normalized_body_text(unmanaged)
    if ISSUE_MENTION_RE.search(normalized) is not None:
        human_reviews.append(
            _human_review("unmanaged_issue_reference", "body-issue-reference")
        )
    if FUTURE_PLAN_RE.search(normalized) is not None:
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


def _report(
    status: str,
    diagnostics: list[dict[str, str]],
    human_reviews: list[dict[str, str]],
    mode: str,
) -> dict[str, Any]:
    return {
        "schema_version": SCHEMA_VERSION,
        "machine_status": status,
        "diagnostics": diagnostics,
        "human_reviews": human_reviews,
        "body_mode": mode,
    }


def _evaluate_managed(
    context_raw: Any, body: str, normalized_body: str
) -> tuple[int, dict[str, Any]]:
    """Evaluate a body that carries a managed evidence block."""
    _reject_raw_html(normalized_body)
    _reject_directive_keywords(normalized_body)
    _validate_json_unicode(context_raw, "context")
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
    _check_references(payload["references"], context, normalized_body)
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
    return code, _report(status, diagnostics, human_reviews, MANAGED_MODE)


def _evaluate_prose(
    context_raw: Any, body: str, normalized_body: str
) -> tuple[int, dict[str, Any]]:
    """Evaluate a plain-prose body: references are verified, claims are not."""
    _reject_raw_html(normalized_body, strict=False)
    _validate_json_unicode(context_raw, "context")
    context = _validate_context(context_raw)
    anchored, mentions = parse_body_references(body)
    _check_prose_references(anchored, context)
    human_reviews = [
        _human_review("unverified_claim_family", family)
        for family in UNVERIFIED_CLAIM_FAMILIES
    ]
    if context["is_draft"]:
        human_reviews.append(_human_review("draft_state", "body-draft-state"))
    human_reviews.extend(
        _human_review("unverified_issue_mention", f"#{number}") for number in mentions
    )
    _charge_unmanaged_prose(body, human_reviews)
    return EXIT_PASS, _report(PASS, [], human_reviews, PROSE_MODE)


def evaluate(context_raw: Any, body: str) -> tuple[int, dict[str, Any]]:
    """Evaluate parsed context and Markdown; return ``(exit_code, report)``."""
    mode = UNKNOWN_MODE
    try:
        if not isinstance(body, str):
            raise GateInputError("INVALID_TYPE", "body must be a string")
        if len(_validate_unicode_text(body, "body")) > MAX_BODY_BYTES:
            raise GateInputError("INPUT_TOO_LARGE", "body exceeds the size limit")
        normalized_body = _normalized_body_text(body)
        mode = MANAGED_MODE if managed_marker_count(body) else PROSE_MODE
        if mode == MANAGED_MODE:
            return _evaluate_managed(context_raw, body, normalized_body)
        return _evaluate_prose(context_raw, body, normalized_body)
    except GateInputError as error:
        return (
            EXIT_FAIL,
            _report(FAIL, [_diagnostic(error.code, error.message)], [], mode),
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
            _report(FAIL, [_diagnostic(error.code, error.message)], [], UNKNOWN_MODE),
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

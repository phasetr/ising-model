#!/usr/bin/env python3
"""Fail-closed repository-native link checks for tracked Markdown.

The supported grammar is intentionally bounded.  Outside code, this checker
accepts inline Markdown links/images and reference links/definitions, plus
explicit ``<a id=...>`` / ``<a name=...>`` fragment owners.  Raw local HTML
href/src, Liquid link tags, and local-link-shaped text not consumed by that
grammar are findings rather than silently ignored syntax.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
import urllib.parse
from collections import Counter
from dataclasses import dataclass
from pathlib import Path, PurePosixPath

REPO_ROOT = Path(__file__).resolve().parent.parent
MARKDOWN_PATHS = ("README.md", "docs")
LANDING = "docs/index.md"
CANONICAL_OWNERS = frozenset({
    "docs/status.md", "docs/library-map.md", "docs/refactoring-rollback-ledger.md",
    "docs/references.md", "docs/theorems/index.md", "docs/coverage/index.md",
})

_OPEN_FENCE_RE = re.compile(r"^[ \t]{0,3}(?:(`{3,})([^`]*)|(~{3,})(.*))$")
_HEADING_RE = re.compile(r"^[ \t]{0,3}(#{1,6})[ \t]+(.+?)[ \t]*#*[ \t]*$")
_DEFINITION_RE = re.compile(r"^[ \t]{0,3}\[([^]\n]+)\]:[ \t]*(<[^>]+>|\S+)[ \t]*$")
_INLINE_RE = re.compile(
    r"(!?)\[([^]\n]*)\]\([ \t]*(<[^>\n]+>|[^\s)]*)"
    r"(?:[ \t]+(?:\"[^\"\n]*\"|'[^'\n]*'|\([^()\n]*\)))?[ \t]*\)"
)
_REFERENCE_USE_RE = re.compile(r"(!?)\[([^]\n]*)\]\[([^]\n]*)\]")
_RAW_CANDIDATE_RE = re.compile(
    r"!?\[[^]\n]*?\]\([ \t]*(?:<[^>\s]+>|[^\s)]*)"
    r"(?:[ \t]+(?:\"[^\"\n]*\"|'[^'\n]*'|\([^()\n]*\)))?[ \t]*\)"
)
_RAW_REFERENCE_DEF_RE = re.compile(r"^[ \t]{0,3}\[[^]\n]+\]:")
_RAW_REFERENCE_USE_RE = re.compile(r"!?\[[^]\n]*\]\[[^]\n]*(?:\]|$)")
_RAW_HTML_LINK_RE = re.compile(
    r"<[^>]+\b(?:href|src)[ \t\n]*=[ \t\n]*(?:(['\"])(.*?)\1|([^\s>]+))[^>]*>", re.I | re.S
)
_LIQUID_LINK_RE = re.compile(r"{%[ \t\n]*link[ \t\n]+([^%]+?)[ \t\n]*%}", re.S)
_EXPLICIT_ANCHOR_RE = re.compile(r"<a[ \t]+(?:id|name)[ \t]*=[ \t]*(['\"])([^'\"]+)\1[ \t]*></a>", re.I)
_SCHEME_RE = re.compile(r"^[A-Za-z][A-Za-z0-9+.-]*:")


@dataclass(frozen=True, order=True)
class Finding:
    source: str
    line: int
    code: str
    destination: str
    detail: str

    def render(self) -> str:
        target = f" `{self.destination}`" if self.destination else ""
        return f"V5: {self.source}:{self.line}: {self.code}:{target} {self.detail}".rstrip()


@dataclass(frozen=True)
class Link:
    source: str
    line: int
    destination: str
    image: bool = False
    label: str = ""


@dataclass(frozen=True)
class ParsedMarkdown:
    links: tuple[Link, ...]
    findings: tuple[Finding, ...]
    headings: tuple[str, ...]
    explicit_anchors: tuple[tuple[str, int], ...]
    candidate_count: int
    consumed_count: int
    candidate_identities: tuple[tuple[int, int, str], ...]
    consumed_identities: tuple[tuple[int, int, str], ...]


def _git_names(root: Path, pathspecs: tuple[str, ...] | None) -> tuple[list[str], list[Finding]]:
    """Run one stable ``git ls-files`` query and decode it fail-closed."""
    command = ["git", "ls-files", "-z"]
    if pathspecs is not None:
        command += ["--", *pathspecs]
    try:
        proc = subprocess.run(command, cwd=root, capture_output=True, check=False)
    except OSError as exc:
        return [], [Finding("<git>", 0, "TRACKED_SET", "", f"could not run git: {exc}")]
    if proc.returncode != 0:
        stderr = proc.stderr.decode("utf-8", errors="replace").strip()
        return [], [Finding("<git>", 0, "TRACKED_SET", "", f"git ls-files failed: {stderr}")]
    try:
        names = [name for name in proc.stdout.decode("utf-8").split("\0") if name]
    except UnicodeDecodeError as exc:
        return [], [Finding("<git>", 0, "TRACKED_SET", "", f"non-UTF-8 path: {exc}")]
    if not names:
        return [], [Finding("<git>", 0, "TRACKED_SET", "", "git ls-files returned an empty tracked set")]
    return sorted(names), []


def _is_doc_markdown(name: str) -> bool:
    return name == "README.md" or (name.startswith("docs/") and name.endswith(".md"))


def tracked_markdown(root: Path = REPO_ROOT) -> tuple[list[str], list[Finding]]:
    names, failures = _git_names(root, MARKDOWN_PATHS)
    return sorted(name for name in names if _is_doc_markdown(name)), failures


def raw_tracked_markdown(root: Path = REPO_ROOT) -> tuple[list[str], list[Finding]]:
    """Independently derive scope from every tracked name, not MARKDOWN_PATHS."""
    names, failures = _git_names(root, None)
    return sorted(name for name in names if _is_doc_markdown(name)), failures


def _external(destination: str) -> bool:
    return bool(_SCHEME_RE.match(destination)) or destination.startswith("//")


def _local_shaped(text: str) -> bool:
    text = text.strip(" <>\"'")
    return bool(text) and not _external(text) and (
        text.startswith(('.', '/', '#')) or '/' in text or '\\' in text
        or re.search(r"\.(?:md|html?|png|jpe?g|gif|svg|pdf)(?:[?#]|$)", text, re.I) is not None
    )


def _raw_local(destination: str) -> bool:
    """Classify raw HTML/Liquid destinations without an extension proxy."""
    destination = destination.strip(" <>\"'")
    return bool(destination) and not _external(destination)


def _mask_inline_code_and_comments(line: str, active: bool) -> tuple[str, bool, bool]:
    """Blank escapes, code spans, and HTML comments in Markdown order.

    Returns the masked line, the outgoing HTML-comment state, and whether an
    unmatched backtick run was encountered.  An active comment owns its bytes
    until ``-->``; otherwise escapes and code spans prevent a literal ``<!--``
    inside them from changing comment state.
    """
    chars = list(line)
    pos = 0
    while pos < len(line):
        if active:
            close = line.find("-->", pos)
            end = len(line) if close < 0 else close + 3
            chars[pos:end] = " " * (end - pos)
            if close < 0:
                return "".join(chars), True, False
            active = False
            pos = end
            continue
        if line[pos] == "\\":
            slash_end = pos
            while slash_end < len(line) and line[slash_end] == "\\":
                slash_end += 1
            if line.startswith("<!--", slash_end):
                slash_count = slash_end - pos
                chars[pos:slash_end] = " " * slash_count
                if slash_count % 2 == 1:
                    chars[slash_end:slash_end + 4] = " " * 4
                    pos = slash_end + 4
                else:
                    pos = slash_end
                continue
        if line[pos] == "`":
            end = pos
            while end < len(line) and line[end] == "`":
                end += 1
            marker = "`" * (end - pos)
            close = line.find(marker, end)
            if close < 0:
                return "".join(chars), active, True
            chars[pos:close + len(marker)] = " " * (close + len(marker) - pos)
            pos = close + len(marker)
            continue
        if line.startswith("<!--", pos):
            active = True
            continue
        pos += 1
    return "".join(chars), active, False


def parse_markdown(source: str, text: str) -> ParsedMarkdown:
    """Parse the bounded grammar and enforce raw candidate coverage."""
    inline_links: list[Link] = []
    definitions: dict[str, Link] = {}
    uses: list[tuple[int, str, bool, str]] = []
    findings: list[Finding] = []
    headings: list[str] = []
    anchors: list[tuple[str, int]] = []
    candidate_identities: list[tuple[int, int, str]] = []
    consumed_identities: list[tuple[int, int, str]] = []
    fence_char = ""
    fence_length = 0
    html_comment = False
    masked_lines: list[str] = []
    lines = text.splitlines()
    for lineno, raw in enumerate(lines, 1):
        if fence_char:
            masked_lines.append(" " * len(raw))
            close = re.match(rf"^[ \t]{{0,3}}{re.escape(fence_char)}{{{fence_length},}}[ \t]*$", raw)
            if close:
                fence_char, fence_length = "", 0
            continue
        if not html_comment:
            opener = _OPEN_FENCE_RE.match(raw)
            if opener:
                masked_lines.append(" " * len(raw))
                marker = opener.group(1) or opener.group(3)
                fence_char, fence_length = marker[0], len(marker)
                continue
        line, html_comment, unmatched = _mask_inline_code_and_comments(raw, html_comment)
        masked_lines.append(line)
        if unmatched:
            findings.append(Finding(source, lineno, "MALFORMED_CODE_SPAN", "", "unmatched backtick run"))
            continue
        for match in _RAW_HTML_LINK_RE.finditer(line):
            destination = match.group(2) or match.group(3)
            if _raw_local(destination):
                candidate_identities.append((lineno, match.start(), "raw-html"))
                findings.append(Finding(source, lineno, "RAW_LOCAL_HTML", destination, "local href/src is outside the supported Markdown grammar"))
                if destination.startswith("#"):
                    inline_links.append(Link(source, lineno, destination))
        for match in _LIQUID_LINK_RE.finditer(line):
            destination = match.group(1).strip()
            if _raw_local(destination):
                candidate_identities.append((lineno, match.start(), "liquid"))
                findings.append(Finding(source, lineno, "LIQUID_LOCAL_LINK", destination, "Liquid links are not GitHub-native Markdown"))
                if destination.startswith("#"):
                    inline_links.append(Link(source, lineno, destination))
        for match in _EXPLICIT_ANCHOR_RE.finditer(line):
            anchors.append((match.group(2), lineno))
        heading = _HEADING_RE.match(line)
        if heading:
            headings.append(heading.group(2).strip())
        # Count syntax independently of destination classification.  External
        # links are consumed by the same grammar, so including both sides keeps
        # this census exact without asking the grammar parser for its input.
        raw_inline = list(_RAW_CANDIDATE_RE.finditer(line))
        punctuation = list(re.finditer(r"\]\(", line))
        parsed_inline = list(_INLINE_RE.finditer(line))
        raw_positions = {line.find("](", match.start()) for match in raw_inline}
        parsed_positions = {line.find("](", match.start()) for match in parsed_inline}
        candidate_identities.extend((lineno, position, "inline") for position in raw_positions)
        candidate_identities.extend(
            (lineno, match.start(), "inline") for match in punctuation
            if match.start() not in raw_positions and match.start() not in parsed_positions
        )
        consumed_identities.extend((lineno, position, "inline") for position in parsed_positions)
        for match in parsed_inline:
            image = bool(match.group(1))
            label = match.group(2)
            destination = match.group(3).strip("<>")
            inline_links.append(Link(source, lineno, destination, image, label))
        raw_defs = bool(_RAW_REFERENCE_DEF_RE.match(line))
        definition = _DEFINITION_RE.match(line)
        if raw_defs:
            candidate_identities.append((lineno, 0, "definition"))
        if definition:
            consumed_identities.append((lineno, definition.start(), "definition"))
            key = " ".join(definition.group(1).casefold().split())
            item = Link(source, lineno, definition.group(2).strip("<>"))
            if key in definitions:
                findings.append(Finding(source, lineno, "DUPLICATE_REFERENCE", item.destination, f"duplicate label [{key}]"))
            else:
                definitions[key] = item
        raw_uses = list(_RAW_REFERENCE_USE_RE.finditer(line))
        parsed_uses = list(_REFERENCE_USE_RE.finditer(line))
        candidate_identities.extend((lineno, match.start(), "reference") for match in raw_uses)
        consumed_identities.extend((lineno, match.start(), "reference") for match in parsed_uses)
        for match in parsed_uses:
            key = " ".join((match.group(3) or match.group(2)).casefold().split())
            uses.append((lineno, key, bool(match.group(1)), match.group(2)))
        # Any local-link punctuation that was not consumed is a hard finding.
        if len(punctuation) != len(parsed_inline):
            findings.append(Finding(source, lineno, "UNPARSED_LOCAL_LINK", raw.strip(), "link punctuation was not consumed by the bounded grammar"))
    masked_text = "\n".join(masked_lines)
    starts = [0]
    for match in re.finditer("\n", masked_text):
        starts.append(match.end())
    for kind, pattern, code, detail in (
        ("raw-html-multiline", _RAW_HTML_LINK_RE, "RAW_LOCAL_HTML", "multiline local href/src is outside the supported Markdown grammar"),
        ("liquid-multiline", _LIQUID_LINK_RE, "LIQUID_LOCAL_LINK", "multiline Liquid links are not GitHub-native Markdown"),
    ):
        for match in pattern.finditer(masked_text):
            if "\n" not in match.group(0):
                continue
            destination = (match.group(2) or match.group(3)) if kind.startswith("raw-html") else match.group(1).strip()
            if not _raw_local(destination):
                continue
            lineno = sum(start <= match.start() for start in starts)
            column = match.start() - starts[lineno - 1]
            candidate_identities.append((lineno, column, kind))
            findings.append(Finding(source, lineno, code, destination, detail))
    if fence_char:
        findings.append(Finding(source, len(lines) or 1, "MALFORMED_FENCE", "", "unclosed fenced code block"))
    if html_comment:
        findings.append(Finding(source, len(lines) or 1, "MALFORMED_HTML_COMMENT", "", "unclosed HTML comment"))
    used: set[str] = set()
    for lineno, key, image, label in uses:
        if key not in definitions:
            findings.append(Finding(source, lineno, "MISSING_REFERENCE", key, "reference label has no definition"))
            continue
        used.add(key)
        definition = definitions[key]
        inline_links.append(Link(source, lineno, definition.destination, image, label))
    for key, definition in definitions.items():
        if key not in used and _local_shaped(definition.destination):
            findings.append(Finding(source, definition.line, "UNUSED_LOCAL_REFERENCE", definition.destination, f"definition [{key}] renders no link"))
    if Counter(candidate_identities) != Counter(consumed_identities):
        findings.append(Finding(
            source, 0, "CANDIDATE_COVERAGE", "",
            f"raw candidate identities do not match grammar consumptions "
            f"({len(candidate_identities)} raw, {len(consumed_identities)} parsed)",
        ))
    return ParsedMarkdown(
        tuple(inline_links), tuple(findings), tuple(headings), tuple(anchors),
        len(candidate_identities), len(consumed_identities),
        tuple(candidate_identities), tuple(consumed_identities),
    )


def _rendered_heading_text(heading: str) -> str:
    heading = re.sub(r"!\[([^]]*)\]\([^)]*\)", r"\1", heading)
    heading = re.sub(r"\[([^]]+)\]\([^)]*\)", r"\1", heading)
    heading = re.sub(r"<[^>]*>", "", heading)
    return re.sub(r"[*_~`]", "", heading)


def github_anchors(headings: tuple[str, ...], explicit: tuple[tuple[str, int], ...], source: str) -> tuple[set[str], list[Finding]]:
    anchors: set[str] = set()
    findings: list[Finding] = []
    counts: dict[str, int] = {}
    for heading in headings:
        plain = _rendered_heading_text(heading).strip().lower()
        base = re.sub(r"[^\w\- ]", "", plain, flags=re.UNICODE).replace(" ", "-")
        count = counts.get(base, 0)
        slug = base if count == 0 else f"{base}-{count}"
        counts[base] = count + 1
        if slug in anchors:
            findings.append(Finding(source, 0, "DUPLICATE_ANCHOR", slug, "generated anchor is duplicated"))
        anchors.add(slug)
    for anchor, lineno in explicit:
        if anchor in anchors:
            findings.append(Finding(source, lineno, "DUPLICATE_ANCHOR", anchor, "explicit anchor duplicates another owner"))
        anchors.add(anchor)
    return anchors, findings


def _resolve(source: str, destination: str) -> tuple[str, str]:
    parsed = urllib.parse.urlsplit(destination)
    decoded = urllib.parse.unquote(parsed.path)
    base = PurePosixPath(source).parent
    parts: list[str] = []
    for part in (base / decoded).parts:
        if part in ("", "."):
            continue
        if part == "..":
            if not parts:
                return "", urllib.parse.unquote(parsed.fragment)
            parts.pop()
        else:
            parts.append(part)
    return PurePosixPath(*parts).as_posix(), urllib.parse.unquote(parsed.fragment)


def _load_markdown_anchors(root: Path, target: str) -> tuple[set[str], list[Finding]]:
    """Load fragment owners for a tracked Markdown target outside scan scope."""
    try:
        text = (root / target).read_text(encoding="utf-8")
    except (OSError, UnicodeError) as exc:
        return set(), [Finding(target, 0, "UNREADABLE", "", str(exc))]
    parsed = parse_markdown(target, text)
    return github_anchors(parsed.headings, parsed.explicit_anchors, target)


def check(root: Path = REPO_ROOT) -> tuple[list[Finding], list[str], list[Link]]:
    names, findings = tracked_markdown(root)
    raw_names, raw_failures = raw_tracked_markdown(root)
    findings += raw_failures
    if not names:
        findings.append(Finding("<scope>", 0, "EMPTY_MARKDOWN_SCOPE", "", "no tracked README/docs Markdown"))
    if names != raw_names:
        findings.append(Finding("<scope>", 0, "SCOPE_MISMATCH", "", f"scoped {len(names)} != independent raw {len(raw_names)}"))
    tracked_names, tracked_failures = _git_names(root, None)
    findings += tracked_failures
    if findings:
        return sorted(set(findings)), [], []
    tracked = set(tracked_names)
    all_links: list[Link] = []
    anchors_by_source: dict[str, set[str]] = {}
    visited: list[str] = []
    for name in names:
        path = root / name
        try:
            if not path.is_file() or path.is_symlink():
                raise OSError("not a regular file")
            text = path.read_text(encoding="utf-8")
        except (OSError, UnicodeError) as exc:
            findings.append(Finding(name, 0, "UNREADABLE", "", str(exc)))
            continue
        visited.append(name)
        parsed = parse_markdown(name, text)
        all_links.extend(parsed.links)
        findings.extend(parsed.findings)
        anchors, anchor_findings = github_anchors(parsed.headings, parsed.explicit_anchors, name)
        anchors_by_source[name] = anchors
        findings.extend(anchor_findings)
    edges: set[tuple[str, str]] = set()
    for link in all_links:
        destination = link.destination
        if link.image and not link.label.strip():
            findings.append(Finding(link.source, link.line, "EMPTY_IMAGE_ALT", destination, "image alt text must be nonempty"))
        if not destination:
            findings.append(Finding(link.source, link.line, "MISSING_TARGET", destination, "link destination is empty"))
            continue
        if _external(destination):
            continue
        parsed_url = urllib.parse.urlsplit(destination)
        if parsed_url.query:
            findings.append(Finding(link.source, link.line, "QUERY_NOT_ALLOWED", destination, "repository-local links may not carry queries"))
            continue
        if "\\" in destination:
            findings.append(Finding(link.source, link.line, "BACKSLASH_PATH", destination, "repository paths use forward slashes"))
            continue
        if parsed_url.path.startswith("/"):
            findings.append(Finding(link.source, link.line, "ROOT_ABSOLUTE_PATH", destination, "repository-local links must be source-relative"))
            continue
        if destination.startswith("#"):
            target, fragment = link.source, urllib.parse.unquote(destination[1:])
        else:
            target, fragment = _resolve(link.source, destination)
        if not target:
            findings.append(Finding(link.source, link.line, "PATH_ESCAPE", destination, "target escapes repository"))
            continue
        if parsed_url.path.lower().endswith(".html"):
            findings.append(Finding(link.source, link.line, "LOCAL_HTML", destination, "link must name tracked source, not Jekyll output"))
            continue
        if target not in tracked:
            findings.append(Finding(link.source, link.line, "MISSING_TARGET", destination, f"case-sensitive tracked target `{target}` does not exist"))
            continue
        target_path = root / target
        if not target_path.is_file() or target_path.is_symlink():
            findings.append(Finding(link.source, link.line, "NONREGULAR_TARGET", destination, f"`{target}` is not a regular file"))
            continue
        edges.add((link.source, target))
        if fragment:
            if target.lower().endswith(".md") and target not in anchors_by_source:
                anchors, anchor_findings = _load_markdown_anchors(root, target)
                anchors_by_source[target] = anchors
                findings.extend(anchor_findings)
            if fragment not in anchors_by_source.get(target, set()):
                findings.append(Finding(link.source, link.line, "MISSING_FRAGMENT", destination, f"fragment not found in `{target}`"))
    if ("README.md", LANDING) not in edges:
        findings.append(Finding("README.md", 0, "README_REACHABILITY", LANDING, "README must render a direct link to the landing"))
    reached = {target for source, target in edges if source == LANDING}
    for owner in sorted(CANONICAL_OWNERS - reached):
        findings.append(Finding(LANDING, 0, "OWNER_REACHABILITY", owner, "landing must render a direct link to canonical owner"))
    return sorted(set(findings)), visited, all_links


def main() -> int:
    parser = argparse.ArgumentParser(description="Check tracked Markdown links")
    parser.add_argument("--check", action="store_true", help="check the tracked tree (default)")
    parser.add_argument("--root", type=Path, default=REPO_ROOT, help="repository root (test/diagnostic use)")
    parser.add_argument("--self-test", action="store_true", help="run scripts/test_docs_link_check.py")
    args = parser.parse_args()
    if args.self_test:
        from test_docs_link_check import run_suite  # noqa: PLC0415
        return run_suite()
    findings, visited, links = check(args.root.resolve())
    if findings:
        for finding in findings:
            print(finding.render())
        print(f"documentation links: FAIL ({len(findings)} findings; {len(visited)} files read)")
        return 1
    local = sum(1 for link in links if link.destination and not _external(link.destination))
    fragments = sum(1 for link in links if not _external(link.destination) and urllib.parse.urlsplit(link.destination).fragment)
    print(f"documentation links: PASS ({len(visited)} tracked Markdown files; {local} local links; {fragments} fragments)")
    return 0


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""Fail-closed checks for repository-native links in tracked Markdown.

The authored documentation is read on GitHub as source.  Repository-local
links therefore name tracked source files (normally ``.md``), never Jekyll's
derived ``.html`` output.  This checker deliberately has a narrow remit: local
target existence, Markdown heading fragments, image targets, and the two entry
point reachability contracts.  It neither fetches external URLs nor judges the
documentation's prose.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
import urllib.parse
from dataclasses import dataclass
from pathlib import Path, PurePosixPath

REPO_ROOT = Path(__file__).resolve().parent.parent
MARKDOWN_PATHS = ("README.md", "docs")
LANDING = "docs/index.md"
CANONICAL_OWNERS = frozenset(
    {
        "docs/status.md",
        "docs/library-map.md",
        "docs/refactoring-rollback-ledger.md",
        "docs/references.md",
        "docs/theorems/index.md",
        "docs/coverage/index.md",
    }
)

_FENCE_RE = re.compile(r"^[ \t]{0,3}(`{3,}|~{3,})(?:[^`~]*)$")
_HEADING_RE = re.compile(r"^[ \t]{0,3}(#{1,6})[ \t]+(.+?)[ \t]*#*[ \t]*$")
_REFERENCE_RE = re.compile(r"^[ \t]{0,3}\[([^]]+)\]:[ \t]*(\S+)")
_INLINE_LINK_RE = re.compile(r"!?\[[^]\n]*\]\([ \t]*(<[^>]+>|[^\s)]+)")
_REFERENCE_USE_RE = re.compile(r"!?\[([^]\n]+)\]\[([^]\n]*)\]")
_SCHEME_RE = re.compile(r"^[A-Za-z][A-Za-z0-9+.-]*:")


@dataclass(frozen=True, order=True)
class Finding:
    """One stable, source-located link failure."""

    source: str
    line: int
    code: str
    destination: str
    detail: str

    def render(self) -> str:
        """Return the human-readable diagnostic."""
        target = f" `{self.destination}`" if self.destination else ""
        return f"V5: {self.source}:{self.line}: {self.code}:{target} {self.detail}".rstrip()


@dataclass(frozen=True)
class Link:
    """A local-or-external destination extracted from Markdown prose."""

    source: str
    line: int
    destination: str


def tracked_markdown(root: Path = REPO_ROOT) -> tuple[list[str], list[Finding]]:
    """Return the tracked README/docs Markdown population, failing closed."""
    try:
        proc = subprocess.run(
            ["git", "ls-files", "-z", "--", *MARKDOWN_PATHS],
            cwd=root,
            capture_output=True,
            check=False,
        )
    except OSError as exc:
        return [], [Finding("<git>", 0, "TRACKED_SET", "", f"could not run git: {exc}")]
    if proc.returncode != 0:
        detail = proc.stderr.decode("utf-8", errors="replace").strip()
        return [], [Finding("<git>", 0, "TRACKED_SET", "", f"git ls-files failed: {detail}")]
    try:
        names = [name for name in proc.stdout.decode("utf-8").split("\0") if name]
    except UnicodeDecodeError as exc:
        return [], [Finding("<git>", 0, "TRACKED_SET", "", f"non-UTF-8 path: {exc}")]
    names = sorted(name for name in names if name == "README.md" or name.endswith(".md"))
    if not names:
        return [], [Finding("<git>", 0, "TRACKED_SET", "", "no tracked Markdown matched")]
    return names, []


def _mask_code(line: str) -> tuple[str, bool]:
    """Blank paired inline-code spans; report whether a delimiter is unmatched."""
    chars = list(line)
    index = 0
    while index < len(chars):
        if chars[index] != "`":
            index += 1
            continue
        end_run = index
        while end_run < len(chars) and chars[end_run] == "`":
            end_run += 1
        marker = "`" * (end_run - index)
        close = line.find(marker, end_run)
        if close < 0:
            return "".join(chars), True
        for pos in range(index, close + len(marker)):
            chars[pos] = " "
        index = close + len(marker)
    return "".join(chars), False


def parse_markdown(source: str, text: str) -> tuple[list[Link], dict[str, Link], list[Finding], list[str]]:
    """Extract links and headings from prose, ignoring fenced/code examples."""
    links: list[Link] = []
    definitions: dict[str, Link] = {}
    findings: list[Finding] = []
    headings: list[str] = []
    reference_uses: list[tuple[int, str]] = []
    fence_char = ""
    fence_length = 0
    for lineno, raw in enumerate(text.splitlines(), 1):
        fence = _FENCE_RE.match(raw)
        if fence:
            marker = fence.group(1)
            if not fence_char:
                fence_char, fence_length = marker[0], len(marker)
            elif marker[0] == fence_char and len(marker) >= fence_length:
                fence_char, fence_length = "", 0
            continue
        if fence_char:
            continue
        line, unmatched = _mask_code(raw)
        if unmatched:
            findings.append(Finding(source, lineno, "MALFORMED_CODE_SPAN", "", "unmatched backtick run"))
            continue
        heading = _HEADING_RE.match(line)
        if heading:
            headings.append(heading.group(2).strip())
        definition = _REFERENCE_RE.match(line)
        if definition:
            label = " ".join(definition.group(1).casefold().split())
            destination = definition.group(2).strip("<>")
            item = Link(source, lineno, destination)
            if label in definitions:
                findings.append(Finding(source, lineno, "DUPLICATE_REFERENCE", destination, f"duplicate label [{label}]"))
            else:
                definitions[label] = item
        for match in _INLINE_LINK_RE.finditer(line):
            links.append(Link(source, lineno, match.group(1).strip("<>")))
        for match in _REFERENCE_USE_RE.finditer(line):
            label = match.group(2) or match.group(1)
            key = " ".join(label.casefold().split())
            reference_uses.append((lineno, key))
    if fence_char:
        findings.append(Finding(source, len(text.splitlines()) or 1, "MALFORMED_FENCE", "", "unclosed fenced code block"))
    for lineno, key in reference_uses:
        if key not in definitions:
            findings.append(Finding(source, lineno, "MISSING_REFERENCE", key, "reference label has no definition"))
    return links, definitions, findings, headings


def github_slugs(headings: list[str]) -> set[str]:
    """Return GitHub-style heading identifiers, including duplicate suffixes."""
    slugs: set[str] = set()
    counts: dict[str, int] = {}
    for heading in headings:
        plain = re.sub(r"<[^>]*>", "", heading)
        plain = re.sub(r"[*_~`]", "", plain).strip().lower()
        base = re.sub(r"[^\w\- ]", "", plain, flags=re.UNICODE).replace(" ", "-")
        count = counts.get(base, 0)
        slug = base if count == 0 else f"{base}-{count}"
        counts[base] = count + 1
        slugs.add(slug)
    return slugs


def _external(destination: str) -> bool:
    """Return whether a destination is outside repository-path resolution."""
    return bool(_SCHEME_RE.match(destination)) or destination.startswith("//")


def _resolve(source: str, destination: str) -> tuple[str, str]:
    """Return normalized repo-relative path and decoded fragment."""
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


def check(root: Path = REPO_ROOT) -> tuple[list[Finding], list[str], list[Link]]:
    """Check the complete tracked Markdown graph."""
    names, findings = tracked_markdown(root)
    if findings:
        return findings, [], []
    tracked_proc = subprocess.run(["git", "ls-files", "-z"], cwd=root, capture_output=True, check=False)
    if tracked_proc.returncode != 0:
        return [Finding("<git>", 0, "TRACKED_SET", "", "could not list all tracked targets")], [], []
    tracked = {name for name in tracked_proc.stdout.decode("utf-8").split("\0") if name}
    all_links: list[Link] = []
    headings_by_source: dict[str, set[str]] = {}
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
        links, definitions, parse_findings, headings = parse_markdown(name, text)
        findings.extend(parse_findings)
        all_links.extend(links)
        all_links.extend(definitions.values())
        headings_by_source[name] = github_slugs(headings)
    edges: set[tuple[str, str]] = set()
    for link in all_links:
        destination = link.destination
        if not destination or _external(destination):
            continue
        if destination.startswith("#"):
            target, fragment = link.source, urllib.parse.unquote(destination[1:])
        else:
            target, fragment = _resolve(link.source, destination)
        if not target:
            findings.append(Finding(link.source, link.line, "PATH_ESCAPE", destination, "target escapes repository"))
            continue
        path_part = urllib.parse.urlsplit(destination).path.lower()
        if path_part.endswith(".html"):
            findings.append(Finding(link.source, link.line, "LOCAL_HTML", destination, "link must name tracked source, not Jekyll output"))
            continue
        if target not in tracked:
            findings.append(Finding(link.source, link.line, "MISSING_TARGET", destination, f"case-sensitive tracked target `{target}` does not exist"))
            continue
        if not (root / target).is_file() or (root / target).is_symlink():
            findings.append(Finding(link.source, link.line, "NONREGULAR_TARGET", destination, f"`{target}` is not a regular file"))
            continue
        edges.add((link.source, target))
        if fragment:
            if target not in headings_by_source and target.endswith(".md"):
                try:
                    parsed = parse_markdown(target, (root / target).read_text(encoding="utf-8"))
                    headings_by_source[target] = github_slugs(parsed[3])
                except (OSError, UnicodeError) as exc:
                    findings.append(Finding(link.source, link.line, "UNREADABLE_TARGET", destination, str(exc)))
                    continue
            if fragment not in headings_by_source.get(target, set()):
                findings.append(Finding(link.source, link.line, "MISSING_FRAGMENT", destination, f"fragment not found in `{target}`"))
    if ("README.md", LANDING) not in edges:
        findings.append(Finding("README.md", 0, "README_REACHABILITY", LANDING, "README must link directly to the documentation landing"))
    reached = {target for source, target in edges if source == LANDING}
    for owner in sorted(CANONICAL_OWNERS - reached):
        findings.append(Finding(LANDING, 0, "OWNER_REACHABILITY", owner, "landing must link directly to canonical owner"))
    return sorted(set(findings)), visited, all_links


def main() -> int:
    """Run the checker or its test suite."""
    parser = argparse.ArgumentParser(description="Check tracked Markdown links")
    parser.add_argument("--check", action="store_true", help="check the tracked tree (default)")
    parser.add_argument("--self-test", action="store_true", help="run scripts/test_docs_link_check.py")
    args = parser.parse_args()
    if args.self_test:
        from test_docs_link_check import run_suite  # noqa: PLC0415
        return run_suite()
    findings, visited, links = check()
    if findings:
        for finding in findings:
            print(finding.render())
        print(f"documentation links: FAIL ({len(findings)} findings; {len(visited)} files read)")
        return 1
    local = sum(1 for link in links if link.destination and not _external(link.destination))
    print(f"documentation links: PASS ({len(visited)} tracked Markdown files; {local} local links)")
    return 0


if __name__ == "__main__":
    sys.exit(main())

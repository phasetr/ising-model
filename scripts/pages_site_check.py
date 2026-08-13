#!/usr/bin/env python3
"""Prepare and fail-closed check the derived handwritten Pages snapshot."""

from __future__ import annotations

import argparse
import datetime as dt
import html
import hashlib
import json
import os
import posixpath
import re
import shutil
import sys
import tempfile
import time
import urllib.error
import urllib.parse
import urllib.request
from dataclasses import dataclass
from html.parser import HTMLParser
from pathlib import Path, PurePosixPath

MANIFEST_NAME = "pages-manifest.json"
PROVENANCE_ID = "snapshot-provenance"
ACTION_SHAS = (
    "9ca7ed09e240259871327bfc3a3a8d8c4bcb41aa",  # lean-release-tag v1
    "fbc6f3992d24b796d5a048ff273f7fcc4a7b6c09",  # checkout v5.1.0
    "983d7736d9b0ae728b81ab479565c72886d7745b",  # configure-pages v5
    "44a6e6beabd48582f863aeeb6cb2151cc1716697",  # jekyll-build-pages v1.0.13
    "56afc609e74202658d3ffba0e8f6dda462b719fa",  # upload-pages-artifact v3
    "d6db90164ac5ed86f2b6aed7e0febac5b3c0c03e",  # deploy-pages v4
)
REVISION_RE = re.compile(r"[0-9a-f]{40}\Z")


@dataclass(frozen=True, order=True)
class Finding:
    path: str
    code: str
    detail: str

    def render(self) -> str:
        return f"pages: {self.path}: {self.code}: {self.detail}"


@dataclass
class Page:
    anchors: set[str]
    links: list[tuple[str, str]]


class PageParser(HTMLParser):
    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self.anchors: list[str] = []
        self.links: list[tuple[str, str]] = []

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        values = dict(attrs)
        for key in ("id", "name"):
            if values.get(key):
                self.anchors.append(values[key] or "")
        if tag in ("a", "link") and values.get("href") is not None:
            self.links.append(("href", values.get("href") or ""))
        if tag in ("img", "script", "source") and values.get("src") is not None:
            self.links.append(("src", values.get("src") or ""))


def _valid_generated_at(value: str) -> bool:
    if not value.endswith("Z"):
        return False
    try:
        parsed = dt.datetime.fromisoformat(value[:-1] + "+00:00")
    except ValueError:
        return False
    return parsed.tzinfo is not None


def _expected_pages(source: Path) -> tuple[list[str], list[Finding]]:
    findings: list[Finding] = []
    if not source.is_dir() or source.is_symlink():
        return [], [Finding(str(source), "SOURCE", "source is not a regular directory")]
    pages: list[str] = []
    for path in sorted(source.rglob("*.md")):
        if path.is_symlink() or not path.is_file():
            findings.append(Finding(path.as_posix(), "NONREGULAR", "Markdown source is not a regular file"))
            continue
        pages.append(path.relative_to(source).with_suffix(".html").as_posix())
    if not pages:
        findings.append(Finding(str(source), "EMPTY_SOURCE", "no Markdown source pages found"))
    return pages, findings


def _artifact_inventory(site: Path) -> list[dict[str, object]]:
    inventory: list[dict[str, object]] = []
    for path in sorted(site.rglob("*")):
        if not path.is_file() or path.is_symlink() or path.name == MANIFEST_NAME:
            continue
        body = path.read_bytes()
        inventory.append({
            "path": path.relative_to(site).as_posix(),
            "size": len(body),
            "sha256": hashlib.sha256(body).hexdigest(),
        })
    return inventory


def _expected_manifest(site: Path, pages: list[str], baseurl: str, revision: str, generated_at: str) -> dict[str, object]:
    return {
        "format": 1,
        "kind": "handwritten-only",
        "baseurl": baseurl,
        "source_revision": revision,
        "generated_at": generated_at,
        "pages": pages,
        "files": _artifact_inventory(site),
    }


def _read_page(path: Path, relative: str) -> tuple[Page | None, list[Finding]]:
    if path.is_symlink() or not path.is_file():
        return None, [Finding(relative, "NONREGULAR", "rendered page is not a regular file")]
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as exc:
        return None, [Finding(relative, "UNREADABLE", str(exc))]
    parser = PageParser()
    try:
        parser.feed(text)
        parser.close()
    except Exception as exc:  # HTMLParser errors are rare; fail closed if one occurs.
        return None, [Finding(relative, "MALFORMED_HTML", str(exc))]
    duplicates = sorted({anchor for anchor in parser.anchors if parser.anchors.count(anchor) > 1})
    findings = [Finding(relative, "DUPLICATE_ANCHOR", anchor) for anchor in duplicates]
    return Page(set(parser.anchors), parser.links), findings


def _local_target(owner: str, raw: str, baseurl: str) -> tuple[str | None, str, str | None]:
    parsed = urllib.parse.urlsplit(html.unescape(raw))
    if parsed.scheme or parsed.netloc or raw.startswith("//"):
        return None, "", None
    path = urllib.parse.unquote(parsed.path)
    if "\\" in path:
        return "", parsed.fragment, "BACKSLASH"
    if path.startswith("/") and not path.startswith(baseurl + "/"):
        return "", parsed.fragment, "BASEURL_ESCAPE"
    if path == baseurl or path == baseurl + "/":
        target = "index.html"
    elif path.startswith(baseurl + "/"):
        target = path[len(baseurl) + 1:]
    elif not path:
        target = owner
    else:
        target = posixpath.normpath(posixpath.join(posixpath.dirname(owner), path))
    if target.startswith("../") or target == ".." or target.startswith("/"):
        return "", parsed.fragment, "PATH_ESCAPE"
    if target.endswith("/"):
        target += "index.html"
    return target, urllib.parse.unquote(parsed.fragment), None


def check_site(site: Path, source: Path, baseurl: str, revision: str, generated_at: str) -> list[Finding]:
    site, source = site.resolve(), source.resolve()
    findings: list[Finding] = []
    if not REVISION_RE.fullmatch(revision):
        findings.append(Finding("<metadata>", "REVISION", "revision must be 40 lowercase hexadecimal characters"))
    if not _valid_generated_at(generated_at):
        findings.append(Finding("<metadata>", "GENERATED_AT", "timestamp must be an ISO-8601 UTC value"))
    if not baseurl.startswith("/") or baseurl.endswith("/") or baseurl == "/":
        findings.append(Finding("<metadata>", "BASEURL", "baseurl must be a non-root absolute path without trailing slash"))
    expected_pages, source_findings = _expected_pages(source)
    findings.extend(source_findings)
    if not site.is_dir() or site.is_symlink():
        return sorted(findings + [Finding(str(site), "SITE", "site is not a regular directory")])
    actual_files: set[str] = set()
    actual_pages: list[str] = []
    for path in sorted(site.rglob("*")):
        relative = PurePosixPath(path.relative_to(site).as_posix())
        if path.is_symlink():
            findings.append(Finding(relative.as_posix(), "NONREGULAR", "artifact contains a symlink"))
            continue
        if path.is_file():
            actual_files.add(relative.as_posix())
            if relative.suffix.lower() == ".html":
                actual_pages.append(relative.as_posix())
            if relative.parts[:1] == ("docs",):
                findings.append(Finding(relative.as_posix(), "API_CONTENT", "handwritten artifact contains reserved API output"))
    actual_pages.sort()
    if actual_pages != expected_pages:
        findings.append(Finding("<site>", "PAGE_SET", f"expected {expected_pages!r}, got {actual_pages!r}"))
    try:
        expected_manifest = _expected_manifest(site, expected_pages, baseurl, revision, generated_at)
    except OSError as exc:
        findings.append(Finding(MANIFEST_NAME, "MANIFEST", f"could not inventory artifact: {exc}"))
        expected_manifest = None
    manifest_path = site / MANIFEST_NAME
    try:
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        findings.append(Finding(MANIFEST_NAME, "MANIFEST", str(exc)))
        manifest = None
    if manifest != expected_manifest:
        findings.append(Finding(MANIFEST_NAME, "MANIFEST", "manifest does not match checked source metadata and page set"))
    parsed_pages: dict[str, Page] = {}
    for relative in expected_pages:
        page, page_findings = _read_page(site / relative, relative)
        findings.extend(page_findings)
        if page is not None:
            parsed_pages[relative] = page
    for owner, page in parsed_pages.items():
        for attribute, raw in page.links:
            if not raw:
                findings.append(Finding(owner, "EMPTY_LINK", f"empty {attribute}"))
                continue
            target, fragment, error = _local_target(owner, raw, baseurl)
            if target is None:
                continue
            if error:
                findings.append(Finding(owner, error, raw))
                continue
            assert target is not None
            if target.lower().endswith(".md"):
                findings.append(Finding(owner, "RESIDUAL_MARKDOWN", raw))
            if target not in actual_files:
                findings.append(Finding(owner, "MISSING_TARGET", raw))
                continue
            if fragment:
                target_page = parsed_pages.get(target)
                if target_page is None or fragment not in target_page.anchors:
                    findings.append(Finding(owner, "MISSING_FRAGMENT", raw))
    root_path = site / "index.html"
    try:
        root_text = root_path.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as exc:
        findings.append(Finding("index.html", "PROVENANCE", str(exc)))
    else:
        if root_text.count(f'id="{PROVENANCE_ID}"') != 1 or revision not in root_text or generated_at not in root_text:
            findings.append(Finding("index.html", "PROVENANCE", "root does not visibly own exact revision and generation time"))
    return sorted(set(findings))


def prepare_site(site: Path, source: Path, baseurl: str, revision: str, generated_at: str) -> list[Finding]:
    preliminary: list[Finding] = []
    if not REVISION_RE.fullmatch(revision):
        preliminary.append(Finding("<metadata>", "REVISION", "revision must be 40 lowercase hexadecimal characters"))
    if not _valid_generated_at(generated_at):
        preliminary.append(Finding("<metadata>", "GENERATED_AT", "timestamp must be an ISO-8601 UTC value"))
    pages, source_findings = _expected_pages(source.resolve())
    preliminary.extend(source_findings)
    root = site.resolve() / "index.html"
    try:
        text = root.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as exc:
        preliminary.append(Finding("index.html", "PROVENANCE", str(exc)))
        return sorted(preliminary)
    if f'id="{PROVENANCE_ID}"' in text:
        preliminary.append(Finding("index.html", "PROVENANCE", "snapshot marker already exists"))
    if "</body>" not in text:
        preliminary.append(Finding("index.html", "PROVENANCE", "root has no closing body tag"))
    if preliminary:
        return sorted(preliminary)
    provenance = (
        f'<aside id="{PROVENANCE_ID}" data-source-revision="{revision}" '
        f'data-generated-at="{generated_at}">Derived snapshot from '
        f'<a href="https://github.com/phasetr/ising-model/commit/{revision}"><code>{revision}</code></a>, '
        f'generated <time datetime="{generated_at}">{generated_at}</time>.</aside>'
    )
    root.write_text(text.replace("</body>", provenance + "</body>", 1), encoding="utf-8")
    manifest = _expected_manifest(site.resolve(), pages, baseurl, revision, generated_at)
    (site.resolve() / MANIFEST_NAME).write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return check_site(site, source, baseurl, revision, generated_at)


def _fetch(url: str, retries: int = 3) -> tuple[bytes | None, str | None]:
    last = ""
    for attempt in range(retries):
        try:
            request = urllib.request.Request(url, headers={"User-Agent": "ising-model-pages-check/1"})
            with urllib.request.urlopen(request, timeout=20) as response:
                if response.status != 200:
                    raise urllib.error.HTTPError(url, response.status, "unexpected status", response.headers, None)
                if response.geturl() != url:
                    return None, f"redirected to {response.geturl()}"
                return response.read(), None
        except (OSError, urllib.error.URLError) as exc:
            last = str(exc)
            if attempt + 1 < retries:
                time.sleep(2 ** attempt)
    return None, last


def check_live(url: str, source: Path, baseurl: str, revision: str, generated_at: str) -> list[Finding]:
    if not url.startswith("https://") or not url.rstrip("/").endswith(baseurl):
        return [Finding(url, "LIVE_URL", "live URL must be HTTPS and end in the configured baseurl")]
    base = url.rstrip("/") + "/"
    with tempfile.TemporaryDirectory(prefix="pages-live-") as raw:
        site = Path(raw)
        manifest_bytes, error = _fetch(urllib.parse.urljoin(base, MANIFEST_NAME))
        if manifest_bytes is None:
            return [Finding(MANIFEST_NAME, "LIVE_FETCH", error or "fetch failed")]
        try:
            manifest = json.loads(manifest_bytes.decode("utf-8"))
            files = manifest["files"]
        except (UnicodeError, json.JSONDecodeError, KeyError, TypeError) as exc:
            return [Finding(MANIFEST_NAME, "MANIFEST", str(exc))]
        if not isinstance(files, list):
            return [Finding(MANIFEST_NAME, "MANIFEST", "files must be a list")]
        paths: list[str] = []
        for item in files:
            if not isinstance(item, dict) or not isinstance(item.get("path"), str):
                return [Finding(MANIFEST_NAME, "MANIFEST", "every file entry must have a string path")]
            relative = item["path"]
            parts = PurePosixPath(relative).parts
            if not relative or relative.startswith("/") or "\\" in relative or any(part in ("", ".", "..") for part in parts):
                return [Finding(MANIFEST_NAME, "MANIFEST", f"unsafe artifact path: {relative!r}")]
            paths.append(relative)
        if len(paths) != len(set(paths)):
            return [Finding(MANIFEST_NAME, "MANIFEST", "file paths must be unique")]
        (site / MANIFEST_NAME).write_bytes(manifest_bytes)
        findings: list[Finding] = []
        for relative in paths:
            body, fetch_error = _fetch(urllib.parse.urljoin(base, relative))
            if body is None:
                findings.append(Finding(relative, "LIVE_FETCH", fetch_error or "fetch failed"))
                continue
            path = site / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(body)
        findings.extend(check_site(site, source, baseurl, revision, generated_at))
        return sorted(set(findings))


def _print(findings: list[Finding], label: str) -> int:
    for finding in findings:
        print(finding.render())
    if findings:
        print(f"handwritten Pages {label}: FAIL ({len(findings)} findings)")
        return 1
    print(f"handwritten Pages {label}: PASS")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    for command in ("prepare", "check"):
        sub = subparsers.add_parser(command)
        sub.add_argument("--site", type=Path, required=True)
        sub.add_argument("--source", type=Path, default=Path("docs"))
        sub.add_argument("--baseurl", default="/ising-model")
        sub.add_argument("--revision", required=True)
        sub.add_argument("--generated-at", required=True)
    live = subparsers.add_parser("live")
    live.add_argument("--url", required=True)
    live.add_argument("--source", type=Path, default=Path("docs"))
    live.add_argument("--baseurl", default="/ising-model")
    live.add_argument("--revision", required=True)
    live.add_argument("--generated-at", required=True)
    subparsers.add_parser("self-test")
    args = parser.parse_args()
    if args.command == "self-test":
        from test_pages_site_check import run_suite  # noqa: PLC0415
        return run_suite()
    if args.command == "prepare":
        return _print(prepare_site(args.site, args.source, args.baseurl, args.revision, args.generated_at), "artifact")
    if args.command == "check":
        return _print(check_site(args.site, args.source, args.baseurl, args.revision, args.generated_at), "artifact")
    return _print(check_live(args.url, args.source, args.baseurl, args.revision, args.generated_at), "live")


if __name__ == "__main__":
    sys.exit(main())

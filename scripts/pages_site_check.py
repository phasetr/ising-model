#!/usr/bin/env python3
"""Prepare and fail-closed check the derived handwritten Pages snapshot."""

from __future__ import annotations

import argparse
from collections import Counter
import datetime as dt
import html
import hashlib
import json
import os
import posixpath
import re
import shutil
import stat
import subprocess
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
_LAST_STATS = (0, 0, 0)


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


@dataclass(frozen=True)
class StageInventory:
    directories: tuple[str, ...]
    files: tuple[tuple[str, int, str], ...]


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


def _tracked_source_names(source: Path) -> tuple[list[str], list[Finding]]:
    try:
        proc = subprocess.run(
            ["git", "ls-files", "-z", "--", source.name], cwd=source.parent,
            capture_output=True, check=False,
        )
    except OSError as exc:
        return [], [Finding(str(source), "TRACKED_SET", str(exc))]
    if proc.returncode != 0:
        return [], [Finding(str(source), "TRACKED_SET", proc.stderr.decode("utf-8", errors="replace").strip())]
    try:
        names = [item for item in proc.stdout.decode("utf-8").split("\0") if item]
    except UnicodeDecodeError as exc:
        return [], [Finding(str(source), "TRACKED_SET", f"non-UTF-8 path: {exc}")]
    prefix = source.name + "/"
    relative = sorted(name[len(prefix):] for name in names if name.startswith(prefix))
    if not relative:
        return [], [Finding(str(source), "EMPTY_SOURCE", "no tracked source files found")]
    return relative, []


def _expected_pages(source: Path) -> tuple[list[str], list[Finding]]:
    findings: list[Finding] = []
    if not source.is_dir() or source.is_symlink():
        return [], [Finding(str(source), "SOURCE", "source is not a regular directory")]
    names, tracked_findings = _tracked_source_names(source)
    findings.extend(tracked_findings)
    pages: list[str] = []
    for name in names:
        if not name.endswith(".md"):
            continue
        path = source / name
        if path.is_symlink() or not path.is_file():
            findings.append(Finding(path.as_posix(), "NONREGULAR", "Markdown source is not a regular file"))
            continue
        pages.append(PurePosixPath(name).with_suffix(".html").as_posix())
    if not pages:
        findings.append(Finding(str(source), "EMPTY_SOURCE", "no Markdown source pages found"))
    return pages, findings


def check_source(source: Path) -> list[Finding]:
    """Reject raw Liquid openers in the tracked Jekyll source before rendering."""
    global _LAST_STATS
    _LAST_STATS = (0, 0, 0)
    source = source if source.is_absolute() else Path.cwd() / source
    if not source.is_dir() or source.is_symlink():
        return [Finding(str(source), "SOURCE", "source is not a regular directory")]
    names, findings = _tracked_source_names(source)
    markdown_names = [name for name in names if name.endswith(".md")]
    if not markdown_names and not findings:
        findings.append(Finding(str(source), "EMPTY_SOURCE", "no Markdown source pages found"))
    _LAST_STATS = (len(markdown_names), 0, len(names))
    for name in markdown_names:
        path = source / name
        if path.is_symlink() or not path.is_file():
            findings.append(Finding(path.as_posix(), "NONREGULAR", "Markdown source is not a regular file"))
            continue
        try:
            text = path.read_text(encoding="utf-8")
        except (OSError, UnicodeError) as exc:
            findings.append(Finding(name, "SOURCE", str(exc)))
            continue
        for lineno, line in enumerate(text.splitlines(), 1):
            for token in ("{{", "{%"):
                if token in line:
                    findings.append(Finding(name, "LIQUID_DELIMITER", f"line {lineno}: raw {token!r} is unsafe before Markdown rendering"))
    return sorted(set(findings))


def _stage_error(exc: OSError) -> str:
    if exc.strerror:
        return exc.strerror
    if exc.args:
        return str(exc.args[0])
    return exc.__class__.__name__


def _read_stage_file(path: Path, expected: os.stat_result) -> tuple[int, str]:
    flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0)
    descriptor = os.open(path, flags)
    with os.fdopen(descriptor, "rb") as handle:
        actual = os.fstat(handle.fileno())
        if (
            not stat.S_ISREG(actual.st_mode)
            or (actual.st_dev, actual.st_ino) != (expected.st_dev, expected.st_ino)
        ):
            raise OSError("entry changed while staging")
        digest = hashlib.sha256()
        size = 0
        while chunk := handle.read(1024 * 1024):
            digest.update(chunk)
            size += len(chunk)
    return size, digest.hexdigest()


def _stage_inventory(root: Path, logical_root: str) -> tuple[StageInventory, list[Finding]]:
    directories: list[str] = []
    files: list[tuple[str, int, str]] = []
    findings: list[Finding] = []

    def visit(directory: Path, prefix: PurePosixPath, expected: os.stat_result | None = None) -> None:
        descriptor: int | None = None
        try:
            flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0) | getattr(os, "O_NOFOLLOW", 0)
            descriptor = os.open(directory, flags)
            actual = os.fstat(descriptor)
            if not stat.S_ISDIR(actual.st_mode) or (
                expected is not None and (actual.st_dev, actual.st_ino) != (expected.st_dev, expected.st_ino)
            ):
                raise OSError("directory changed while staging")
            with os.scandir(descriptor) as iterator:
                entries = sorted(iterator, key=lambda item: item.name)
        except OSError as exc:
            relative = prefix.as_posix() if prefix.parts else logical_root
            findings.append(Finding(relative, "STAGE_READ", _stage_error(exc)))
            return
        try:
            for entry in entries:
                relative_path = prefix / entry.name
                relative = relative_path.as_posix()
                try:
                    metadata = entry.stat(follow_symlinks=False)
                except OSError as exc:
                    findings.append(Finding(relative, "STAGE_STAT", _stage_error(exc)))
                    continue
                if stat.S_ISDIR(metadata.st_mode):
                    directories.append(relative)
                    visit(directory / entry.name, relative_path, metadata)
                elif stat.S_ISREG(metadata.st_mode):
                    try:
                        size, digest = _read_stage_file(directory / entry.name, metadata)
                    except OSError as exc:
                        findings.append(Finding(relative, "STAGE_READ", _stage_error(exc)))
                    else:
                        files.append((relative, size, digest))
                else:
                    findings.append(Finding(relative, "NONREGULAR", "rendered input contains a non-regular entry"))
        finally:
            assert descriptor is not None
            os.close(descriptor)

    try:
        root_metadata = root.lstat()
    except OSError as exc:
        findings.append(Finding(logical_root, "STAGE_STAT", _stage_error(exc)))
    else:
        visit(root, PurePosixPath(), root_metadata)
    return StageInventory(tuple(sorted(directories)), tuple(sorted(files))), findings


def _stage_paths_overlap(first: Path, second: Path) -> bool:
    try:
        common = Path(os.path.commonpath((str(first), str(second))))
    except ValueError:
        return True
    return common == first or common == second


def _copy_stage_file(source: Path, destination: Path, expected: tuple[int, str]) -> None:
    metadata = source.lstat()
    if not stat.S_ISREG(metadata.st_mode):
        raise OSError("entry changed while staging")
    flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0)
    descriptor = os.open(source, flags)
    digest = hashlib.sha256()
    size = 0
    with os.fdopen(descriptor, "rb") as input_handle, destination.open("xb") as output_handle:
        actual = os.fstat(input_handle.fileno())
        if (
            not stat.S_ISREG(actual.st_mode)
            or (actual.st_dev, actual.st_ino) != (metadata.st_dev, metadata.st_ino)
        ):
            raise OSError("entry changed while staging")
        while chunk := input_handle.read(1024 * 1024):
            output_handle.write(chunk)
            digest.update(chunk)
            size += len(chunk)
    if (size, digest.hexdigest()) != expected:
        raise OSError("entry changed while staging")


def stage_site(input_site: Path, site: Path) -> list[Finding]:
    """Publish a verified runner-owned byte copy of container-rendered output."""
    global _LAST_STATS
    _LAST_STATS = (0, 0, 0)
    source = Path(os.path.abspath(input_site))
    destination = Path(os.path.abspath(site))
    findings: list[Finding] = []
    try:
        source_metadata = source.lstat()
    except OSError as exc:
        return [Finding(str(input_site), "STAGE_INPUT", _stage_error(exc))]
    if not stat.S_ISDIR(source_metadata.st_mode):
        return [Finding(str(input_site), "STAGE_INPUT", "rendered input is not a real directory")]
    if _stage_paths_overlap(source, destination):
        return [Finding(str(site), "STAGE_OVERLAP", "input and destination paths overlap")]
    try:
        destination.lstat()
    except FileNotFoundError:
        pass
    except OSError as exc:
        return [Finding(str(site), "STAGE_DESTINATION", _stage_error(exc))]
    else:
        return [Finding(str(site), "STAGE_DESTINATION", "destination already exists")]
    parent = destination.parent
    try:
        parent_metadata = parent.lstat()
    except OSError as exc:
        return [Finding(str(site), "STAGE_DESTINATION", _stage_error(exc))]
    if not stat.S_ISDIR(parent_metadata.st_mode):
        return [Finding(str(site), "STAGE_DESTINATION", "destination parent is not a real directory")]
    temporary_prefix = f".{destination.name}.stage-"
    try:
        with os.scandir(parent) as iterator:
            stale = sorted(entry.name for entry in iterator if entry.name.startswith(temporary_prefix))
    except OSError as exc:
        return [Finding(str(site), "STAGE_DESTINATION", _stage_error(exc))]
    if stale:
        return [Finding(str(site), "STAGE_TEMP", "stale staging path exists")]

    frozen, inventory_findings = _stage_inventory(source, str(input_site))
    findings.extend(inventory_findings)
    if not frozen.files:
        findings.append(Finding(str(input_site), "EMPTY_SITE", "rendered input has no regular files"))
    if not any(relative == "index.html" for relative, _size, _digest in frozen.files):
        findings.append(Finding("index.html", "STAGE_INDEX", "rendered input has no regular index.html"))
    if findings:
        return sorted(set(findings))

    temporary: Path | None = None
    published = False
    try:
        temporary = Path(tempfile.mkdtemp(prefix=temporary_prefix, dir=parent))
        for relative in frozen.directories:
            source_directory = source / relative
            metadata = source_directory.lstat()
            if not stat.S_ISDIR(metadata.st_mode):
                raise OSError("directory changed while staging")
            (temporary / relative).mkdir()
        for relative, size, digest in frozen.files:
            _copy_stage_file(source / relative, temporary / relative, (size, digest))
        current, current_findings = _stage_inventory(source, str(input_site))
        staged, staged_findings = _stage_inventory(temporary, str(site))
        findings.extend(current_findings)
        findings.extend(staged_findings)
        if current != frozen:
            findings.append(Finding(str(input_site), "STAGE_CHANGED", "rendered input changed while staging"))
        if staged != frozen:
            findings.append(Finding(str(site), "STAGE_INVENTORY", "staged paths or byte digests differ from rendered input"))
        try:
            with (temporary / "index.html").open("r+b"):
                pass
        except OSError as exc:
            findings.append(Finding("index.html", "STAGE_WRITABLE", _stage_error(exc)))
        if not findings:
            try:
                destination.lstat()
            except FileNotFoundError:
                pass
            except OSError as exc:
                findings.append(Finding(str(site), "STAGE_DESTINATION", _stage_error(exc)))
            else:
                findings.append(Finding(str(site), "STAGE_DESTINATION", "destination appeared while staging"))
        if not findings:
            try:
                os.rename(temporary, destination)
            except OSError as exc:
                findings.append(Finding(str(site), "STAGE_RENAME", _stage_error(exc)))
            else:
                published = True
                _LAST_STATS = (0, len(frozen.directories), len(frozen.files))
    except OSError as exc:
        findings.append(Finding(str(site), "STAGE_COPY", _stage_error(exc)))
    finally:
        if temporary is not None and not published:
            try:
                shutil.rmtree(temporary)
            except OSError as exc:
                findings.append(Finding(str(site), "STAGE_CLEANUP", _stage_error(exc)))
    return sorted(set(findings))


def _expected_source_edges(source: Path) -> tuple[list[dict[str, str]], list[Finding]]:
    """Delegate authored syntax to V5 and map its local docs edges to Jekyll output."""
    import docs_link_check as authored  # The sole authored-source detector.

    names, findings = _tracked_source_names(source)
    tracked = set(names)
    edges: list[dict[str, str]] = []
    for name in names:
        if not name.endswith(".md"):
            continue
        path = source / name
        try:
            parsed = authored.parse_markdown(f"docs/{name}", path.read_text(encoding="utf-8"))
        except (OSError, UnicodeError) as exc:
            findings.append(Finding(name, "SOURCE_EDGE", str(exc)))
            continue
        if parsed.findings:
            findings.append(Finding(name, "SOURCE_EDGE", "V5 found unsupported source syntax"))
            continue
        owner = PurePosixPath(name).with_suffix(".html").as_posix()
        for link in parsed.links:
            raw = link.destination
            if not raw or authored._external(raw):
                continue
            target, fragment = authored._resolve(f"docs/{name}", raw)
            if not target.startswith("docs/"):
                continue
            relative = target[len("docs/"):]
            if relative not in tracked:
                findings.append(Finding(name, "SOURCE_EDGE", f"untracked target: {raw}"))
                continue
            rendered = PurePosixPath(relative).with_suffix(".html").as_posix() if relative.endswith(".md") else relative
            edges.append({
                "owner": owner,
                "kind": "src" if link.image else "href",
                "target": rendered,
                "fragment": fragment,
            })
    if not edges:
        findings.append(Finding(str(source), "EMPTY_EDGES", "no tracked local Markdown edges found"))
    return sorted(edges, key=lambda item: (item["owner"], item["kind"], item["target"], item["fragment"])), findings


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


def _expected_manifest(
    site: Path, pages: list[str], source_edges: list[dict[str, str]],
    baseurl: str, revision: str, generated_at: str,
) -> dict[str, object]:
    return {
        "format": 1,
        "kind": "handwritten-only",
        "baseurl": baseurl,
        "source_revision": revision,
        "generated_at": generated_at,
        "pages": pages,
        "source_edges": source_edges,
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
    global _LAST_STATS
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
    expected_edges, edge_findings = _expected_source_edges(source)
    findings.extend(edge_findings)
    if not site.is_dir() or site.is_symlink():
        return sorted(findings + [Finding(str(site), "SITE", "site is not a regular directory")])
    actual_files: set[str] = set()
    actual_pages: list[str] = []
    for path in sorted(site.rglob("*")):
        relative = PurePosixPath(path.relative_to(site).as_posix())
        if path.is_symlink():
            findings.append(Finding(relative.as_posix(), "NONREGULAR", "artifact contains a symlink"))
            continue
        if not path.is_file() and not path.is_dir():
            findings.append(Finding(relative.as_posix(), "NONREGULAR", "artifact entry is neither a regular file nor directory"))
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
        expected_manifest = _expected_manifest(site, expected_pages, expected_edges, baseurl, revision, generated_at)
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
    actual_edges: Counter[tuple[str, str, str, str]] = Counter()
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
            actual_edges[(owner, attribute, target, fragment)] += 1
            if target.lower().endswith(".md"):
                findings.append(Finding(owner, "RESIDUAL_MARKDOWN", raw))
            if target not in actual_files:
                findings.append(Finding(owner, "MISSING_TARGET", raw))
                continue
            if fragment:
                target_page = parsed_pages.get(target)
                if target_page is None or fragment not in target_page.anchors:
                    findings.append(Finding(owner, "MISSING_FRAGMENT", raw))
    expected_edge_counts = Counter(
        (item["owner"], item["kind"], item["target"], item["fragment"])
        for item in expected_edges
    )
    missing_edges = expected_edge_counts - actual_edges
    for (owner, kind, target, fragment), count in sorted(missing_edges.items()):
        suffix = f"#{fragment}" if fragment else ""
        findings.append(Finding(owner, "EDGE_LOSS", f"{target}{suffix}: missing {count} rendered {kind} edge(s)"))
    _LAST_STATS = (len(expected_pages), sum(actual_edges.values()), len(actual_files))
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
    source_edges, edge_findings = _expected_source_edges(source.resolve())
    preliminary.extend(edge_findings)
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
    manifest = _expected_manifest(site.resolve(), pages, source_edges, baseurl, revision, generated_at)
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


def _safe_manifest_path(relative: str, base: str) -> tuple[str | None, str | None]:
    parsed = urllib.parse.urlsplit(relative)
    decoded = urllib.parse.unquote(relative)
    if (
        not relative or parsed.scheme or parsed.netloc or parsed.query or parsed.fragment
        or ":" in relative or "\\" in decoded or decoded.startswith("/")
        or decoded != relative
        or any(part in ("", ".", "..") for part in PurePosixPath(decoded).parts)
    ):
        return None, f"unsafe artifact path: {relative!r}"
    target = urllib.parse.urljoin(base, relative)
    base_url, target_url = urllib.parse.urlsplit(base), urllib.parse.urlsplit(target)
    if (
        (target_url.scheme, target_url.netloc) != (base_url.scheme, base_url.netloc)
        or not target_url.path.startswith(base_url.path)
        or target_url.query or target_url.fragment
    ):
        return None, f"artifact URL escapes publication base: {relative!r}"
    return target, None


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
        fetch_urls: list[str] = []
        for item in files:
            if not isinstance(item, dict) or not isinstance(item.get("path"), str):
                return [Finding(MANIFEST_NAME, "MANIFEST", "every file entry must have a string path")]
            relative = item["path"]
            target_url, path_error = _safe_manifest_path(relative, base)
            if path_error:
                return [Finding(MANIFEST_NAME, "MANIFEST", path_error)]
            assert target_url is not None
            paths.append(relative)
            fetch_urls.append(target_url)
        if len(paths) != len(set(paths)):
            return [Finding(MANIFEST_NAME, "MANIFEST", "file paths must be unique")]
        (site / MANIFEST_NAME).write_bytes(manifest_bytes)
        findings: list[Finding] = []
        for relative, target_url in zip(paths, fetch_urls):
            body, fetch_error = _fetch(target_url)
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
    pages, edges, files = _LAST_STATS
    if label == "stage":
        print(f"handwritten Pages {label}: PASS ({edges} directories; {files} files copied)")
    else:
        print(f"handwritten Pages {label}: PASS ({pages} pages; {edges} local edges; {files} files visited)")
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
    source = subparsers.add_parser("source")
    source.add_argument("--source", type=Path, default=Path("docs"))
    stage = subparsers.add_parser("stage")
    stage.add_argument("--input-site", type=Path, required=True)
    stage.add_argument("--site", type=Path, required=True)
    subparsers.add_parser("self-test")
    args = parser.parse_args()
    if args.command == "self-test":
        from test_pages_site_check import run_suite  # noqa: PLC0415
        return run_suite()
    if args.command == "prepare":
        return _print(prepare_site(args.site, args.source, args.baseurl, args.revision, args.generated_at), "artifact")
    if args.command == "check":
        return _print(check_site(args.site, args.source, args.baseurl, args.revision, args.generated_at), "artifact")
    if args.command == "source":
        return _print(check_source(args.source), "source")
    if args.command == "stage":
        return _print(stage_site(args.input_site, args.site), "stage")
    return _print(check_live(args.url, args.source, args.baseurl, args.revision, args.generated_at), "live")


if __name__ == "__main__":
    sys.exit(main())

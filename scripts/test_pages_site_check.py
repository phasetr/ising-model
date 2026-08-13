#!/usr/bin/env python3
"""Hermetic tests for the derived handwritten-Pages verifier."""

from __future__ import annotations

import hashlib
import importlib.util
import http.server
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import threading
import types
import unittest
import urllib.parse
import uuid
from contextlib import contextmanager
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
import pages_site_check as checker  # noqa: E402

CHECKER_PATH = Path(checker.__file__).resolve()
REPO_ROOT = CHECKER_PATH.parent.parent


class SiteTest(unittest.TestCase):
    def setUp(self) -> None:
        self.raw = tempfile.mkdtemp(prefix="pages-site-")
        self.addCleanup(shutil.rmtree, self.raw, True)
        self.root = Path(self.raw)
        self.source = self.root / "docs"
        self.site = self.root / "_site"
        self.source.mkdir()
        (self.source / "nested").mkdir()
        (self.site / "nested").mkdir(parents=True)
        (self.source / "index.md").write_text(
            "# Home\n\n[status](nested/status.md#status)\n\n![asset](asset.png)\n", encoding="utf-8",
        )
        (self.source / "nested" / "status.md").write_text("# Status\n\n[home](../index.md#home)\n", encoding="utf-8")
        (self.source / "asset.png").write_bytes(b"png")
        (self.site / "asset.png").write_bytes(b"png")
        (self.site / "index.html").write_text(
            '<html><body><h1 id="home">Home</h1>'
            '<a href="nested/status.html#status">status</a>'
            '<img src="asset.png" alt="asset"></body></html>', encoding="utf-8",
        )
        (self.site / "nested" / "status.html").write_text(
            '<html><body><h1 id="status">Status</h1>'
            '<a href="../index.html#home">home</a></body></html>', encoding="utf-8",
        )
        self.revision = "a" * 40
        self.generated = "2026-08-13T12:34:56Z"
        subprocess.run(["git", "init", "-q"], cwd=self.root, check=True)
        subprocess.run(["git", "add", "--", "docs/index.md", "docs/nested/status.md", "docs/asset.png"], cwd=self.root, check=True)

    def prepare(self, module: types.ModuleType = checker) -> list[checker.Finding]:
        return module.prepare_site(self.site, self.source, "/ising-model", self.revision, self.generated)

    def check(self, module: types.ModuleType = checker) -> list[checker.Finding]:
        return module.check_site(self.site, self.source, "/ising-model", self.revision, self.generated)

    def codes(self, module: types.ModuleType = checker) -> list[str]:
        return [item.code for item in self.check(module)]

    def test_prepare_writes_exact_manifest_and_visible_metadata_then_passes(self) -> None:
        self.assertEqual(self.prepare(), [])
        self.assertEqual(self.check(), [])
        manifest = json.loads((self.site / checker.MANIFEST_NAME).read_text(encoding="utf-8"))
        self.assertEqual(manifest["source_revision"], self.revision)
        self.assertEqual(manifest["generated_at"], self.generated)
        self.assertEqual(manifest["baseurl"], "/ising-model")
        self.assertEqual(manifest["pages"], ["index.html", "nested/status.html"])
        self.assertEqual(len(manifest["source_edges"]), 3)
        self.assertEqual([item["path"] for item in manifest["files"]], ["asset.png", "index.html", "nested/status.html"])
        root = (self.site / "index.html").read_text(encoding="utf-8")
        self.assertEqual(root.count('id="snapshot-provenance"'), 1)
        self.assertIn(self.revision, root)
        self.assertIn(self.generated, root)

    def test_missing_wrong_case_fragment_image_and_residual_md_fail(self) -> None:
        self.assertEqual(self.prepare(), [])
        (self.site / "nested" / "status.html").unlink()
        (self.site / "Status.html").write_text('<h1 id="other">x</h1>', encoding="utf-8")
        (self.site / "asset.png").unlink()
        (self.site / "index.html").write_text(
            (self.site / "index.html").read_text(encoding="utf-8")
            .replace("nested/status.html#status", "Status.html#missing")
            .replace("asset.png", "missing.md"), encoding="utf-8",
        )
        codes = self.codes()
        self.assertIn("PAGE_SET", codes)
        self.assertIn("MISSING_FRAGMENT", codes)
        self.assertIn("RESIDUAL_MARKDOWN", codes)
        self.assertIn("MISSING_TARGET", codes)

    def test_manifest_metadata_extra_api_and_base_escape_fail(self) -> None:
        self.assertEqual(self.prepare(), [])
        manifest_path = self.site / checker.MANIFEST_NAME
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        manifest["source_revision"] = "b" * 40
        manifest_path.write_text(json.dumps(manifest), encoding="utf-8")
        (self.site / "docs" / "IsingModel").mkdir(parents=True)
        (self.site / "docs" / "IsingModel" / "Bad.html").write_text("bad", encoding="utf-8")
        (self.site / "index.html").write_text(
            (self.site / "index.html").read_text(encoding="utf-8")
            .replace("</body>", '<a href="/outside.html">escape</a></body>'), encoding="utf-8",
        )
        codes = self.codes()
        self.assertIn("MANIFEST", codes)
        self.assertIn("API_CONTENT", codes)
        self.assertIn("BASEURL_ESCAPE", codes)

    def test_non_utf8_symlink_empty_scope_and_duplicate_anchor_fail(self) -> None:
        self.assertEqual(self.prepare(), [])
        (self.site / "nested" / "status.html").write_bytes(b"\xff")
        self.assertIn("UNREADABLE", self.codes())
        (self.site / "nested" / "status.html").unlink()
        (self.site / "nested" / "status.html").symlink_to(self.site / "index.html")
        self.assertIn("NONREGULAR", self.codes())
        shutil.rmtree(self.source)
        self.source.mkdir()
        self.assertIn("EMPTY_SOURCE", self.codes())

    def test_prepare_refuses_bad_revision_time_and_existing_marker(self) -> None:
        self.assertIn("REVISION", [x.code for x in checker.prepare_site(self.site, self.source, "/ising-model", "short", self.generated)])
        self.assertIn("GENERATED_AT", [x.code for x in checker.prepare_site(self.site, self.source, "/ising-model", self.revision, "today")])
        (self.site / "index.html").write_text('<body><p id="snapshot-provenance">old</p></body>', encoding="utf-8")
        self.assertIn("PROVENANCE", [x.code for x in self.prepare()])

    def test_duplicate_anchor_and_artifact_tamper_fail(self) -> None:
        self.assertEqual(self.prepare(), [])
        status = self.site / "nested" / "status.html"
        status.write_text(status.read_text().replace("</body>", '<i id="status"></i></body>'), encoding="utf-8")
        codes = self.codes()
        self.assertIn("DUPLICATE_ANCHOR", codes)
        self.assertIn("MANIFEST", codes)

    def test_total_rendered_edge_loss_and_nonregular_output_fail(self) -> None:
        self.assertEqual(self.prepare(), [])
        root = self.site / "index.html"
        root.write_text(
            root.read_text(encoding="utf-8")
            .replace('<a href="nested/status.html#status">status</a>', "status")
            .replace('<img src="asset.png" alt="asset">', "asset"),
            encoding="utf-8",
        )
        status = self.site / "nested" / "status.html"
        status.write_text(status.read_text(encoding="utf-8").replace('<a href="../index.html#home">home</a>', "home"), encoding="utf-8")
        self.assertIn("EDGE_LOSS", self.codes())
        fifo = self.site / "nonregular"
        os.mkfifo(fifo)
        self.assertIn("NONREGULAR", self.codes())

    def test_tracked_discovery_ignores_untracked_markdown(self) -> None:
        self.assertEqual(self.prepare(), [])
        (self.source / "untracked.md").write_text("# Untracked\n", encoding="utf-8")
        (self.site / "untracked.html").write_text("<h1>untracked</h1>", encoding="utf-8")
        self.assertIn("PAGE_SET", self.codes())

    def test_source_preflight_rejects_liquid_openers_in_code_and_prose(self) -> None:
        index = self.source / "index.md"
        status = self.source / "nested" / "status.md"
        index.write_text(index.read_text() + "\n`σ^{{i}△{j}}`\n`${{ github.workflow_sha }}`\n", encoding="utf-8")
        status.write_text(status.read_text() + "\n{% raw %}\n", encoding="utf-8")
        findings = checker.check_source(self.source)
        self.assertEqual(
            [(item.path, item.code, item.detail) for item in findings],
            [
                ("index.md", "LIQUID_DELIMITER", "line 7: raw '{{' is unsafe before Markdown rendering"),
                ("index.md", "LIQUID_DELIMITER", "line 8: raw '{{' is unsafe before Markdown rendering"),
                ("nested/status.md", "LIQUID_DELIMITER", "line 5: raw '{%' is unsafe before Markdown rendering"),
            ],
        )
        index.write_text("# Safe\n\n`github.workflow_sha`, `σ^{ {i} △ {j} }`, and standalone `}}`\n", encoding="utf-8")
        status.write_text("# Status\n", encoding="utf-8")
        self.assertEqual(checker.check_source(self.source), [])

    def test_source_preflight_fails_closed_on_bad_tracked_markdown(self) -> None:
        status = self.source / "nested" / "status.md"
        with mock.patch.object(checker.subprocess, "run", side_effect=OSError("git unavailable")):
            self.assertIn("TRACKED_SET", [item.code for item in checker.check_source(self.source)])
        with mock.patch.object(checker.Path, "read_text", side_effect=OSError("unreadable source")):
            findings = checker.check_source(self.source)
        self.assertEqual(
            [(item.path, item.code, item.detail) for item in findings],
            [
                ("index.md", "SOURCE", "unreadable source"),
                ("nested/status.md", "SOURCE", "unreadable source"),
            ],
        )
        status.write_bytes(b"\xff")
        self.assertIn("SOURCE", [item.code for item in checker.check_source(self.source)])
        status.unlink()
        status.symlink_to(self.source / "index.md")
        self.assertIn("NONREGULAR", [item.code for item in checker.check_source(self.source)])
        status.unlink()
        subprocess.run(["git", "rm", "--cached", "-q", "--", "docs/index.md", "docs/nested/status.md"], cwd=self.root, check=True)
        self.assertIn("EMPTY_SOURCE", [item.code for item in checker.check_source(self.source)])

    def test_stage_recreates_read_only_rendered_bytes_as_writable(self) -> None:
        rendered = self.root / "_site-container"
        staged = self.root / "_site-staged"
        shutil.copytree(self.site, rendered)
        for path in rendered.rglob("*"):
            path.chmod(0o555 if path.is_dir() else 0o444)
        rendered.chmod(0o555)
        def snapshot(root: Path):
            return {
                path.relative_to(root).as_posix(): (
                    "directory" if path.is_dir() else "file",
                    path.stat().st_mode & 0o777,
                    None if path.is_dir() else hashlib.sha256(path.read_bytes()).hexdigest(),
                )
                for path in sorted(root.rglob("*"))
            }

        before = snapshot(rendered)
        self.assertEqual(checker.stage_site(rendered, staged), [])
        after_stage = snapshot(staged)
        self.assertEqual(
            {path: (kind, digest) for path, (kind, _mode, digest) in after_stage.items()},
            {path: (kind, digest) for path, (kind, _mode, digest) in before.items()},
        )
        self.assertEqual(snapshot(rendered), before)
        for path in staged.rglob("*"):
            self.assertEqual(path.stat().st_uid, os.getuid())
            self.assertTrue(path.stat().st_mode & 0o200)
        with (staged / "index.html").open("r+b"):
            pass
        self.assertEqual(checker.prepare_site(staged, self.source, "/ising-model", self.revision, self.generated), [])
        self.assertEqual(checker.check_site(staged, self.source, "/ising-model", self.revision, self.generated), [])
        self.assertEqual(snapshot(rendered), before)

    def test_stage_rejects_overlap_existing_empty_and_nonregular_inputs(self) -> None:
        rendered = self.root / "_site-container"
        shutil.copytree(self.site, rendered)
        self.assertIn("STAGE_OVERLAP", [item.code for item in checker.stage_site(rendered, rendered)])
        self.assertIn("STAGE_OVERLAP", [item.code for item in checker.stage_site(rendered, rendered / "child")])
        parent = self.root / "publication"
        parent.mkdir()
        nested_input = parent / "input"
        shutil.copytree(rendered, nested_input)
        self.assertIn("STAGE_OVERLAP", [item.code for item in checker.stage_site(nested_input, parent)])
        destination = self.root / "existing"
        destination.write_text("sentinel", encoding="utf-8")
        self.assertIn("STAGE_DESTINATION", [item.code for item in checker.stage_site(rendered, destination)])
        self.assertEqual(destination.read_text(encoding="utf-8"), "sentinel")
        destination.unlink()
        destination.symlink_to(self.root / "missing")
        self.assertIn("STAGE_DESTINATION", [item.code for item in checker.stage_site(rendered, destination)])
        destination.unlink()
        empty = self.root / "empty"
        empty.mkdir()
        self.assertIn("EMPTY_SITE", [item.code for item in checker.stage_site(empty, destination)])
        (empty / "other.html").write_text("other", encoding="utf-8")
        self.assertIn("STAGE_INDEX", [item.code for item in checker.stage_site(empty, destination)])
        input_link = self.root / "input-link"
        input_link.symlink_to(rendered, target_is_directory=True)
        self.assertIn("STAGE_INPUT", [item.code for item in checker.stage_site(input_link, destination)])

    def test_stage_rejects_links_fifo_stale_temp_and_preserves_external_target(self) -> None:
        rendered = self.root / "_site-container"
        shutil.copytree(self.site, rendered)
        external = self.root / "external"
        external.write_text("untouched", encoding="utf-8")
        (rendered / "outside-link").symlink_to(external)
        (rendered / "dangling-link").symlink_to(self.root / "missing")
        fifo = rendered / "fifo"
        os.mkfifo(fifo)
        destination = self.root / "_site-staged"
        findings = checker.stage_site(rendered, destination)
        self.assertEqual([item.code for item in findings], ["NONREGULAR", "NONREGULAR", "NONREGULAR"])
        self.assertFalse(destination.exists())
        self.assertEqual(external.read_text(encoding="utf-8"), "untouched")
        fifo.unlink()
        (rendered / "outside-link").unlink()
        (rendered / "dangling-link").unlink()
        stale = self.root / "._site-staged.stage-stale"
        stale.mkdir()
        self.assertIn("STAGE_TEMP", [item.code for item in checker.stage_site(rendered, destination)])
        self.assertTrue(stale.is_dir())

    def test_stage_copy_inventory_rename_errors_are_stable_and_atomic(self) -> None:
        rendered = self.root / "_site-container"
        shutil.copytree(self.site, rendered)
        destination = self.root / "_site-staged"
        with mock.patch.object(checker, "_copy_stage_file", side_effect=OSError("copy refused")):
            findings = checker.stage_site(rendered, destination)
        self.assertEqual([(item.code, item.detail) for item in findings], [("STAGE_COPY", "copy refused")])
        self.assertFalse(destination.exists())
        self.assertEqual(list(self.root.glob("._site-staged.stage-*")), [])
        real_inventory = checker._stage_inventory
        calls = 0

        def corrupt_inventory(root: Path, logical: str):
            nonlocal calls
            calls += 1
            inventory, findings = real_inventory(root, logical)
            if calls == 3:
                inventory = checker.StageInventory(inventory.directories, inventory.files[:-1])
            return inventory, findings

        with mock.patch.object(checker, "_stage_inventory", side_effect=corrupt_inventory):
            self.assertIn("STAGE_INVENTORY", [item.code for item in checker.stage_site(rendered, destination)])
        self.assertFalse(destination.exists())
        with mock.patch.object(checker, "_rename_stage_noreplace", side_effect=OSError("rename refused")):
            findings = checker.stage_site(rendered, destination)
        self.assertEqual([(item.code, item.detail) for item in findings], [("STAGE_RENAME", "rename refused")])
        self.assertFalse(destination.exists())

    def test_stage_stat_read_create_write_and_writability_errors_are_stable(self) -> None:
        rendered = self.root / "_site-container"
        destination = self.root / "_site-staged"
        shutil.copytree(self.site, rendered)

        real_lstat = checker.Path.lstat
        root_stats = 0

        def fail_second_root_stat(path: Path):
            nonlocal root_stats
            if path == rendered:
                root_stats += 1
                if root_stats == 2:
                    raise OSError("stat refused")
            return real_lstat(path)

        with mock.patch.object(checker.Path, "lstat", fail_second_root_stat):
            findings = checker.stage_site(rendered, destination)
        self.assertIn(("STAGE_STAT", "stat refused"), [(item.code, item.detail) for item in findings])
        self.assertFalse(destination.exists())

        with mock.patch.object(checker, "_read_stage_file", side_effect=OSError("read refused")):
            findings = checker.stage_site(rendered, destination)
        self.assertIn(("STAGE_READ", "read refused"), [(item.code, item.detail) for item in findings])
        self.assertFalse(destination.exists())

        real_open = checker.Path.open

        def fail_create(path: Path, mode: str = "r", *args, **kwargs):
            if mode == "xb":
                raise OSError("create refused")
            return real_open(path, mode, *args, **kwargs)

        with mock.patch.object(checker.Path, "open", fail_create):
            findings = checker.stage_site(rendered, destination)
        self.assertEqual([(item.code, item.detail) for item in findings], [("STAGE_COPY", "create refused")])
        self.assertFalse(destination.exists())

        real_write = checker._copy_stage_file

        def fail_write(source: Path, target: Path, expected: tuple[int, str]) -> None:
            if source.name == "asset.png":
                raise OSError("write refused")
            real_write(source, target, expected)

        with mock.patch.object(checker, "_copy_stage_file", side_effect=fail_write):
            findings = checker.stage_site(rendered, destination)
        self.assertEqual([(item.code, item.detail) for item in findings], [("STAGE_COPY", "write refused")])
        self.assertFalse(destination.exists())

        def fail_writable(path: Path, mode: str = "r", *args, **kwargs):
            if mode == "r+b":
                raise OSError("writable refused")
            return real_open(path, mode, *args, **kwargs)

        with mock.patch.object(checker.Path, "open", fail_writable):
            findings = checker.stage_site(rendered, destination)
        self.assertEqual([(item.code, item.detail) for item in findings], [("STAGE_WRITABLE", "writable refused")])
        self.assertFalse(destination.exists())
        with mock.patch.object(checker.tempfile, "mkdtemp", side_effect=OSError("stage root refused")):
            findings = checker.stage_site(rendered, destination)
        self.assertEqual([(item.code, item.detail) for item in findings], [("STAGE_COPY", "stage root refused")])
        self.assertFalse(destination.exists())
        self.assertEqual(list(self.root.glob("._site-staged.stage-*")), [])

    def test_stage_commit_never_replaces_destination_created_during_staging(self) -> None:
        rendered = self.root / "_site-container"
        destination = self.root / "_site-staged"
        shutil.copytree(self.site, rendered)
        real_publish = checker._rename_stage_noreplace

        def race(source: Path, target: Path) -> None:
            target.mkdir()
            (target / "competitor").write_text("preserved", encoding="utf-8")
            real_publish(source, target)

        with mock.patch.object(checker, "_rename_stage_noreplace", side_effect=race):
            findings = checker.stage_site(rendered, destination)
        self.assertEqual([item.code for item in findings], ["STAGE_RENAME"])
        self.assertEqual((destination / "competitor").read_text(encoding="utf-8"), "preserved")
        self.assertFalse((destination / "index.html").exists())
        self.assertEqual(list(self.root.glob("._site-staged.stage-*")), [])
        shutil.rmtree(destination)
        with mock.patch.object(checker.sys, "platform", "unsupported"):
            findings = checker.stage_site(rendered, destination)
        self.assertEqual([item.code for item in findings], ["STAGE_RENAME"])
        self.assertIn("unavailable", findings[0].detail)
        self.assertFalse(destination.exists())

    def test_stage_cli_success_and_failure(self) -> None:
        rendered = self.root / "_site-container"
        destination = self.root / "_site-staged"
        shutil.copytree(self.site, rendered)
        passed = subprocess.run(
            [sys.executable, str(CHECKER_PATH), "stage", "--input-site", str(rendered), "--site", str(destination)],
            text=True, capture_output=True, check=False,
        )
        self.assertEqual(passed.returncode, 0, passed.stdout + passed.stderr)
        self.assertIn("handwritten Pages stage: PASS", passed.stdout)
        failed = subprocess.run(
            [sys.executable, str(CHECKER_PATH), "stage", "--input-site", str(rendered), "--site", str(destination)],
            text=True, capture_output=True, check=False,
        )
        self.assertEqual(failed.returncode, 1)
        self.assertIn("STAGE_DESTINATION", failed.stdout)

    def test_fetch_retries_and_rejects_redirect(self) -> None:
        response = mock.MagicMock()
        response.__enter__.return_value = response
        response.status = 200
        response.geturl.return_value = "https://example.test/right"
        response.read.return_value = b"ok"
        with mock.patch.object(checker.urllib.request, "urlopen", side_effect=[OSError("one"), response]), mock.patch.object(checker.time, "sleep") as sleep:
            body, error = checker._fetch("https://example.test/right")
        self.assertEqual((body, error), (b"ok", None))
        sleep.assert_called_once()
        response.geturl.return_value = "https://example.test/wrong"
        with mock.patch.object(checker.urllib.request, "urlopen", return_value=response):
            body, error = checker._fetch("https://example.test/right", retries=1)
        self.assertIsNone(body)
        self.assertIn("redirected", error or "")
        with mock.patch.object(checker.urllib.request, "urlopen", side_effect=OSError("down")) as request, mock.patch.object(checker.time, "sleep") as sleep:
            body, error = checker._fetch("https://example.test/right")
        self.assertEqual((body, error), (None, "down"))
        self.assertEqual(request.call_count, 3)
        self.assertEqual(sleep.call_count, 2)

    def test_fetch_retry_success_and_exhaustion_against_local_http_server(self) -> None:
        class Handler(http.server.BaseHTTPRequestHandler):
            attempts = 0
            always_fail = False

            def do_GET(self):
                type(self).attempts += 1
                if type(self).always_fail or type(self).attempts < 3:
                    self.send_response(503)
                    self.end_headers()
                    return
                body = b"ready"
                self.send_response(200)
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)

            def log_message(self, _format, *_args):
                return

        server = http.server.ThreadingHTTPServer(("127.0.0.1", 0), Handler)
        thread = threading.Thread(target=server.serve_forever, daemon=True)
        thread.start()
        self.addCleanup(server.server_close)
        self.addCleanup(server.shutdown)
        url = f"http://127.0.0.1:{server.server_port}/snapshot"
        with mock.patch.object(checker.time, "sleep"):
            self.assertEqual(checker._fetch(url), (b"ready", None))
        self.assertEqual(Handler.attempts, 3)
        Handler.attempts = 0
        Handler.always_fail = True
        with mock.patch.object(checker.time, "sleep"):
            body, error = checker._fetch(url)
        self.assertIsNone(body)
        self.assertIn("503", error or "")
        self.assertEqual(Handler.attempts, 3)

    def test_live_pipeline_passes_and_rejects_stale_revision(self) -> None:
        self.assertEqual(self.prepare(), [])

        def fetch(url: str, retries: int = 3):
            del retries
            prefix = "https://example.test/ising-model/"
            if not url.startswith(prefix):
                return None, "outside base"
            path = self.site / urllib.parse.unquote(url[len(prefix):].split("?", 1)[0])
            try:
                return path.read_bytes(), None
            except OSError as exc:
                return None, str(exc)

        with mock.patch.object(checker, "_fetch", side_effect=fetch):
            self.assertEqual(checker.check_live("https://example.test/ising-model/", self.source, "/ising-model", self.revision, self.generated), [])
        manifest_path = self.site / checker.MANIFEST_NAME
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        manifest["source_revision"] = "b" * 40
        manifest_path.write_text(json.dumps(manifest), encoding="utf-8")
        with mock.patch.object(checker, "_fetch", side_effect=fetch):
            codes = [item.code for item in checker.check_live("https://example.test/ising-model/", self.source, "/ising-model", self.revision, self.generated)]
        self.assertIn("MANIFEST", codes)

    def test_live_fetches_manifest_inventory_and_rejects_unsafe_paths(self) -> None:
        self.assertEqual(self.prepare(), [])
        requested: list[str] = []

        def fetch(url: str, retries: int = 3):
            del retries
            requested.append(url)
            prefix = "https://example.test/ising-model/"
            path = self.site / urllib.parse.unquote(url[len(prefix):])
            return path.read_bytes(), None

        with mock.patch.object(checker, "_fetch", side_effect=fetch):
            self.assertEqual(checker.check_live("https://example.test/ising-model/", self.source, "/ising-model", self.revision, self.generated), [])
        self.assertIn("https://example.test/ising-model/asset.png", requested)
        manifest_path = self.site / checker.MANIFEST_NAME
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        attacks = (
            "https://attacker.invalid/steal", "//attacker.invalid/steal", "../outside",
            "%2e%2e/outside", "%2Foutside", "nested%5coutside", "nested\\outside",
            "asset.png?secret=1", "asset.png#fragment", "C:outside",
        )
        for attack in attacks:
            with self.subTest(attack=attack):
                poisoned = json.loads(json.dumps(manifest))
                poisoned["files"][0]["path"] = attack
                manifest_bytes = json.dumps(poisoned).encode()
                fetch_mock = mock.Mock(return_value=(manifest_bytes, None))
                with mock.patch.object(checker, "_fetch", fetch_mock):
                    findings = checker.check_live("https://example.test/ising-model/", self.source, "/ising-model", self.revision, self.generated)
                self.assertEqual([item.code for item in findings], ["MANIFEST"])
                fetch_mock.assert_called_once_with("https://example.test/ising-model/pages-manifest.json")


@contextmanager
def mutant(old: str, new: str):
    source = CHECKER_PATH.read_text(encoding="utf-8")
    count = source.count(old)
    if count != 1:
        raise AssertionError(f"mutation replacement count is {count}, expected exactly 1: {old!r}")
    with tempfile.TemporaryDirectory(prefix="pages-mutant-") as raw:
        path = Path(raw) / "pages_site_check.py"
        path.write_text(source.replace(old, new), encoding="utf-8")
        name = f"pages_site_mutant_{uuid.uuid4().hex}"
        spec = importlib.util.spec_from_file_location(name, path)
        assert spec and spec.loader
        module = importlib.util.module_from_spec(spec)
        sys.modules[name] = module
        try:
            spec.loader.exec_module(module)
            yield module
        finally:
            sys.modules.pop(name, None)


def workflow_contract_findings(pages: str, release: str, lean: str) -> list[str]:
    """Bounded exact contract shared by the real-tree and mutation tests."""
    findings: list[str] = []
    dispatch = pages.split("workflow_dispatch:", 1)[-1].split("workflow_call:", 1)[0]
    required_counts = {
        "manual mode": (dispatch, "mode:", 1),
        "manual ref guard": (pages, 'test "$RUN_REF" = refs/heads/main', 2),
        "manual kind": (pages, 'test -z "$INVOCATION_KIND"', 1),
        "release kind": (pages, 'test "$INVOCATION_KIND" = release', 1),
        "cross-mode mode": (pages, 'test -z "$MODE"', 1),
        "release deploy": (pages, 'test "$RELEASE_DEPLOY" = true', 1),
        "validated deploy": (pages, "if: needs.build.outputs.deploy == 'true'", 1),
        "tag input": (pages, 'case "$SOURCE_REF" in refs/tags/v*)', 1),
        "Pages credentials": (pages, "persist-credentials: false", 2),
        "release credentials": (release, "persist-credentials: false", 2),
        "one deployer": (pages, "actions/deploy-pages@", 1),
        "one artifact": (pages, "actions/upload-pages-artifact@", 1),
        "new tag query": (release, 'existing=$(git ls-remote origin "refs/tags/$tag")', 1),
        "new tag verdict": (release, 'test -z "$existing"', 1),
        "toolchain equality": (release, 'test "$toolchain" = "$EXPECTED_TOOLCHAIN"', 1),
        "new range": (release, 'test "$source_sha" != "$BEFORE"', 1),
        "main before write": (release, 'test "$PUSH_REF" = refs/heads/main', 1),
        "push before write": (release, 'test "$EVENT_NAME" = push', 1),
        "zero action bypass": (release, "if: github.event.before != '0000000000000000000000000000000000000000'", 1),
        "zero release path": (release, "if: github.event.before == '0000000000000000000000000000000000000000'", 1),
        "zero current snapshot": (release, 'test "$source_sha" = "$AFTER"', 1),
        "caller kind": (release, "invocation_kind: release", 1),
        "caller deploy": (release, "deploy: true", 1),
        "source preflight": (pages, "python3 scripts/pages_site_check.py source --source ./docs", 1),
        "container destination": (pages, "destination: ./_site-container", 1),
        "ownership stage": (pages, "python3 scripts/pages_site_check.py stage", 1),
        "stage source": (pages, "--input-site ./_site-container --site ./_site", 1),
        "prepare final": (pages, "--site ./_site --source ./docs --baseurl /ising-model", 1),
        "upload final": (pages, "path: ./_site", 1),
    }
    for label, (text, needle, expected) in required_counts.items():
        if text.count(needle) != expected:
            findings.append(label)
    if "source_sha:" in dispatch or "source_ref:" in dispatch:
        findings.append("editable manual source")
    if 'test "$EVENT_NAME" = workflow_call' in pages or "github.event_name == 'workflow_call'" in pages:
        findings.append("caller event assumption")
    if "python3 scripts/test_pages_site_check.py" not in pages or "python3 scripts/docs_link_check.py --check" not in pages:
        findings.append("publication source gates")
    source_gate = "python3 scripts/pages_site_check.py source --source ./docs"
    if source_gate in pages and pages.index(source_gate) > pages.find("actions/jekyll-build-pages@"):
        findings.append("late source preflight")
    jekyll = "actions/jekyll-build-pages@"
    stage = "python3 scripts/pages_site_check.py stage"
    prepare = "python3 scripts/pages_site_check.py prepare"
    if all(needle in pages for needle in (jekyll, stage, prepare)) and not (
        pages.index(jekyll) < pages.index(stage) < pages.index(prepare)
    ):
        findings.append("ownership stage order")
    if "needs: [prepare-release-source, lean-release-tag]" not in release or "refs/tags/$tag" not in release:
        findings.append("release resolver")
    if "      - 'master'" in release:
        findings.append("non-main release trigger")
    if 'gh api --method POST "repos/$REPOSITORY/git/tags"' not in release or 'gh api --method POST "repos/$REPOSITORY/releases"' not in release:
        findings.append("zero-before release semantics")
    if "pages: write" in lean or "id-token: write" in lean:
        findings.append("Lean authority")
    uses = re.findall(r"uses:[ ]+([^\s]+@([^\s]+))", pages + release)
    if not uses or any(re.fullmatch(r"[0-9a-f]{40}", ref) is None for _whole, ref in uses):
        findings.append("immutable action refs")
    return findings


def workflow_run_script(workflow: str, step_name: str) -> str:
    marker = f"    - name: {step_name}\n"
    block = workflow.split(marker, 1)[1]
    body = block.split("      run: |\n", 1)[1]
    lines: list[str] = []
    for line in body.splitlines():
        if line.startswith("        "):
            lines.append(line[8:])
        elif not line:
            lines.append("")
        else:
            break
    return "\n".join(lines) + "\n"


class MutationTest(SiteTest):
    def test_page_set_manifest_api_and_base_guards_are_nonvacuous(self) -> None:
        self.assertEqual(self.prepare(), [])
        baseline = self.root / "baseline-site"
        shutil.copytree(self.site, baseline)
        cases = [
            ("if actual_pages != expected_pages:", "if False:", "PAGE_SET"),
            ('if relative.parts[:1] == ("docs",):', "if False:", "API_CONTENT"),
            ("if manifest != expected_manifest:", "if False:", "MANIFEST"),
            ("if path.startswith(\"/\") and not path.startswith(baseurl + \"/\"):", "if False:", "BASEURL_ESCAPE"),
        ]
        for old, new, code in cases:
            with self.subTest(code=code):
                shutil.rmtree(self.site)
                shutil.copytree(baseline, self.site)
                if code == "PAGE_SET":
                    (self.site / "extra.html").write_text("extra", encoding="utf-8")
                elif code == "API_CONTENT":
                    (self.site / "docs").mkdir()
                    (self.site / "docs" / "Bad.html").write_text("bad", encoding="utf-8")
                elif code == "MANIFEST":
                    (self.site / checker.MANIFEST_NAME).write_text("{}", encoding="utf-8")
                else:
                    (self.site / "index.html").write_text(
                        (self.site / "index.html").read_text().replace("</body>", '<a href="/bad">x</a></body>'),
                        encoding="utf-8",
                    )
                self.assertIn(code, self.codes())
                with mutant(old, new) as module:
                    self.assertNotIn(code, self.codes(module))

    def test_tracked_edges_fragments_discovery_and_retry_guards_are_nonvacuous(self) -> None:
        self.assertEqual(self.prepare(), [])
        root = self.site / "index.html"
        root.write_text(root.read_text().replace("nested/status.html#status", "nested/status.html#missing"), encoding="utf-8")
        self.assertIn("MISSING_FRAGMENT", self.codes())
        with mutant(
            "if target_page is None or fragment not in target_page.anchors:",
            "if False:",
        ) as module:
            self.assertNotIn("MISSING_FRAGMENT", self.codes(module))
        root.write_text(root.read_text().replace("nested/status.html#missing", "#home"), encoding="utf-8")
        self.assertIn("EDGE_LOSS", self.codes())
        with mutant(
            "missing_edges = expected_edge_counts - actual_edges",
            "missing_edges = Counter()",
        ) as module:
            self.assertNotIn("EDGE_LOSS", self.codes(module))
        (self.source / "untracked.md").write_text("# Untracked\n", encoding="utf-8")
        (self.site / "untracked.html").write_text("<h1>untracked</h1>", encoding="utf-8")
        self.assertIn("PAGE_SET", self.codes())
        with mutant(
            'relative = sorted(name[len(prefix):] for name in names if name.startswith(prefix))',
            'relative = sorted(path.relative_to(source).as_posix() for path in source.rglob("*") if path.is_file())',
        ) as module:
            self.assertNotIn("PAGE_SET", self.codes(module))
        with mock.patch.object(checker.urllib.request, "urlopen", side_effect=OSError("down")), mock.patch.object(checker.time, "sleep"):
            self.assertEqual(checker._fetch("https://example.test/right"), (None, "down"))
        with mutant("return None, last", 'return b"", None') as module, mock.patch.object(module.urllib.request, "urlopen", side_effect=OSError("down")), mock.patch.object(module.time, "sleep"):
            self.assertNotEqual(module._fetch("https://example.test/right"), (None, "down"))

    def test_live_manifest_origin_guard_is_mutation_pinned(self) -> None:
        self.assertEqual(self.prepare(), [])
        manifest = json.loads((self.site / checker.MANIFEST_NAME).read_text(encoding="utf-8"))
        manifest["files"][0]["path"] = "https://attacker.invalid/steal"
        manifest_bytes = json.dumps(manifest).encode()
        with mutant(
            "    parsed = urllib.parse.urlsplit(relative)\n    decoded = urllib.parse.unquote(relative)",
            "    return urllib.parse.urljoin(base, relative), None\n    decoded = urllib.parse.unquote(relative)",
        ) as module:
            responses = [(manifest_bytes, None)]
            fetch_mock = mock.Mock(side_effect=lambda _url: responses.pop(0) if responses else (None, "attacker reached"))
            with mock.patch.object(module, "_fetch", fetch_mock):
                findings = module.check_live("https://example.test/ising-model/", self.source, "/ising-model", self.revision, self.generated)
            self.assertGreater(fetch_mock.call_count, 1)
            self.assertTrue(any(item.code == "LIVE_FETCH" for item in findings))

    def test_source_liquid_guard_is_mutation_pinned(self) -> None:
        index = self.source / "index.md"
        guard = '            for token in ("{{", "{%"):'
        for opener, weakened in (("{{", '            for token in ("{%",):'), ("{%", '            for token in ("{{",):')):
            with self.subTest(opener=opener):
                index.write_text(f"# Unsafe\n\n{opener}\n", encoding="utf-8")
                self.assertIn("LIQUID_DELIMITER", [item.code for item in checker.check_source(self.source)])
                with mutant(guard, weakened) as module:
                    self.assertNotIn("LIQUID_DELIMITER", [item.code for item in module.check_source(self.source)])

    def test_source_read_oserror_guard_is_mutation_pinned(self) -> None:
        with mock.patch.object(checker.Path, "read_text", side_effect=OSError("unreadable source")):
            self.assertEqual(
                [item.code for item in checker.check_source(self.source)],
                ["SOURCE", "SOURCE"],
            )
        with mutant(
            '            text = path.read_text(encoding="utf-8")\n        except (OSError, UnicodeError) as exc:\n            findings.append(Finding(name, "SOURCE", str(exc)))',
            '            text = path.read_text(encoding="utf-8")\n        except UnicodeError as exc:\n            findings.append(Finding(name, "SOURCE", str(exc)))',
        ) as module, mock.patch.object(module.Path, "read_text", side_effect=OSError("unreadable source")):
            with self.assertRaisesRegex(OSError, "unreadable source"):
                module.check_source(self.source)

    def test_stage_security_and_conservation_guards_are_mutation_pinned(self) -> None:
        rendered = self.root / "_site-container"
        shutil.copytree(self.site, rendered)
        destination = self.root / "_site-staged"
        cases = (
            (
                "    if _stage_paths_overlap(source, destination):\n        return [Finding(str(site), \"STAGE_OVERLAP\", \"input and destination paths overlap\")]",
                "    if False:\n        return [Finding(str(site), \"STAGE_OVERLAP\", \"input and destination paths overlap\")]",
                lambda module: self.assertNotIn("STAGE_OVERLAP", [item.code for item in module.stage_site(rendered, rendered / "child")]),
            ),
            (
                "                else:\n                    findings.append(Finding(relative, \"NONREGULAR\", \"rendered input contains a non-regular entry\"))",
                "                else:\n                    pass",
                lambda module: self._assert_stage_mutant_accepts_symlink(module, rendered, destination),
            ),
            (
                "        if staged != frozen:\n            findings.append(Finding(str(site), \"STAGE_INVENTORY\", \"staged paths or byte digests differ from rendered input\"))",
                "        if False:\n            findings.append(Finding(str(site), \"STAGE_INVENTORY\", \"staged paths or byte digests differ from rendered input\"))",
                lambda module: self._assert_stage_mutant_misses_inventory(module, rendered, destination),
            ),
            (
                '        _rename_stage_noreplace(temporary, destination)\n',
                '        shutil.copytree(temporary, destination)\n',
                lambda module: self._assert_stage_mutant_uses_nonatomic_publish(module, rendered, destination),
            ),
        )
        for old, new, assertion in cases:
            with self.subTest(old=old):
                if os.path.lexists(destination):
                    if destination.is_dir() and not destination.is_symlink():
                        shutil.rmtree(destination)
                    else:
                        destination.unlink()
                with mutant(old, new) as module:
                    assertion(module)

    def test_stage_copy_descriptor_writability_and_publish_guards_are_mutation_pinned(self) -> None:
        rendered = self.root / "_site-container"
        destination = self.root / "_site-staged"
        shutil.copytree(self.site, rendered)
        cases = (
            (
                '    flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0)\n    descriptor = os.open(source, flags)',
                '    flags = os.O_RDONLY\n    descriptor = os.open(source, flags)',
                self._assert_stage_nofollow_guard,
            ),
            (
                '            or (actual.st_dev, actual.st_ino) != (metadata.st_dev, metadata.st_ino)\n',
                '            or False\n',
                self._assert_stage_file_identity_guard,
            ),
            (
                '                expected is not None and (actual.st_dev, actual.st_ino) != (expected.st_dev, expected.st_ino)\n',
                '                False\n',
                self._assert_stage_directory_identity_guard,
            ),
            (
                '        try:\n            with (temporary / "index.html").open("r+b"):\n                pass\n        except OSError as exc:\n            findings.append(Finding("index.html", "STAGE_WRITABLE", _stage_error(exc)))',
                '        try:\n            pass\n        except OSError as exc:\n            findings.append(Finding("index.html", "STAGE_WRITABLE", _stage_error(exc)))',
                self._assert_stage_writability_guard,
            ),
            (
                '            _copy_stage_file(source / relative, temporary / relative, (size, digest))',
                '            pass',
                self._assert_stage_omitted_copy_detected,
            ),
            (
                '            output_handle.write(chunk)\n            digest.update(chunk)',
                '            output_handle.write(chunk + b"corrupt")\n            digest.update(chunk)',
                self._assert_stage_corrupt_copy_detected,
            ),
            (
                '                _rename_stage_noreplace(temporary, destination)',
                '                os.rename(temporary, destination)',
                self._assert_stage_publish_race_guard,
            ),
        )
        for old, new, assertion in cases:
            with self.subTest(old=old):
                if os.path.lexists(destination):
                    if destination.is_dir() and not destination.is_symlink():
                        shutil.rmtree(destination)
                    else:
                        destination.unlink()
                with mutant(old, new) as module:
                    assertion(module, rendered, destination)

    def _assert_stage_mutant_accepts_symlink(self, module: types.ModuleType, rendered: Path, destination: Path) -> None:
        link = rendered / "outside"
        link.symlink_to(self.root / "missing")
        self.assertNotIn("NONREGULAR", [item.code for item in module.stage_site(rendered, destination)])
        link.unlink()

    def _assert_stage_mutant_misses_inventory(self, module: types.ModuleType, rendered: Path, destination: Path) -> None:
        real_inventory = module._stage_inventory
        calls = 0

        def corrupt(root: Path, logical: str):
            nonlocal calls
            calls += 1
            inventory, findings = real_inventory(root, logical)
            if calls == 3:
                inventory = module.StageInventory(inventory.directories, inventory.files[:-1])
            return inventory, findings

        with mock.patch.object(module, "_stage_inventory", side_effect=corrupt):
            self.assertNotIn("STAGE_INVENTORY", [item.code for item in module.stage_site(rendered, destination)])

    def _assert_stage_mutant_uses_nonatomic_publish(self, module: types.ModuleType, rendered: Path, destination: Path) -> None:
        with mock.patch.object(module.shutil, "copytree", side_effect=OSError("non-atomic publish reached")):
            findings = module.stage_site(rendered, destination)
        self.assertTrue(any(item.detail == "non-atomic publish reached" for item in findings))

    def _assert_stage_nofollow_guard(self, module: types.ModuleType, rendered: Path, destination: Path) -> None:
        target = rendered / "asset.png"
        preserved = rendered / "asset-preserved.png"
        real_open = os.open
        swapped = False

        def race(path, flags, *args, **kwargs):
            nonlocal swapped
            if Path(path) == target and not swapped:
                swapped = True
                target.rename(preserved)
                target.symlink_to(preserved.name)
            return real_open(path, flags, *args, **kwargs)

        with mock.patch.object(module.os, "open", side_effect=race):
            findings = module.stage_site(rendered, destination)
        self.assertNotIn("STAGE_COPY", [item.code for item in findings])
        target.unlink()
        preserved.rename(target)

    def _assert_stage_file_identity_guard(self, module: types.ModuleType, rendered: Path, destination: Path) -> None:
        target = rendered / "asset.png"
        replacement = self.root / "replacement"
        replacement.write_bytes(target.read_bytes())
        real_open = os.open
        target_opens = 0

        def race(path, flags, *args, **kwargs):
            nonlocal target_opens
            if Path(path) == target:
                target_opens += 1
            if Path(path) == target and target_opens == 2:
                target.unlink()
                replacement.rename(target)
            return real_open(path, flags, *args, **kwargs)

        with mock.patch.object(module.os, "open", side_effect=race):
            self.assertEqual(module.stage_site(rendered, destination), [])

    def _assert_stage_writability_guard(self, module: types.ModuleType, rendered: Path, destination: Path) -> None:
        real_open = module.Path.open

        def fail(path: Path, mode: str = "r", *args, **kwargs):
            if mode == "r+b":
                raise OSError("writable refused")
            return real_open(path, mode, *args, **kwargs)

        with mock.patch.object(module.Path, "open", fail):
            self.assertNotIn("STAGE_WRITABLE", [item.code for item in module.stage_site(rendered, destination)])

    def _assert_stage_directory_identity_guard(self, module: types.ModuleType, rendered: Path, destination: Path) -> None:
        target = rendered / "nested"
        replacement = self.root / "replacement-directory"
        shutil.copytree(target, replacement)
        real_open = os.open
        swapped = False

        def race(path, flags, *args, **kwargs):
            nonlocal swapped
            if Path(path) == target and not swapped:
                swapped = True
                shutil.rmtree(target)
                replacement.rename(target)
            return real_open(path, flags, *args, **kwargs)

        with mock.patch.object(module.os, "open", side_effect=race):
            self.assertEqual(module.stage_site(rendered, destination), [])

    def _assert_stage_omitted_copy_detected(self, module: types.ModuleType, rendered: Path, destination: Path) -> None:
        findings = module.stage_site(rendered, destination)
        self.assertIn("STAGE_INVENTORY", [item.code for item in findings])
        self.assertFalse(destination.exists())

    def _assert_stage_corrupt_copy_detected(self, module: types.ModuleType, rendered: Path, destination: Path) -> None:
        findings = module.stage_site(rendered, destination)
        self.assertIn("STAGE_INVENTORY", [item.code for item in findings])
        self.assertFalse(destination.exists())

    def _assert_stage_publish_race_guard(self, module: types.ModuleType, rendered: Path, destination: Path) -> None:
        real_rename = os.rename

        def race(source: Path, target: Path) -> None:
            target.mkdir()
            real_rename(source, target)

        with mock.patch.object(module.os, "rename", side_effect=race):
            self.assertEqual(module.stage_site(rendered, destination), [])
        self.assertTrue((destination / "index.html").exists())


class WorkflowContractTest(unittest.TestCase):
    def test_single_writer_triggers_pins_permissions_and_release_call(self) -> None:
        pages = (REPO_ROOT / ".github/workflows/pages.yml").read_text(encoding="utf-8")
        release = (REPO_ROOT / ".github/workflows/create-release.yml").read_text(encoding="utf-8")
        lean = (REPO_ROOT / ".github/workflows/lean_action_ci.yml").read_text(encoding="utf-8")
        self.assertEqual(workflow_contract_findings(pages, release, lean), [])
        self.assertIn("workflow_dispatch:", pages)
        self.assertIn("workflow_call:", pages)
        dispatch = pages.split("workflow_dispatch:", 1)[1].split("workflow_call:", 1)[0]
        self.assertIn("mode:", dispatch)
        self.assertNotIn("source_sha:", dispatch)
        self.assertNotIn("source_ref:", dispatch)
        self.assertNotIn("\n  push:", pages)
        self.assertNotIn("schedule:", pages)
        self.assertNotIn("docgen", pages.lower())
        self.assertEqual(pages.count("actions/deploy-pages@"), 1)
        self.assertIn("cancel-in-progress: false", pages)
        self.assertEqual(pages.count("persist-credentials: false"), 2)
        self.assertIn('test "$RUN_REF" = refs/heads/main', pages)
        self.assertIn('source_sha=$(git rev-parse refs/remotes/origin/main^{commit})', pages)
        self.assertIn('case "$SOURCE_REF" in refs/tags/v*)', pages)
        self.assertIn("python3 scripts/test_pages_site_check.py", pages)
        self.assertIn("python3 scripts/docs_link_check.py --check", pages)
        source_gate = "python3 scripts/pages_site_check.py source --source ./docs"
        self.assertEqual(pages.count(source_gate), 1)
        self.assertLess(pages.index(source_gate), pages.index("actions/jekyll-build-pages@"))
        stage = "python3 scripts/pages_site_check.py stage"
        self.assertEqual(pages.count(stage), 1)
        self.assertLess(pages.index("actions/jekyll-build-pages@"), pages.index(stage))
        self.assertLess(pages.index(stage), pages.index("python3 scripts/pages_site_check.py prepare"))
        self.assertEqual(pages.count("destination: ./_site-container"), 1)
        self.assertEqual(pages.count("--input-site ./_site-container --site ./_site"), 1)
        for sha in checker.ACTION_SHAS:
            self.assertIn(sha, pages + release)
        external_uses = re.findall(r"uses:[ ]+([^\s]+@[^\s]+)", pages + release)
        self.assertTrue(external_uses)
        self.assertTrue(all(re.search(r"@[0-9a-f]{40}$", item) for item in external_uses))
        self.assertIn("uses: ./.github/workflows/pages.yml", release)
        self.assertIn("needs: [prepare-release-source, lean-release-tag]", release)
        self.assertIn('existing=$(git ls-remote origin "refs/tags/$tag")', release)
        self.assertIn("refs/tags/$tag", release)
        self.assertIn("refs/tags/v[0-9]*", release)
        self.assertIn('zero=0000000000000000000000000000000000000000', release)
        self.assertIn('git show "$source_sha:lean-toolchain"', release)
        self.assertIn('git show "$parent:lean-toolchain"', release)
        self.assertIn("source_sha=$(git rev-parse", release)
        self.assertIn("if: needs.resolve-release-source.outputs.publish == 'true'", release)
        self.assertIn("deploy: true", release)
        self.assertIn("invocation_kind: release", release)
        write_job = release.split("lean-release-tag:", 1)[1].split("resolve-release-source:", 1)[0]
        self.assertEqual(write_job.count("contents: write"), 1)
        self.assertNotIn("git fetch", write_job)
        resolver = release.split("resolve-release-source:", 1)[1].split("publish-handwritten-pages:", 1)[0]
        self.assertEqual(resolver.count("contents: read"), 1)
        self.assertNotIn("contents: write", resolver)
        self.assertEqual(release.count("persist-credentials: false"), 2)
        self.assertNotIn("pages: write", lean)
        self.assertNotIn("id-token: write", lean)
        self.assertNotIn("docgen-action", lean)
        self.assertIn("python3 scripts/test_pages_site_check.py", lean)
        self.assertEqual((REPO_ROOT / "README.md").read_text().count("Derived handwritten Pages snapshot"), 1)

    def test_identity_and_permission_guards_are_mutation_pinned(self) -> None:
        pages_path = REPO_ROOT / ".github/workflows/pages.yml"
        release_path = REPO_ROOT / ".github/workflows/create-release.yml"
        cases = (
            (pages_path, 'test "$RUN_REF" = refs/heads/main', 'test -n "$RUN_REF"', 2),
            (pages_path, 'case "$SOURCE_REF" in refs/tags/v*)', 'case "$SOURCE_REF" in *)', 1),
            (pages_path, 'persist-credentials: false', 'persist-credentials: true', 2),
            (release_path, 'test -z "$existing"', 'true', 1),
            (release_path, 'test "$toolchain" = "$EXPECTED_TOOLCHAIN"', 'true', 1),
            (release_path, 'test "$source_sha" != "$BEFORE"', 'true', 1),
            (release_path, 'test "$PUSH_REF" = refs/heads/main', 'true', 1),
            (release_path, 'test "$EVENT_NAME" = push', 'true', 1),
            (release_path, "if: github.event.before != '0000000000000000000000000000000000000000'", "if: true", 1),
            (release_path, "if: github.event.before == '0000000000000000000000000000000000000000'", "if: false", 1),
            (release_path, 'test "$source_sha" = "$AFTER"', 'true', 1),
            (pages_path, 'test -z "$INVOCATION_KIND"', 'true', 1),
            (pages_path, 'test "$INVOCATION_KIND" = release', 'true', 1),
            (pages_path, 'test -z "$MODE"', 'true', 1),
            (pages_path, 'test "$RELEASE_DEPLOY" = true', 'true', 1),
            (pages_path, "if: needs.build.outputs.deploy == 'true'", "if: inputs.deploy", 1),
            (release_path, "invocation_kind: release", "invocation_kind: manual", 1),
            (pages_path, "python3 scripts/pages_site_check.py source --source ./docs", "true", 1),
            (pages_path, "destination: ./_site-container", "destination: ./_site", 1),
            (pages_path, "python3 scripts/pages_site_check.py stage", "true", 1),
            (pages_path, "--input-site ./_site-container --site ./_site", "--input-site ./_site --site ./_site-container", 1),
        )
        real_pages = pages_path.read_text(encoding="utf-8")
        real_release = release_path.read_text(encoding="utf-8")
        lean = (REPO_ROOT / ".github/workflows/lean_action_ci.yml").read_text(encoding="utf-8")
        self.assertEqual(workflow_contract_findings(real_pages, real_release, lean), [])
        for path, guard, weakened, expected_count in cases:
            with self.subTest(guard=guard):
                text = path.read_text(encoding="utf-8")
                count = text.count(guard)
                self.assertEqual(count, expected_count)
                mutant_text = text.replace(guard, weakened, 1)
                self.assertEqual(mutant_text.count(guard), count - 1)
                pages = mutant_text if path == pages_path else real_pages
                release = mutant_text if path == release_path else real_release
                self.assertNotEqual(workflow_contract_findings(pages, release, lean), [])

        source_gate = "python3 scripts/pages_site_check.py source --source ./docs"
        moved = real_pages.replace(source_gate, "true", 1).replace(
            "      - name: Record generation time",
            f"      - name: Late source preflight\n        run: {source_gate}\n      - name: Record generation time",
            1,
        )
        self.assertEqual(moved.count(source_gate), 1)
        self.assertIn("late source preflight", workflow_contract_findings(moved, real_release, lean))
        stage = "python3 scripts/pages_site_check.py stage"
        late_stage = real_pages.replace(stage, "true", 1).replace(
            "      - name: Upload the one complete Pages artifact",
            f"      - name: Late ownership stage\n        run: {stage}\n      - name: Upload the one complete Pages artifact",
            1,
        )
        self.assertEqual(late_stage.count(stage), 1)
        self.assertIn("ownership stage order", workflow_contract_findings(late_stage, real_release, lean))

    def test_reusable_release_identity_accepts_caller_push_event(self) -> None:
        pages = (REPO_ROOT / ".github/workflows/pages.yml").read_text(encoding="utf-8")
        block = pages.split("      - name: Resolve and verify the invocation-specific source identity", 1)[1]
        script = block.split("        run: |\n", 1)[1].split("      - name:", 1)[0]
        lines = script.splitlines()
        script = "\n".join(line[10:] for line in lines) + "\n"
        with tempfile.TemporaryDirectory(prefix="pages-release-event-") as raw:
            repo = Path(raw)
            subprocess.run(["git", "init", "-q"], cwd=repo, check=True)
            subprocess.run(["git", "config", "user.email", "verify@example.invalid"], cwd=repo, check=True)
            subprocess.run(["git", "config", "user.name", "verify"], cwd=repo, check=True)
            (repo / "file").write_text("x", encoding="utf-8")
            subprocess.run(["git", "add", "--", "file"], cwd=repo, check=True)
            subprocess.run(["git", "commit", "-qm", "source"], cwd=repo, check=True)
            sha = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=repo, text=True).strip()
            subprocess.run(["git", "tag", "v-test"], cwd=repo, check=True)
            output = repo / "output"
            env = dict(os.environ, EVENT_NAME="push", INVOCATION_KIND="release", MODE="",
                       RELEASE_DEPLOY="true", RUN_REF="refs/heads/main", SOURCE_REF="refs/tags/v-test",
                       SOURCE_SHA=sha, GITHUB_OUTPUT=str(output))
            subprocess.run(["bash", "-eu", "-o", "pipefail", "-c", script], cwd=repo, env=env, check=True)
            emitted = output.read_text(encoding="utf-8")
            self.assertIn(f"source-sha={sha}\n", emitted)
            self.assertIn("deploy=true\n", emitted)

    def test_zero_before_multi_commit_release_is_current_and_mismatches_fail(self) -> None:
        release = (REPO_ROOT / ".github/workflows/create-release.yml").read_text(encoding="utf-8")
        prepare = workflow_run_script(release, "Derive the intended tag and require it to be absent")
        write = workflow_run_script(release, "Create the initial annotated tag and release without a null revision range")
        resolve = workflow_run_script(release, "Resolve the exact release tag and peeled source commit")
        zero = "0" * 40
        with tempfile.TemporaryDirectory(prefix="pages-zero-release-") as raw:
            root = Path(raw)
            origin = root / "origin.git"
            repo = root / "repo"
            subprocess.run(["git", "init", "--bare", "-q", str(origin)], check=True)
            subprocess.run(["git", "init", "-q", "-b", "main", str(repo)], check=True)
            subprocess.run(["git", "config", "user.email", "verify@example.invalid"], cwd=repo, check=True)
            subprocess.run(["git", "config", "user.name", "verify"], cwd=repo, check=True)
            subprocess.run(["git", "remote", "add", "origin", str(origin)], cwd=repo, check=True)
            (repo / "lean-toolchain").write_text("leanprover/lean4:v4.99-test\n", encoding="utf-8")
            subprocess.run(["git", "add", "lean-toolchain"], cwd=repo, check=True)
            subprocess.run(["git", "commit", "-qm", "toolchain"], cwd=repo, check=True)
            (repo / "history").write_text("same toolchain\n", encoding="utf-8")
            subprocess.run(["git", "add", "history"], cwd=repo, check=True)
            subprocess.run(["git", "commit", "-qm", "later snapshot"], cwd=repo, check=True)
            after = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=repo, text=True).strip()
            subprocess.run(["git", "push", "-q", "-u", "origin", "main"], cwd=repo, check=True)
            prepare_output = root / "prepare-output"
            base_env = dict(os.environ, EVENT_NAME="push", PUSH_REF="refs/heads/main", PUSH_SHA=after,
                            GITHUB_OUTPUT=str(prepare_output))
            subprocess.run(["bash", "-eu", "-o", "pipefail", "-c", prepare], cwd=repo, env=base_env, check=True)
            emitted = dict(line.split("=", 1) for line in prepare_output.read_text().splitlines())
            self.assertEqual(emitted, {"source-ref": "refs/tags/v4.99-test", "toolchain": "leanprover/lean4:v4.99-test"})

            fake_bin = root / "bin"
            fake_bin.mkdir()
            fake_gh = fake_bin / "gh"
            fake_gh.write_text(
                "#!/bin/bash\nset -euo pipefail\n"
                "if [[ \"$*\" == *'/git/tags'* ]]; then\n"
                "  tag=; object=; for arg in \"$@\"; do case \"$arg\" in tag=*) tag=${arg#tag=};; object=*) object=${arg#object=};; esac; done\n"
                "  git tag -a \"$tag\" -m \"Release $tag\" \"$object\"; git rev-parse \"refs/tags/$tag\"\n"
                "elif [[ \"$*\" == *'/git/refs'* ]]; then\n"
                "  ref=; sha=; for arg in \"$@\"; do case \"$arg\" in ref=*) ref=${arg#ref=};; sha=*) sha=${arg#sha=};; esac; done\n"
                "  git push -q origin \"$sha:$ref\"\n"
                "elif [[ \"$*\" == *'/releases'* ]]; then exit 0; else exit 1; fi\n",
                encoding="utf-8",
            )
            fake_gh.chmod(0o755)
            write_env = dict(os.environ, PATH=str(fake_bin) + os.pathsep + os.environ["PATH"], GH_TOKEN="token",
                             REPOSITORY="owner/repo", SOURCE_REF=emitted["source-ref"], SOURCE_SHA=after)
            subprocess.run(["bash", "-eu", "-o", "pipefail", "-c", write], cwd=repo, env=write_env, check=True)
            self.assertEqual(subprocess.check_output(["git", "cat-file", "-t", "refs/tags/v4.99-test"], cwd=repo, text=True).strip(), "tag")

            def resolve_run(expected_ref=emitted["source-ref"], expected_toolchain=emitted["toolchain"], expected_after=after):
                output = root / f"resolve-{uuid.uuid4().hex}"
                env = dict(os.environ, BEFORE=zero, AFTER=expected_after, EXPECTED_REF=expected_ref,
                           EXPECTED_TOOLCHAIN=expected_toolchain, GITHUB_OUTPUT=str(output))
                proc = subprocess.run(["bash", "-eu", "-o", "pipefail", "-c", resolve], cwd=repo, env=env)
                return proc, output

            passed, output = resolve_run()
            self.assertEqual(passed.returncode, 0)
            resolved = dict(line.split("=", 1) for line in output.read_text().splitlines())
            self.assertEqual(resolved, {"publish": "true", "source-ref": "refs/tags/v4.99-test", "source-sha": after})
            self.assertNotEqual(resolve_run(expected_toolchain="leanprover/lean4:v-wrong")[0].returncode, 0)
            self.assertNotEqual(resolve_run(expected_ref="refs/tags/v-wrong")[0].returncode, 0)
            older = subprocess.check_output(["git", "rev-parse", "HEAD^"], cwd=repo, text=True).strip()
            self.assertNotEqual(resolve_run(expected_after=older)[0].returncode, 0)


def run_suite() -> int:
    result = unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromModule(sys.modules[__name__]))
    return 0 if result.wasSuccessful() else 1


if __name__ == "__main__":
    sys.exit(run_suite())

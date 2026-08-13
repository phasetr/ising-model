#!/usr/bin/env python3
"""Hermetic tests for the derived handwritten-Pages verifier."""

from __future__ import annotations

import importlib.util
import json
import shutil
import sys
import tempfile
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
        (self.source / "index.md").write_text("# Home\n", encoding="utf-8")
        (self.source / "nested" / "status.md").write_text("# Status\n", encoding="utf-8")
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
        manifest["files"][0]["path"] = "../outside"
        manifest_path.write_text(json.dumps(manifest), encoding="utf-8")
        with mock.patch.object(checker, "_fetch", side_effect=fetch):
            findings = checker.check_live("https://example.test/ising-model/", self.source, "/ising-model", self.revision, self.generated)
        self.assertEqual([item.code for item in findings], ["MANIFEST"])


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


class WorkflowContractTest(unittest.TestCase):
    def test_single_writer_triggers_pins_permissions_and_release_call(self) -> None:
        pages = (REPO_ROOT / ".github/workflows/pages.yml").read_text(encoding="utf-8")
        release = (REPO_ROOT / ".github/workflows/create-release.yml").read_text(encoding="utf-8")
        lean = (REPO_ROOT / ".github/workflows/lean_action_ci.yml").read_text(encoding="utf-8")
        self.assertIn("workflow_dispatch:", pages)
        self.assertIn("workflow_call:", pages)
        self.assertNotIn("\n  push:", pages)
        self.assertNotIn("schedule:", pages)
        self.assertNotIn("docgen", pages.lower())
        self.assertEqual(pages.count("actions/deploy-pages@"), 1)
        self.assertIn("cancel-in-progress: false", pages)
        for sha in checker.ACTION_SHAS:
            self.assertIn(sha, pages + release)
        self.assertIn("uses: ./.github/workflows/pages.yml", release)
        self.assertIn("needs: lean-release-tag", release)
        self.assertIn("git tag --points-at", release)
        self.assertIn("source_sha=$(git rev-parse", release)
        self.assertNotIn("pages: write", lean)
        self.assertNotIn("id-token: write", lean)
        self.assertNotIn("docgen-action", lean)
        self.assertIn("python3 scripts/test_pages_site_check.py", lean)
        self.assertEqual((REPO_ROOT / "README.md").read_text().count("Derived handwritten Pages snapshot"), 1)


def run_suite() -> int:
    result = unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromModule(sys.modules[__name__]))
    return 0 if result.wasSuccessful() else 1


if __name__ == "__main__":
    sys.exit(run_suite())

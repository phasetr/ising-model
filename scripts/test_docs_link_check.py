#!/usr/bin/env python3
"""Tests for the bounded tracked-Markdown link checker."""

from __future__ import annotations

import contextlib
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import docs_link_check as checker  # noqa: E402


class RepoTest(unittest.TestCase):
    """Materialize a tracked repository and exercise the public check entry."""

    def setUp(self) -> None:
        self.raw = tempfile.mkdtemp(prefix="docs-links-")
        self.addCleanup(shutil.rmtree, self.raw, True)
        self.root = Path(self.raw)
        subprocess.run(["git", "init", "-q"], cwd=self.root, check=True)

    def write(self, files: dict[str, str | bytes], *, stage: bool = True) -> None:
        """Write fixture files and optionally stage the complete tree."""
        for name, content in files.items():
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(content) if isinstance(content, bytes) else path.write_text(content, encoding="utf-8")
        if stage:
            subprocess.run(["git", "add", "-A"], cwd=self.root, check=True)

    def base(self, extra: dict[str, str | bytes] | None = None) -> None:
        """Write the minimum clean reachable graph."""
        owners = {owner: f"# {Path(owner).stem}\n" for owner in checker.CANONICAL_OWNERS}
        landing_links = "\n".join(f"[{owner}]({owner.removeprefix('docs/')})" for owner in sorted(owners))
        files: dict[str, str | bytes] = {
            "README.md": "[Documentation](docs/index.md)\n",
            "docs/index.md": landing_links + "\n",
            **owners,
        }
        files.update(extra or {})
        self.write(files)

    def codes(self) -> list[str]:
        return [finding.code for finding in checker.check(self.root)[0]]


class ResolutionTest(RepoTest):
    def test_clean_md_nested_static_fragment_image_and_external_pass(self) -> None:
        self.base({
            "docs/asset.png": b"png",
            "docs/status.md": "# Same\n# Same\n![asset](asset.png)\n[second](#same-1)\n[web](https://example.test/page.html)\n",
        })
        self.assertEqual(self.codes(), [])

    def test_local_html_is_rejected_but_external_html_and_fenced_examples_are_not(self) -> None:
        self.base({"docs/status.md": "[bad](missing.html)\n[web](https://example.test/a.html)\n```md\n[fake](missing.html)\n```\n"})
        findings = checker.check(self.root)[0]
        self.assertEqual([item.code for item in findings], ["LOCAL_HTML"])
        self.assertEqual(findings[0].destination, "missing.html")

    def test_missing_wrong_case_fragment_image_and_escape_fail(self) -> None:
        self.base({"docs/status.md": "[missing](none.md)\n[case](Index.md)\n[fragment](index.md#absent)\n![image](none.png)\n[escape](../../outside.md)\n"})
        codes = self.codes()
        self.assertEqual(codes.count("MISSING_TARGET"), 3)
        self.assertIn("MISSING_FRAGMENT", codes)
        self.assertIn("PATH_ESCAPE", codes)

    def test_present_but_untracked_target_fails(self) -> None:
        self.base()
        self.write({"docs/untracked.md": "# untracked\n"}, stage=False)
        with (self.root / "docs/status.md").open("a", encoding="utf-8") as stream:
            stream.write("[untracked](untracked.md)\n")
        self.assertIn("MISSING_TARGET", self.codes())

    def test_reference_link_is_checked_and_inline_code_is_ignored(self) -> None:
        self.base({"docs/status.md": "[missing][owner]\n[owner]: missing.md\n`[fake](also-missing.md)`\n"})
        findings = checker.check(self.root)[0]
        self.assertEqual([item.destination for item in findings if item.code == "MISSING_TARGET"], ["missing.md"])

    def test_unclosed_fence_and_code_span_fail_closed(self) -> None:
        self.base({"docs/status.md": "`unclosed\n~~~md\n[fake](none.md)\n"})
        codes = self.codes()
        self.assertIn("MALFORMED_CODE_SPAN", codes)
        self.assertIn("MALFORMED_FENCE", codes)

    def test_readme_and_each_landing_owner_are_required(self) -> None:
        self.base()
        (self.root / "README.md").write_text("no link\n", encoding="utf-8")
        (self.root / "docs/index.md").write_text("[status](status.md)\n", encoding="utf-8")
        codes = self.codes()
        self.assertEqual(codes.count("README_REACHABILITY"), 1)
        self.assertEqual(codes.count("OWNER_REACHABILITY"), len(checker.CANONICAL_OWNERS) - 1)


class ParserTest(unittest.TestCase):
    def test_reference_definition_and_use_are_extracted(self) -> None:
        links, definitions, findings, _ = checker.parse_markdown("docs/a.md", "[x][id]\n[id]: b.md\n")
        self.assertEqual(links, [])
        self.assertEqual(definitions["id"].destination, "b.md")
        self.assertEqual(findings, [])

    def test_missing_reference_definition_fails(self) -> None:
        findings = checker.parse_markdown("docs/a.md", "[x][missing]\n")[2]
        self.assertEqual([item.code for item in findings], ["MISSING_REFERENCE"])


class RealTreeTest(unittest.TestCase):
    def test_the_delivered_tree_is_clean_and_nonvacuous(self) -> None:
        findings, visited, links = checker.check()
        self.assertEqual(findings, [])
        self.assertIn("docs/index.md", visited)
        self.assertIn("docs/completion-claims.md", visited)
        self.assertIn("docs/refactoring-rollback-ledger.md", visited)
        self.assertIn("docs/source-coverage-high-temperature.md", visited)
        self.assertGreater(len(links), 76)


def run_suite() -> int:
    suite = unittest.defaultTestLoader.loadTestsFromModule(sys.modules[__name__])
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    return 0 if result.wasSuccessful() else 1


if __name__ == "__main__":
    sys.exit(run_suite())

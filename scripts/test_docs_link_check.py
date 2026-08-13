#!/usr/bin/env python3
"""Hermetic and mutation tests for the tracked-Markdown link checker."""

from __future__ import annotations

import importlib.util
import shutil
import subprocess
import sys
import tempfile
import types
import unittest
import uuid
from collections import Counter
from contextlib import contextmanager
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
import docs_link_check as checker  # noqa: E402

CHECKER_PATH = Path(checker.__file__).resolve()


class RepoTest(unittest.TestCase):
    """Materialize a tracked repository and exercise the public entry points."""

    def setUp(self) -> None:
        self.raw = tempfile.mkdtemp(prefix="docs-links-")
        self.addCleanup(shutil.rmtree, self.raw, True)
        self.root = Path(self.raw)
        subprocess.run(["git", "init", "-q"], cwd=self.root, check=True)

    def write(self, files: dict[str, str | bytes], *, stage: bool = True) -> None:
        for name, content in files.items():
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(content) if isinstance(content, bytes) else path.write_text(content, encoding="utf-8")
        if stage and files:
            subprocess.run(["git", "add", "--", *sorted(files)], cwd=self.root, check=True)

    def base(self, extra: dict[str, str | bytes] | None = None) -> None:
        owners = {owner: f"# {Path(owner).stem}\n" for owner in checker.CANONICAL_OWNERS}
        landing = "\n".join(f"[{owner}]({owner.removeprefix('docs/')})" for owner in sorted(owners))
        files: dict[str, str | bytes] = {
            "README.md": "[Documentation](docs/index.md)\n",
            "docs/index.md": landing + "\n",
            **owners,
        }
        files.update(extra or {})
        self.write(files)

    def findings(self, module: types.ModuleType = checker) -> list[checker.Finding]:
        return module.check(self.root)[0]

    def codes(self, module: types.ModuleType = checker) -> list[str]:
        return [finding.code for finding in self.findings(module)]

    def cli(self) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [sys.executable, str(CHECKER_PATH), "--check", "--root", str(self.root)],
            cwd=Path(tempfile.gettempdir()), text=True, capture_output=True, check=False,
        )


class ResolutionTest(RepoTest):
    def test_empty_tracked_scope_fails_end_to_end(self) -> None:
        self.write({"notes.txt": "outside scope\n"})
        proc = self.cli()
        self.assertNotEqual(proc.returncode, 0)
        self.assertIn("TRACKED_SET", proc.stdout)

    def test_clean_nested_static_image_external_fragment_and_cli_pass(self) -> None:
        self.base({
            "docs/asset.png": b"png",
            "docs/status.md": "# Same\n# Same\n![asset](asset.png)\n[second](#same-1)\n[web](https://example.test/page.html)\n",
        })
        self.assertEqual(self.codes(), [])
        proc = self.cli()
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)

    def test_local_html_is_rejected_end_to_end(self) -> None:
        self.base({"docs/status.md": "[bad](missing.html)\n[web](https://example.test/a.html)\n```md\n[fake](missing.html)\n```\n"})
        proc = self.cli()
        self.assertNotEqual(proc.returncode, 0)
        self.assertIn("LOCAL_HTML", proc.stdout)
        self.assertEqual([x.destination for x in self.findings() if x.code == "LOCAL_HTML"], ["missing.html"])

    def test_missing_wrong_case_fragment_image_and_escape_fail(self) -> None:
        self.base({"docs/status.md": "[missing](none.md)\n[case](Index.md)\n[fragment](index.md#absent)\n![image](none.png)\n[escape](../../outside.md)\n"})
        codes = self.codes()
        self.assertEqual(codes.count("MISSING_TARGET"), 3)
        self.assertIn("MISSING_FRAGMENT", codes)
        self.assertIn("PATH_ESCAPE", codes)

    def test_query_backslash_root_absolute_and_empty_alt_fail(self) -> None:
        self.base({"docs/asset.png": b"png", "docs/status.md": "[q](index.md?q=1)\n[b](..\\README.md)\n[r](/README.md)\n![](asset.png)\n"})
        codes = self.codes()
        for code in ("QUERY_NOT_ALLOWED", "BACKSLASH_PATH", "ROOT_ABSOLUTE_PATH", "EMPTY_IMAGE_ALT"):
            self.assertIn(code, codes)

    def test_present_but_untracked_target_fails(self) -> None:
        self.base({"docs/status.md": "[untracked](untracked.md)\n"})
        self.write({"docs/untracked.md": "# untracked\n"}, stage=False)
        self.assertIn("MISSING_TARGET", self.codes())

    def test_raw_html_liquid_and_malformed_inline_fail_closed(self) -> None:
        self.base({"docs/status.md": '<a href="missing.md">bad</a>\n<img src=asset.png>\n<a href="https://example.test/a.md">external</a>\n{% link missing.md %}\nbroken ](missing.md)\n[x][missing.md\n'})
        codes = self.codes()
        self.assertEqual(codes.count("RAW_LOCAL_HTML"), 2)
        self.assertIn("LIQUID_LOCAL_LINK", codes)
        self.assertIn("UNPARSED_LOCAL_LINK", codes)
        self.assertIn("CANDIDATE_COVERAGE", codes)

    def test_extensionless_raw_html_and_liquid_destinations_fail(self) -> None:
        self.base({"docs/status.md": '<a href="LICENSE">license</a>\n{% link LICENSE %}\n'})
        codes = self.codes()
        self.assertIn("RAW_LOCAL_HTML", codes)
        self.assertIn("LIQUID_LOCAL_LINK", codes)

    def test_raw_fragment_destinations_are_candidates_and_are_validated(self) -> None:
        self.base({
            "docs/status.md": (
                '# Present\n'
                '<a href="#present">present</a>\n'
                '<a href="#missing-html">missing</a>\n'
                '{% link #missing-liquid %}\n'
            ),
        })
        findings = self.findings()
        codes = [item.code for item in findings]
        self.assertIn("RAW_LOCAL_HTML", codes)
        self.assertIn("LIQUID_LOCAL_LINK", codes)
        self.assertEqual(codes.count("MISSING_FRAGMENT"), 2)
        self.assertFalse(any(item.code == "MISSING_FRAGMENT" and item.destination == "#present" for item in findings))

    def test_comments_titles_and_tilde_info_are_handled_as_markdown(self) -> None:
        self.base({
            "docs/status.md": (
                '<!-- [fake](missing.md) <a href="LICENSE"> -->\n'
                '<!--\n~~~not-a-fence\n{% link LICENSE %}\n-->\n'
                '<!-- hidden --> [after](index.md)\n'
                '[title](index.md "optional title")\n'
                "~~~language~variant\n[fenced](missing.md)\n~~~\n"
            ),
        })
        self.assertEqual(self.codes(), [])

    def test_escaped_and_code_comment_openers_cannot_hide_following_links(self) -> None:
        self.base({
            "docs/status.md": (
                '\\<!-- escaped literal\n'
                '`<!--` code literal\n'
                '\\\\<!-- real comment -->\n'
                '[first](missing-one.md)\n'
                '[second](missing-two.md)\n'
            ),
        })
        self.assertEqual(self.codes().count("MISSING_TARGET"), 2)
        self.assertNotIn("MALFORMED_HTML_COMMENT", self.codes())

    def test_unclosed_html_comment_fails_closed(self) -> None:
        self.base({"docs/status.md": "<!-- open\n[hidden](missing.md)\n"})
        self.assertIn("MALFORMED_HTML_COMMENT", self.codes())

    def test_fragment_on_tracked_markdown_outside_scope_is_loaded(self) -> None:
        self.base({
            "CONTRIBUTING.md": "# Setup\n",
            "docs/status.md": "[contributor setup](../CONTRIBUTING.md#setup)\n",
        })
        findings, visited, _links = checker.check(self.root)
        self.assertEqual(findings, [])
        self.assertNotIn("CONTRIBUTING.md", visited)

    def test_empty_reference_image_alt_and_non_utf8_markdown_fail(self) -> None:
        self.base({"docs/asset.png": b"png", "docs/status.md": "![][asset]\n[asset]: asset.png\n", "docs/binary.md": b"\xff"})
        codes = self.codes()
        self.assertIn("EMPTY_IMAGE_ALT", codes)
        self.assertIn("UNREADABLE", codes)

    def test_empty_and_unclosed_inline_and_image_constructs_fail(self) -> None:
        self.base({"docs/status.md": "![]()\n![alt](\n[x](\n"})
        codes = self.codes()
        self.assertIn("EMPTY_IMAGE_ALT", codes)
        self.assertIn("MISSING_TARGET", codes)
        self.assertEqual(codes.count("UNPARSED_LOCAL_LINK"), 2)
        self.assertIn("CANDIDATE_COVERAGE", codes)

    def test_multiline_raw_html_and_liquid_links_fail_coverage(self) -> None:
        self.base({
            "docs/status.md": (
                '<a\n href = "missing.md">broken</a>\n'
                '<img\n src=asset.png>\n'
                '{% link\n missing.md %}\n'
                '{%\n link another.md %}\n'
            ),
        })
        codes = self.codes()
        self.assertEqual(codes.count("RAW_LOCAL_HTML"), 2)
        self.assertEqual(codes.count("LIQUID_LOCAL_LINK"), 2)
        self.assertIn("CANDIDATE_COVERAGE", codes)

    def test_reference_use_is_edge_but_unused_local_definition_is_not(self) -> None:
        self.base({"README.md": "[landing]: docs/index.md\n", "docs/status.md": "[missing][owner]\n[owner]: missing.md\n[unused]: index.md\n[external]: https://example.test/\n"})
        codes = self.codes()
        self.assertIn("README_REACHABILITY", codes)
        self.assertIn("MISSING_TARGET", codes)
        self.assertIn("UNUSED_LOCAL_REFERENCE", codes)
        self.assertNotIn("external", " ".join(x.destination for x in self.findings()))

    def test_unused_owner_definitions_do_not_fake_landing_reachability(self) -> None:
        owners = "\n".join(f"[x]: {owner.removeprefix('docs/')}" for owner in sorted(checker.CANONICAL_OWNERS))
        self.base({"docs/index.md": owners + "\n"})
        self.assertEqual(self.codes().count("OWNER_REACHABILITY"), len(checker.CANONICAL_OWNERS))

    def test_strict_fence_close_keeps_following_example_masked(self) -> None:
        self.base({"docs/status.md": "~~~md\n~~~not-a-close\n[still fake](missing.md)\n~~~   \n"})
        self.assertEqual(self.codes(), [])

    def test_heading_rendered_label_and_explicit_anchors(self) -> None:
        self.base({"docs/status.md": "## [Setup](index.md)\n<a id=\"stable\"></a>\n<a name='legacy'></a>\n[to setup](#setup)\n[to stable](#stable)\n[to legacy](#legacy)\n"})
        self.assertEqual(self.codes(), [])

    def test_duplicate_explicit_and_generated_anchors_fail(self) -> None:
        self.base({"docs/status.md": "# Stable\n<a id=\"stable\"></a>\n<a name=\"other\"></a>\n<a id=\"other\"></a>\n"})
        self.assertEqual(self.codes().count("DUPLICATE_ANCHOR"), 2)

    def test_unclosed_fence_and_code_span_fail_closed(self) -> None:
        self.base({"docs/status.md": "`unclosed\n~~~md\n[fake](none.md)\n"})
        codes = self.codes()
        self.assertIn("MALFORMED_CODE_SPAN", codes)
        self.assertIn("MALFORMED_FENCE", codes)


class TrackedSetFailureTest(unittest.TestCase):
    def fake(self, *, returncode: int = 0, stdout: bytes = b"a\0", stderr: bytes = b"") -> mock.Mock:
        return mock.Mock(returncode=returncode, stdout=stdout, stderr=stderr)

    def test_git_oserror_nonzero_nonutf8_and_empty_are_stable_findings(self) -> None:
        cases = [
            (OSError("missing"), None, "could not run git"),
            (None, self.fake(returncode=2, stderr=b"bad"), "git ls-files failed"),
            (None, self.fake(stdout=b"\xff\0"), "non-UTF-8 path"),
            (None, self.fake(stdout=b""), "empty tracked set"),
        ]
        for error, result, detail in cases:
            with self.subTest(detail=detail):
                effect = error if error else None
                with mock.patch.object(checker.subprocess, "run", side_effect=effect, return_value=result):
                    names, findings = checker._git_names(Path("."), None)
                self.assertEqual(names, [])
                self.assertEqual([x.code for x in findings], ["TRACKED_SET"])
                self.assertIn(detail, findings[0].detail)


@contextmanager
def mutant(old: str, new: str):
    source = CHECKER_PATH.read_text(encoding="utf-8")
    count = source.count(old)
    if count != 1:
        raise AssertionError(f"mutation replacement count is {count}, expected exactly 1: {old!r}")
    with tempfile.TemporaryDirectory(prefix="docs-link-mutant-") as raw:
        path = Path(raw) / "docs_link_check.py"
        path.write_text(source.replace(old, new), encoding="utf-8")
        name = f"docs_link_mutant_{uuid.uuid4().hex}"
        spec = importlib.util.spec_from_file_location(name, path)
        assert spec and spec.loader
        module = importlib.util.module_from_spec(spec)
        sys.modules[name] = module
        try:
            spec.loader.exec_module(module)
            yield module
        finally:
            sys.modules.pop(name, None)


class MutationTest(RepoTest):
    def test_independent_census_kills_scope_shrink(self) -> None:
        self.base({"docs/extra.md": "# Extra\n"})
        with mutant('MARKDOWN_PATHS = ("README.md", "docs")', 'MARKDOWN_PATHS = ("README.md",)') as module:
            self.assertIn("SCOPE_MISMATCH", self.codes(module))

    def test_candidate_identity_blocks_cross_offset_laundering(self) -> None:
        text = "[broken]: missing.md trailing\n[x](<https://example.test/a b>)\n"
        self.base({"docs/status.md": text})
        self.assertIn("CANDIDATE_COVERAGE", self.codes())
        parsed = checker.parse_markdown("docs/status.md", text)
        self.assertEqual(parsed.candidate_count, parsed.consumed_count)
        self.assertNotEqual(Counter(parsed.candidate_identities), Counter(parsed.consumed_identities))
        with mutant(
            "if Counter(candidate_identities) != Counter(consumed_identities):",
            "if len(candidate_identities) != len(consumed_identities):",
        ) as module:
            self.assertEqual(self.codes(module), [])

    def test_raw_fragment_and_comment_lifecycle_guards_are_nonvacuous(self) -> None:
        cases = [
            (
                'return bool(destination) and not _external(destination)',
                'return bool(destination) and not _external(destination) and not destination.startswith("#")',
                '<a href="#missing">missing</a>\n',
                "RAW_LOCAL_HTML",
            ),
            (
                'if slash_count % 2 == 1:',
                'if False:',
                '\\<!-- literal\n[broken](missing.md)\n',
                "MISSING_TARGET",
            ),
            (
                'if line[pos] == "`":',
                'if False:',
                '`<!--` literal\n[broken](missing.md)\n',
                "MISSING_TARGET",
            ),
            (
                'if html_comment:',
                'if False:',
                '<!-- open\n[hidden](missing.md)\n',
                "MALFORMED_HTML_COMMENT",
            ),
        ]
        for old, new, text, guarded_code in cases:
            with self.subTest(guard=guarded_code, old=old):
                self.base({"docs/status.md": text})
                self.assertIn(guarded_code, self.codes())
                with mutant(old, new) as module:
                    self.assertNotIn(guarded_code, self.codes(module))

    def test_punctuation_and_multiline_raw_guards_are_nonvacuous(self) -> None:
        cases = [
            (
                'if match.start() not in raw_positions and match.start() not in parsed_positions',
                'if False',
                "![alt](\n",
                "CANDIDATE_COVERAGE",
            ),
            (
                'if "\\n" not in match.group(0):',
                'if True:',
                '<a\n href="missing.md">broken</a>\n',
                "RAW_LOCAL_HTML",
            ),
        ]
        for old, new, text, guarded_code in cases:
            with self.subTest(guard=guarded_code):
                self.base({"docs/status.md": text})
                self.assertIn(guarded_code, self.codes())
                with mutant(old, new) as module:
                    self.assertNotIn(guarded_code, self.codes(module))

    def test_query_backslash_and_root_guards_are_each_nonvacuous(self) -> None:
        cases = [
            ('if parsed_url.query:', 'if False:', "[x](index.md?q=1)\n", {}, "QUERY_NOT_ALLOWED"),
            ('if "\\\\" in destination:', 'if False:', "[x](back\\\\slash.md)\n", {"docs/back\\slash.md": "# target\n"}, "BACKSLASH_PATH"),
            ('if parsed_url.path.startswith("/"):', 'if False:', "[x](/docs/status.md)\n", {}, "ROOT_ABSOLUTE_PATH"),
        ]
        for old, new, link, targets, guarded_code in cases:
            with self.subTest(old=old):
                self.base({"docs/status.md": link, **targets})
                self.assertIn(guarded_code, self.codes())
                with mutant(old, new) as module:
                    self.assertNotIn(guarded_code, self.codes(module))


class RealTreeTest(unittest.TestCase):
    def test_delivered_tree_census_is_exact_and_clean(self) -> None:
        findings, visited, links = checker.check()
        self.assertEqual(findings, [])
        local = [link for link in links if link.destination and not checker._external(link.destination)]
        fragments = [link for link in local if "#" in link.destination]
        self.assertEqual(len(visited), 21)
        self.assertEqual(len(local), 79)
        self.assertEqual(len(fragments), 2)
        self.assertEqual(visited, checker.raw_tracked_markdown()[0])


def run_suite() -> int:
    suite = unittest.defaultTestLoader.loadTestsFromModule(sys.modules[__name__])
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    return 0 if result.wasSuccessful() else 1


if __name__ == "__main__":
    sys.exit(run_suite())

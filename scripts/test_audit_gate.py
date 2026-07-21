#!/usr/bin/env python3
"""Tests for ``scripts/audit_gate.py`` (V1-V4).

Run directly (``python3 scripts/test_audit_gate.py``) or through the gate's own
``--self-test`` flag. V1-V4 are the repository's correctness gate -- they decide
whether a push is honest -- and until this suite existed nothing checked *them*.
That is the same hole the dead-candidate scanner had when it passed three false
``safe-to-delete`` verdicts.

What makes a gate test worth having
-----------------------------------
A test that only asserts "the current tree passes" is nearly worthless: it stays
green when a check is quietly weakened, which is the realistic failure mode (a
regex relaxed to silence a false positive, an allowlist widened, a range dropped
from a character class, a ``continue`` added to an exception handler). So every
check here is tested in two directions:

1. **Fixture direction** -- a hand-built input with a known verdict, so the check
   is pinned against material independent of the repository's current state.
2. **Mutation direction** (:class:`MutationTest`) -- ``audit_gate.py``'s source is
   loaded with a surgical weakening applied (regex relaxed, token tuple trimmed,
   allowlist widened, Unicode range removed, fail-closed handler turned into a
   skip) and the mutant is required to *miss* what the real gate catches. Each
   mutation is paired with the fixture test that would fail if a developer made
   that edit for real, so the suite demonstrably detects weakening rather than
   merely passing.

Cost
----
V1, V2 and V4 are pure Python and run against fixtures plus one shared pass over
the real tree (cached in :func:`real_tree_results`, about five seconds total).

V3 shells out to ``lake env lean``, which needs the whole library's oleans and
costs minutes -- unacceptable in a suite meant to run on every edit. V3 is
therefore tested hermetically: its pure parts (``read_capstones``,
``parse_axioms_output``, the subset decision, the unknown-identifier hard
failure, the empty-list guard) are exercised with a stubbed ``lake env lean``
whose canned output covers the cases that matter, plus a cheap real-tree honesty
check that every capstone name at least exists as a declaration in the library.
The genuine end-to-end V3 runs where it belongs: CI's
``python3 scripts/audit_gate.py --full``. Set ``AUDIT_GATE_LIVE_V3=1`` to opt
into the live check locally.

Note on this file's own text: V4 scans ``scripts/``, so every Japanese sample
below is built with ``chr()`` instead of being written literally. A test suite
that made its own gate fail would be self-defeating.
"""

from __future__ import annotations

import os
import subprocess
import sys
import tempfile
import types
import unittest
from contextlib import contextmanager
from pathlib import Path
from typing import Iterator

sys.path.insert(0, str(Path(__file__).resolve().parent))

import audit_gate as ag  # noqa: E402  (path bootstrap first)

AUDIT_GATE_PATH = Path(ag.__file__).resolve()

# Sample characters, built from codepoints (see the module docstring).
HIRAGANA_A = chr(0x3042)  # U+3042
KATAKANA_A = chr(0x30A2)  # U+30A2
KANJI = chr(0x6F22)  # U+6F22, CJK unified ideographs
IDEOGRAPHIC_SPACE = chr(0x3000)  # U+3000, invisible rewrite residue
IDEOGRAPHIC_COMMA = chr(0x3001)  # U+3001
KANGXI_RADICAL = chr(0x2F00)  # U+2F00, Kangxi radical one
SQUARED_ERA_NAME = chr(0x337B)  # U+337B, squared era name (CJK compatibility)
PARENTHESIZED_IDEOGRAPH = chr(0x3231)  # U+3231, enclosed CJK
VERTICAL_COMMA = chr(0xFE10)  # U+FE10, vertical forms
CJK_COMPAT_FORM = chr(0xFE30)  # U+FE30, CJK compatibility forms
HALFWIDTH_KATAKANA = chr(0xFF71)  # U+FF71
EXT_A_IDEOGRAPH = chr(0x3401)  # U+3401
EXT_B_IDEOGRAPH = chr(0x20001)  # U+20001
IVS_SELECTOR = chr(0xE0100)  # U+E0100, ideographic variation selector
EMOJI_SELECTOR = chr(0xFE0F)  # U+FE0F, deliberately NOT in the class

_REAL: tuple[list[str], list[str], list[str], int] | None = None


def real_tree_results() -> tuple[list[str], list[str], list[str], int]:
    """Return ``(v1, v2, v4, files)`` for the real tree, computed at most once.

    V1 and V2 each re-scan every library file through the character-at-a-time
    ``strip_noncode``, so the whole suite shares one pass.
    """
    global _REAL
    if _REAL is None:
        v4, scanned = ag.check_v4()
        _REAL = (ag.check_v1(), ag.check_v2(), v4, scanned)
    return _REAL


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


@contextmanager
def patched(module: types.ModuleType, **attrs: object) -> Iterator[None]:
    """Temporarily set module attributes, restoring the originals afterwards."""
    saved = {name: getattr(module, name) for name in attrs}
    for name, value in attrs.items():
        setattr(module, name, value)
    try:
        yield
    finally:
        for name, value in saved.items():
            setattr(module, name, value)


@contextmanager
def library(files: dict[str, str], module: types.ModuleType | None = None) -> Iterator[Path]:
    """Build a throwaway ``IsingModel/`` tree and point V1/V2 at it.

    ``files`` maps a path relative to the library directory to its contents.
    """
    target = module if module is not None else ag
    with tempfile.TemporaryDirectory() as raw:
        root = Path(raw)
        lib = root / "IsingModel"
        for name, text in files.items():
            path = lib / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text, encoding="utf-8")
        with patched(target, REPO_ROOT=root, LIB_DIR=lib):
            yield root


@contextmanager
def tracked_repo(
    files: dict[str, str | bytes],
    paths: tuple[str, ...] = ("docs",),
    module: types.ModuleType | None = None,
    stage: bool = True,
) -> Iterator[Path]:
    """Build a throwaway git repository and point V4 at it.

    Files are staged (not committed): ``git ls-files`` reads the index, so
    staging is enough and keeps the fixture fast. ``stage=False`` leaves the
    files untracked, which is how the "untracked scratch never trips V4"
    expectation is tested.
    """
    target = module if module is not None else ag
    with tempfile.TemporaryDirectory() as raw:
        root = Path(raw)
        for name, content in files.items():
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            if isinstance(content, bytes):
                path.write_bytes(content)
            else:
                path.write_text(content, encoding="utf-8")
        subprocess.run(["git", "init", "-q"], cwd=root, check=True)
        if stage:
            subprocess.run(["git", "add", "-A"], cwd=root, check=True)
        with patched(target, REPO_ROOT=root, V4_PATHS=paths):
            yield root


class FakeProc:
    """Minimal stand-in for ``subprocess.CompletedProcess``."""

    def __init__(self, stdout: str = "", stderr: str = "", returncode: int = 0) -> None:
        self.stdout = stdout
        self.stderr = stderr
        self.returncode = returncode


@contextmanager
def stub_lean(stdout: str = "", stderr: str = "", returncode: int = 0) -> Iterator[dict]:
    """Replace ``lake env lean`` by canned output; yield the captured invocation.

    The captured dict holds the argv and the generated ``.lean`` source, read
    before ``check_v3`` deletes it, so tests can assert what was asked of Lean.
    """
    captured: dict[str, object] = {}
    real_run = subprocess.run

    def fake_run(cmd, **kwargs):  # type: ignore[no-untyped-def]
        if list(cmd[:3]) == ["lake", "env", "lean"]:
            captured["cmd"] = list(cmd)
            captured["source"] = Path(cmd[-1]).read_text(encoding="utf-8")
            return FakeProc(stdout, stderr, returncode)
        return real_run(cmd, **kwargs)

    with patched(subprocess, run=fake_run):
        yield captured


@contextmanager
def capstones(text: str, module: types.ModuleType | None = None) -> Iterator[Path]:
    """Point ``read_capstones`` at a throwaway capstone list."""
    target = module if module is not None else ag
    with tempfile.TemporaryDirectory() as raw:
        path = Path(raw) / "capstones.txt"
        path.write_text(text, encoding="utf-8")
        with patched(target, CAPSTONES_FILE=path):
            yield path


def load_mutated(*substitutions: tuple[str, str]) -> types.ModuleType:
    """Return ``audit_gate`` re-imported with textual weakenings applied.

    Each substitution must match exactly once in the source; a substitution that
    stops matching means the code it targeted moved, and the mutation test that
    used it has become vacuous, so this raises instead of silently applying
    nothing. ``__file__`` is kept pointing at the real script so ``REPO_ROOT``
    and friends resolve exactly as in production.
    """
    source = AUDIT_GATE_PATH.read_text(encoding="utf-8")
    for old, new in substitutions:
        count = source.count(old)
        if count != 1:
            raise AssertionError(
                f"mutation target matched {count} times, expected 1: {old!r}"
            )
        source = source.replace(old, new)
    module = types.ModuleType("audit_gate_mutant")
    module.__file__ = str(AUDIT_GATE_PATH)
    exec(compile(source, str(AUDIT_GATE_PATH), "exec"), module.__dict__)  # noqa: S102
    return module


def drop_range(low: int, high: int) -> tuple[str, str]:
    """Return a substitution removing one Unicode range from the V4 class."""
    line = f"    (0x{low:X}, 0x{high:X}),\n"
    return (line, "")


# ---------------------------------------------------------------------------
# Shared primitive: strip_noncode
# ---------------------------------------------------------------------------


class StripNoncodeTest(unittest.TestCase):
    """``strip_noncode`` is the primitive V1, V2 and the scanner all trust."""

    def test_line_comment_is_blanked(self) -> None:
        """Text after ``--`` cannot declare anything."""
        self.assertNotIn("axiom", ag.strip_noncode("def f := 1 -- axiom bad"))

    def test_block_comment_is_blanked(self) -> None:
        """Documentation prose is not code."""
        self.assertNotIn("sorry", ag.strip_noncode("/- proof by sorry -/\ndef f := 1"))

    def test_nested_block_comment_closes_once(self) -> None:
        """A nested ``/- -/`` must not end the outer comment early."""
        cleaned = ag.strip_noncode("/- a /- b -/ sorry -/\ntheorem t : True := trivial")
        self.assertNotIn("sorry", cleaned)
        self.assertIn("theorem t", cleaned)

    def test_string_body_is_blanked(self) -> None:
        """A token inside a string literal is data, not a proof step."""
        self.assertNotIn("sorry", ag.strip_noncode('def m := "sorry"'))

    def test_comment_opener_inside_string_does_not_open_a_comment(self) -> None:
        """The fail-open hole two independent passes would leave.

        ``def m := "/-"`` must not swallow the code that follows it; if it did,
        every ``sorry`` after such a line would become invisible to V2.
        """
        cleaned = ag.strip_noncode('def m := "/-"\ntheorem t : True := by sorry')
        self.assertIn("sorry", cleaned)

    def test_quote_inside_comment_does_not_open_a_string(self) -> None:
        """Symmetric case: an apostrophe-free ``"`` in prose is inert."""
        cleaned = ag.strip_noncode('-- say "hello\ntheorem t : True := by sorry')
        self.assertIn("sorry", cleaned)

    def test_escaped_quote_does_not_end_the_string(self) -> None:
        """``\\"`` is consumed as a unit, so the string keeps running."""
        cleaned = ag.strip_noncode('def m := "a\\"sorry"\ndef g := 1')
        self.assertNotIn("sorry", cleaned)
        self.assertIn("def g", cleaned)

    def test_line_numbering_is_preserved(self) -> None:
        """Blanking to spaces keeps diagnostics pointing at the right line."""
        source = '/- one\ntwo -/\ndef f := "a\nb"\ntheorem t : True := trivial\n'
        self.assertEqual(
            len(ag.strip_noncode(source).splitlines()), len(source.splitlines())
        )

    def test_column_numbering_is_preserved(self) -> None:
        """Every line keeps its width, so column offsets stay usable."""
        source = "def f := 1 -- trailing note\n"
        self.assertEqual(
            [len(line) for line in ag.strip_noncode(source).splitlines()],
            [len(line) for line in source.splitlines()],
        )

    def test_code_outside_constructs_is_untouched(self) -> None:
        """The transformation is identity on plain code."""
        source = "theorem t (n : Nat) : n = n := rfl\n"
        self.assertEqual(ag.strip_noncode(source), source)

    def test_unterminated_block_comment_swallows_the_rest(self) -> None:
        """Matching Lean: an unclosed ``/-`` really does comment out the file."""
        self.assertNotIn("sorry", ag.strip_noncode("/- open\ntheorem t := by sorry"))


# ---------------------------------------------------------------------------
# Import contract with dead_candidate_scan.py
# ---------------------------------------------------------------------------


class ImportContractTest(unittest.TestCase):
    """``dead_candidate_scan.py`` imports five names from ``audit_gate``.

    They are a published interface, not internals: breaking one breaks the
    scanner at import time, and a scanner that will not start is a scanner whose
    verdicts nobody re-checks.
    """

    NAMES = ("LIB_DIR", "REPO_ROOT", "read_capstones", "rel", "strip_noncode")

    def test_the_scanner_still_imports_exactly_these_names(self) -> None:
        """Guard the contract against silent growth on the consumer side."""
        source = (AUDIT_GATE_PATH.parent / "dead_candidate_scan.py").read_text(
            encoding="utf-8"
        )
        tail = source.split("from audit_gate import (", 1)[1].splitlines()
        names = []
        for raw in tail[1:]:  # first line carries the trailing `# noqa` comment
            line = raw.split("#")[0].strip()
            if line.startswith(")"):
                break
            if line:
                names.append(line.rstrip(","))
        imported = tuple(sorted(names))
        self.assertEqual(imported, tuple(sorted(self.NAMES)))

    def test_all_exported_names_exist(self) -> None:
        """Each imported name is present in the module."""
        for name in self.NAMES:
            self.assertTrue(hasattr(ag, name), name)

    def test_paths_are_absolute_directories(self) -> None:
        """``REPO_ROOT`` and ``LIB_DIR`` are resolved paths the scanner walks."""
        self.assertTrue(ag.REPO_ROOT.is_absolute())
        self.assertTrue(ag.LIB_DIR.is_dir())
        self.assertEqual(ag.LIB_DIR.parent, ag.REPO_ROOT)

    def test_rel_returns_posix_relative_paths(self) -> None:
        """The scanner prints and compares these strings."""
        self.assertEqual(ag.rel(ag.LIB_DIR / "Basic.lean"), "IsingModel/Basic.lean")

    def test_strip_noncode_returns_a_string_of_equal_length(self) -> None:
        """The scanner indexes the cleaned text against the raw text."""
        source = 'theorem t : True := trivial -- note\ndef m := "x"\n'
        self.assertEqual(len(ag.strip_noncode(source)), len(source))

    def test_read_capstones_returns_a_list_of_names(self) -> None:
        """The scanner turns this into a set of allowlisted declarations."""
        names = ag.read_capstones()
        self.assertIsInstance(names, list)
        self.assertTrue(names)
        for name in names:
            self.assertIsInstance(name, str)
            self.assertNotIn(" ", name)


# ---------------------------------------------------------------------------
# V1: no axiom declarations
# ---------------------------------------------------------------------------


class V1AxiomTest(unittest.TestCase):
    """V1 must catch every spelling of an ``axiom`` declaration."""

    def failures(self, text: str) -> list[str]:
        """Run V1 over a one-file fixture library."""
        with library({"F.lean": text}):
            return ag.check_v1()

    def test_plain_axiom_is_caught(self) -> None:
        """The base case."""
        self.assertEqual(len(self.failures("axiom bad : True\n")), 1)

    def test_indented_axiom_is_caught(self) -> None:
        """Declarations inside a ``namespace`` are usually indented."""
        self.assertEqual(len(self.failures("namespace N\n  axiom bad : True\nend N\n")), 1)

    def test_modifiers_do_not_hide_an_axiom(self) -> None:
        """``private``/``protected``/``noncomputable``/``unsafe``/``scoped``."""
        for prefix in (
            "private ",
            "protected ",
            "noncomputable ",
            "unsafe ",
            "scoped ",
            "local ",
            "scoped[N] ",
            "private noncomputable ",
        ):
            with self.subTest(prefix=prefix):
                self.assertEqual(len(self.failures(f"{prefix}axiom bad : True\n")), 1)

    def test_attribute_block_does_not_hide_an_axiom(self) -> None:
        """``@[simp] axiom`` is still an axiom."""
        self.assertEqual(len(self.failures("@[simp] private axiom bad : True\n")), 1)

    def test_reported_line_number_is_right(self) -> None:
        """Diagnostics must point at the declaration, not the file."""
        failures = self.failures("-- header\n\naxiom bad : True\n")
        self.assertTrue(failures[0].endswith("F.lean:3: axiom declaration"), failures)

    def test_commented_axiom_is_not_reported(self) -> None:
        """Prose about axioms is not an axiom."""
        self.assertEqual(self.failures("-- axiom bad : True\n/- axiom b : True -/\n"), [])

    def test_axiom_in_a_string_is_not_reported(self) -> None:
        """Neither is a string literal naming one."""
        self.assertEqual(self.failures('def m : String := "axiom bad"\n'), [])

    def test_identifier_containing_axiom_is_not_reported(self) -> None:
        """``axiomatic_foo`` and ``theorem axiom_free`` are innocent."""
        self.assertEqual(
            self.failures("theorem axiom_free : True := trivial\ndef axiomatic := 1\n"), []
        )

    def test_axiom_not_at_line_start_is_not_reported(self) -> None:
        """``#print axioms X`` and ``exact axiomFoo`` must stay silent."""
        self.assertEqual(self.failures("#print axioms IsingModel.foo\n"), [])

    def test_all_library_files_are_visited(self) -> None:
        """Nested directories are searched, not just the top level."""
        with library({"A.lean": "axiom a : True\n", "Sub/B.lean": "axiom b : True\n"}):
            self.assertEqual(len(ag.check_v1()), 2)

    def test_real_tree_has_no_axioms(self) -> None:
        """The project's standing claim: zero axiomatized targets."""
        self.assertEqual(real_tree_results()[0], [])


# ---------------------------------------------------------------------------
# V2: no sorry / admit / native_decide
# ---------------------------------------------------------------------------


class V2TokenTest(unittest.TestCase):
    """V2 must catch unfinished proofs and the compiler-trusting shortcut."""

    def failures(self, text: str, name: str = "F.lean") -> list[str]:
        """Run V2 over a one-file fixture library."""
        with library({name: text}):
            return ag.check_v2()

    def test_sorry_is_caught(self) -> None:
        """The headline case."""
        self.assertEqual(len(self.failures("theorem t : True := by sorry\n")), 1)

    def test_admit_is_caught(self) -> None:
        """``admit`` is ``sorry`` under another name."""
        self.assertEqual(len(self.failures("theorem t : True := by admit\n")), 1)

    def test_native_decide_is_caught(self) -> None:
        """Outside the allowlist, kernel-bypassing evaluation is banned."""
        self.assertEqual(len(self.failures("theorem t : True := by native_decide\n")), 1)

    def test_each_occurrence_is_reported_with_its_line(self) -> None:
        """Two offences on two lines produce two located reports."""
        failures = self.failures("theorem a : True := by sorry\ntheorem b : True := by admit\n")
        self.assertEqual(len(failures), 2)
        self.assertIn("F.lean:1: `sorry`", failures[0])
        self.assertIn("F.lean:2: `admit`", failures[1])

    def test_token_in_a_comment_is_not_reported(self) -> None:
        """A TODO mentioning ``sorry`` is prose."""
        self.assertEqual(self.failures("-- no sorry here\n/- admit -/\n"), [])

    def test_token_in_a_string_is_not_reported(self) -> None:
        """So is an error message."""
        self.assertEqual(self.failures('def msg := "sorry"\n'), [])

    def test_word_boundaries_are_respected(self) -> None:
        """``sorryAx``/``admitted``/``no_sorrying`` are different identifiers."""
        self.assertEqual(
            self.failures("def sorryAx_free := 1\ndef admitted := 2\ndef presorry := 3\n"), []
        )

    def test_native_decide_allowlist_applies_to_the_listed_file(self) -> None:
        """The exemption exists for executable sanity checks in the library."""
        listed = next(iter(ag.V2_NATIVE_DECIDE_FILE_ALLOWLIST)).split("/", 1)[1]
        self.assertEqual(self.failures("example : True := by native_decide\n", listed), [])

    def test_allowlist_never_exempts_sorry_or_admit(self) -> None:
        """The exemption is per-token, not per-file.

        A file-wide exemption would make the allowlisted file a hiding place for
        unfinished proofs -- the single worst outcome V2 can produce.
        """
        listed = next(iter(ag.V2_NATIVE_DECIDE_FILE_ALLOWLIST)).split("/", 1)[1]
        failures = self.failures("example : True := by sorry\nexample : True := by admit\n", listed)
        self.assertEqual(len(failures), 2)

    def test_allowlist_does_not_cover_other_files(self) -> None:
        """A non-listed file gets no ``native_decide`` grace."""
        self.assertEqual(len(self.failures("example : True := by native_decide\n")), 1)

    def test_allowlist_entries_exist(self) -> None:
        """A stale allowlist entry is a silent exemption nobody re-reads."""
        for entry in ag.V2_NATIVE_DECIDE_FILE_ALLOWLIST:
            self.assertTrue((ag.REPO_ROOT / entry).is_file(), entry)

    def test_real_tree_is_clean(self) -> None:
        """The project's standing claim: no sorry/admit outside the allowlist."""
        self.assertEqual(real_tree_results()[1], [])


# ---------------------------------------------------------------------------
# V3: capstone axiom audit (hermetic; see module docstring)
# ---------------------------------------------------------------------------


class V3CapstoneTest(unittest.TestCase):
    """V3's decision logic, with ``lake env lean`` stubbed out."""

    def test_read_capstones_drops_comments_and_blanks(self) -> None:
        """The list is meant to be annotated."""
        with capstones("# note\n\nIsingModel.a\n  IsingModel.b  \n\n# tail\n"):
            self.assertEqual(ag.read_capstones(), ["IsingModel.a", "IsingModel.b"])

    def test_parse_axioms_output_reads_dependencies(self) -> None:
        """The ``depends on axioms: [...]`` shape."""
        parsed = ag.parse_axioms_output(
            "'IsingModel.a' depends on axioms: [propext, Classical.choice]"
        )
        self.assertEqual(parsed, {"IsingModel.a": {"propext", "Classical.choice"}})

    def test_parse_axioms_output_reads_the_axiom_free_shape(self) -> None:
        """A fully constructive proof prints a different sentence."""
        parsed = ag.parse_axioms_output("'IsingModel.a' does not depend on any axioms")
        self.assertEqual(parsed, {"IsingModel.a": set()})

    def test_parse_axioms_output_omits_unresolved_names(self) -> None:
        """Absence is how ``check_v3`` learns a name did not resolve."""
        self.assertEqual(ag.parse_axioms_output("error: unknown identifier 'X'"), {})

    def test_allowed_axioms_are_exactly_the_three_classical_ones(self) -> None:
        """Widening this set is the cheapest way to fake an axiom-free library."""
        self.assertEqual(ag.ALLOWED_AXIOMS, {"propext", "Classical.choice", "Quot.sound"})

    def test_the_permitted_set_passes(self) -> None:
        """Baseline: the three classical axioms are accepted."""
        with capstones("IsingModel.a\n"), stub_lean(
            "'IsingModel.a' depends on axioms: [propext, Classical.choice, Quot.sound]"
        ):
            failures, observed = ag.check_v3()
        self.assertEqual(failures, [])
        self.assertEqual(observed, ag.ALLOWED_AXIOMS)

    def test_an_axiom_free_capstone_passes(self) -> None:
        """A subset -- here the empty set -- is accepted."""
        with capstones("IsingModel.a\n"), stub_lean(
            "'IsingModel.a' does not depend on any axioms"
        ):
            failures, observed = ag.check_v3()
        self.assertEqual((failures, observed), ([], set()))

    def test_a_project_axiom_fails(self) -> None:
        """Any fourth axiom -- ``sorryAx`` above all -- is a failure."""
        with capstones("IsingModel.a\n"), stub_lean(
            "'IsingModel.a' depends on axioms: [propext, sorryAx]"
        ):
            failures, _ = ag.check_v3()
        self.assertEqual(len(failures), 1)
        self.assertIn("sorryAx", failures[0])

    def test_an_unknown_identifier_is_a_hard_failure(self) -> None:
        """A stale capstone name must not read as "nothing to check"."""
        with capstones("IsingModel.gone\n"), stub_lean(
            stderr="error: unknown identifier 'IsingModel.gone'", returncode=1
        ):
            failures, _ = ag.check_v3()
        self.assertTrue(any("unknown identifier" in f for f in failures), failures)

    def test_a_missing_result_is_a_failure(self) -> None:
        """Silence about a capstone is not consent."""
        with capstones("IsingModel.a\nIsingModel.b\n"), stub_lean(
            "'IsingModel.a' depends on axioms: [propext]"
        ):
            failures, _ = ag.check_v3()
        self.assertEqual(len(failures), 1)
        self.assertIn("IsingModel.b", failures[0])

    def test_an_empty_capstone_list_is_a_failure(self) -> None:
        """A vacuous V3 would pass forever; the guard makes emptiness loud."""
        with capstones("# only comments\n"):
            failures, _ = ag.check_v3()
        self.assertEqual(len(failures), 1)
        self.assertIn("no theorems", failures[0])

    def test_nonzero_exit_without_a_parsed_problem_is_a_failure(self) -> None:
        """A build error must not be mistaken for a pass."""
        with capstones("IsingModel.a\n"), stub_lean(stderr="error: build failed", returncode=1):
            failures, _ = ag.check_v3()
        self.assertTrue(failures)

    def test_the_generated_source_asks_about_every_capstone(self) -> None:
        """The file handed to Lean must import the library and list all names."""
        with capstones("IsingModel.a\nIsingModel.b\n"), stub_lean(
            "'IsingModel.a' depends on axioms: [propext]\n"
            "'IsingModel.b' depends on axioms: [propext]"
        ) as captured:
            ag.check_v3()
        source = str(captured["source"])
        self.assertIn("import IsingModel", source)
        self.assertIn("#print axioms IsingModel.a", source)
        self.assertIn("#print axioms IsingModel.b", source)

    def test_the_temp_file_is_removed(self) -> None:
        """V3 must not leak scratch ``.lean`` files into the tree."""
        with capstones("IsingModel.a\n"), stub_lean(
            "'IsingModel.a' depends on axioms: [propext]"
        ) as captured:
            ag.check_v3()
        self.assertFalse(Path(str(captured["cmd"][-1])).exists())

    def test_real_capstones_exist_in_the_library(self) -> None:
        """Cheap honesty check for the real list, without paying for Lean.

        The full check is the ``#print axioms`` run in CI (``--full``); this one
        catches the common rot -- a renamed or deleted capstone -- in a second.
        """
        sources = "\n".join(
            ag.strip_noncode(path.read_text(encoding="utf-8")) for path in ag.iter_lib_files()
        )
        for name in ag.read_capstones():
            leaf = name.rsplit(".", 1)[-1]
            self.assertIn(leaf, sources, f"capstone {name} not found in the library")

    @unittest.skipUnless(os.environ.get("AUDIT_GATE_LIVE_V3") == "1", "opt-in (needs lake)")
    def test_live_capstone_audit(self) -> None:
        """The real thing, opt-in: identical to what CI runs with ``--full``."""
        failures, _ = ag.check_v3()
        self.assertEqual(failures, [])


# ---------------------------------------------------------------------------
# V4: no Japanese text -- character class
# ---------------------------------------------------------------------------


class V4CharClassTest(unittest.TestCase):
    """What the Japanese class must and must not match."""

    def assertMatches(self, char: str) -> None:  # noqa: N802 (unittest style)
        """Assert the class covers ``char``."""
        self.assertTrue(ag._JAPANESE_RE.search(char), hex(ord(char)))

    def assertNoMatch(self, char: str) -> None:  # noqa: N802 (unittest style)
        """Assert the class leaves ``char`` alone."""
        self.assertIsNone(ag._JAPANESE_RE.search(char), hex(ord(char)))

    def test_kana_is_matched(self) -> None:
        """Hiragana, katakana and halfwidth katakana."""
        for char in (HIRAGANA_A, KATAKANA_A, HALFWIDTH_KATAKANA, chr(0x30FC)):
            self.assertMatches(char)

    def test_ideographs_are_matched(self) -> None:
        """The main block plus extensions A and B."""
        for char in (KANJI, EXT_A_IDEOGRAPH, EXT_B_IDEOGRAPH, chr(0xF900)):
            self.assertMatches(char)

    def test_invisible_punctuation_is_matched(self) -> None:
        """The residue a rewrite leaves behind is the whole point of V4."""
        for char in (IDEOGRAPHIC_SPACE, IDEOGRAPHIC_COMMA, chr(0x3002), chr(0xFF01)):
            self.assertMatches(char)

    def test_radicals_are_matched(self) -> None:
        """U+2E80-U+2FDF: radicals and ideographic description characters."""
        for char in (KANGXI_RADICAL, chr(0x2E80), chr(0x2FF0)):
            self.assertMatches(char)

    def test_enclosed_and_compatibility_forms_are_matched(self) -> None:
        """U+3190-U+33FF: kanbun, enclosed CJK, squared abbreviations."""
        for char in (PARENTHESIZED_IDEOGRAPH, SQUARED_ERA_NAME, chr(0x3190), chr(0x31F0)):
            self.assertMatches(char)

    def test_vertical_and_small_forms_are_matched(self) -> None:
        """U+FE10-U+FE1F and U+FE30-U+FE6F."""
        for char in (VERTICAL_COMMA, CJK_COMPAT_FORM, chr(0xFE50)):
            self.assertMatches(char)

    def test_ideographic_variation_selectors_are_matched(self) -> None:
        """U+E0100-U+E01EF: an orphaned selector is invisible residue."""
        for char in (IVS_SELECTOR, chr(0xE01EF)):
            self.assertMatches(char)

    def test_emoji_variation_selector_is_deliberately_excluded(self) -> None:
        """U+FE00-U+FE0F is out of scope, by measurement, not oversight.

        U+FE0F selects emoji presentation for symbols the tree already uses
        (checkmark, star), and a variation selector in Japanese text always
        follows a base ideograph the class already catches -- so including the
        block would buy nothing and cost false positives. Pinning the exclusion
        makes it a decision rather than an accident.
        """
        for char in (EMOJI_SELECTOR, chr(0xFE00)):
            self.assertNoMatch(char)

    def test_lean_mathematical_notation_is_not_matched(self) -> None:
        """Greek, blackboard bold and operators fill the library."""
        for char in "abZ09_'()[]{}<>=+-*/\\|&^%$#@!?,.;:~`\"":
            self.assertNoMatch(char)
        for char in "alphabetagamma":
            self.assertNoMatch(char)
        for char in (
            chr(0x03B1),  # alpha
            chr(0x03B2),  # beta
            chr(0x039B),  # capital lambda
            chr(0x211D),  # double-struck R
            chr(0x2115),  # double-struck N
            chr(0x2211),  # summation
            chr(0x00D7),  # multiplication sign
            chr(0x2713),  # checkmark, present in the library
            chr(0x2605),  # star, present in docs/index.md
            chr(0x2026),  # horizontal ellipsis
        ):
            self.assertNoMatch(char)

    def test_bopomofo_and_hangul_are_not_matched(self) -> None:
        """V4 is a Japanese gate, not a general non-Latin gate."""
        for char in (chr(0x3105), chr(0x3131), chr(0xAC00)):
            self.assertNoMatch(char)

    def test_the_ranges_are_ordered_and_disjoint(self) -> None:
        """An overlapping or reversed range is a silently broken class."""
        previous = -1
        for low, high in ag._JAPANESE_RANGES:
            self.assertLess(low, high)
            self.assertGreater(low, previous)
            previous = high

    def test_this_file_and_the_gate_pass_their_own_class(self) -> None:
        """Both scripts are scanned by V4, so they must be Japanese-free."""
        for path in (AUDIT_GATE_PATH, Path(__file__).resolve()):
            self.assertIsNone(
                ag._JAPANESE_RE.search(path.read_text(encoding="utf-8")), path.name
            )


# ---------------------------------------------------------------------------
# V4: no Japanese text -- scanning behaviour
# ---------------------------------------------------------------------------


class V4ScanTest(unittest.TestCase):
    """How V4 chooses files, and how it behaves when something goes wrong."""

    def test_japanese_in_a_tracked_file_is_reported(self) -> None:
        """The base case, with the offending line located."""
        with tracked_repo({"docs/a.md": f"ok\ntitle {KANJI}\n"}):
            failures, scanned = ag.check_v4()
        self.assertEqual(scanned, 1)
        self.assertEqual(len(failures), 1)
        self.assertIn("docs/a.md:2", failures[0])

    def test_the_offending_characters_are_shown(self) -> None:
        """A report has to be actionable: invisible residue needs its codepoint."""
        with tracked_repo({"docs/a.md": f"x{IDEOGRAPHIC_SPACE}y\n"}):
            failures, _ = ag.check_v4()
        self.assertIn(repr(IDEOGRAPHIC_SPACE)[1:-1], failures[0])

    def test_an_english_tree_passes(self) -> None:
        """No false positive on ordinary ASCII prose."""
        with tracked_repo({"docs/a.md": "# Title\n\nPlain English.\n"}):
            self.assertEqual(ag.check_v4(), ([], 1))

    def test_untracked_files_are_ignored(self) -> None:
        """Scratch files must never trip the gate."""
        with tracked_repo({"docs/a.md": f"{HIRAGANA_A}\n"}, stage=False):
            failures, _ = ag.check_v4()
        self.assertEqual(len(failures), 1)
        self.assertIn("nothing to scan", failures[0])

    def test_files_outside_the_paths_are_ignored(self) -> None:
        """Scope is set by ``V4_PATHS``, which is what keeps internal notes out."""
        with tracked_repo(
            {"docs/a.md": "English\n", "notes/b.md": f"{HIRAGANA_A}\n"}, paths=("docs",)
        ):
            self.assertEqual(ag.check_v4(), ([], 1))

    def test_a_long_line_is_truncated_in_the_report(self) -> None:
        """Diagnostics stay readable even for a minified or generated line."""
        with tracked_repo({"docs/a.md": "x" * 200 + KANJI + "\n"}):
            failures, _ = ag.check_v4()
        self.assertIn("...", failures[0])
        self.assertLess(len(failures[0]), 200)

    def test_a_binary_file_is_a_failure_not_a_skip(self) -> None:
        """Fail-closed: an unscannable tracked file demands a decision.

        Skipping would let a committed binary -- or a mis-encoded source --
        count as "scanned", which is the fail-open shape V4 exists to remove.
        """
        with tracked_repo({"docs/a.bin": b"\xff\xfe\x00\x01"}):
            failures, _ = ag.check_v4()
        self.assertEqual(len(failures), 1)
        self.assertIn("not valid UTF-8", failures[0])

    def test_an_empty_match_is_a_failure(self) -> None:
        """Scanning nothing is not passing."""
        with tracked_repo({"docs/a.md": "English\n"}, paths=("no_such_dir",)):
            failures, scanned = ag.check_v4()
        self.assertEqual(scanned, 0)
        self.assertTrue(any("nothing to scan" in f for f in failures), failures)

    def test_a_failing_git_is_a_failure(self) -> None:
        """A broken ``git`` must not silently empty the file list."""

        def broken(cmd, **kwargs):  # type: ignore[no-untyped-def]
            return FakeProc(stderr="fatal: not a git repository", returncode=128)

        with patched(subprocess, run=broken):
            failures, scanned = ag.check_v4()
        self.assertEqual(scanned, 0)
        self.assertTrue(any("git ls-files` failed" in f for f in failures), failures)

    def test_a_missing_git_is_a_failure(self) -> None:
        """Same, for a machine without ``git`` at all."""

        def missing(cmd, **kwargs):  # type: ignore[no-untyped-def]
            raise FileNotFoundError("git")

        with patched(subprocess, run=missing):
            failures, scanned = ag.check_v4()
        self.assertEqual(scanned, 0)
        self.assertTrue(any("could not run" in f for f in failures), failures)

    def test_every_line_of_a_file_is_reported(self) -> None:
        """One report per offending line, not one per file."""
        with tracked_repo({"docs/a.md": f"{KANJI}\nok\n{KATAKANA_A}\n"}):
            failures, _ = ag.check_v4()
        self.assertEqual(len(failures), 2)

    def test_real_tree_is_japanese_free(self) -> None:
        """The measured ratchet: zero hits over every tracked scanned file."""
        self.assertEqual(real_tree_results()[2], [])
        self.assertGreater(real_tree_results()[3], 2000)


# ---------------------------------------------------------------------------
# V4 scope: which tracked files escape the gate
# ---------------------------------------------------------------------------


class ScopeCoverageTest(unittest.TestCase):
    """Every tracked file is either scanned by V4 or explicitly excluded.

    Without this test, ``V4_PATHS`` silently rots: a new top-level tracked file
    (or a whole new directory) is simply never scanned, and nothing says so. The
    exclusion list is deliberately tiny -- internal working material that is
    Japanese on purpose -- so any other unscanned path is a decision that has to
    be made rather than defaulted.
    """

    def tracked(self, *pathspec: str) -> set[str]:
        """Return the tracked paths matching ``pathspec`` (all files if empty)."""
        proc = subprocess.run(
            ["git", "ls-files", "-z", "--", *pathspec],
            cwd=str(ag.REPO_ROOT),
            capture_output=True,
            text=True,
            check=True,
        )
        return {name for name in proc.stdout.split("\0") if name}

    def test_no_tracked_file_escapes_unnoticed(self) -> None:
        """The invariant: scanned + deliberately excluded = everything tracked."""
        unscanned = sorted(self.tracked() - self.tracked(*ag.V4_PATHS))
        stray = [
            name
            for name in unscanned
            if not name.startswith(ag.V4_UNSCANNED_PREFIXES)
        ]
        self.assertEqual(stray, [], "tracked but neither scanned nor excluded")

    def test_the_excluded_prefixes_are_non_empty(self) -> None:
        """A stale exclusion would quietly widen the gate's blind spot."""
        for prefix in ag.V4_UNSCANNED_PREFIXES:
            self.assertTrue(self.tracked(prefix.rstrip("/")), prefix)

    def test_the_machine_managed_files_are_scanned(self) -> None:
        """Being generated is no reason to leave a committed file unscanned."""
        scanned = self.tracked(*ag.V4_PATHS)
        for name in (".gitignore", ".vscode/settings.json", "lake-manifest.json", "lean-toolchain"):
            self.assertIn(name, scanned)

    def test_the_scope_is_not_the_whole_repository(self) -> None:
        """``V4_PATHS`` must never become ``"."``: internal notes are Japanese."""
        self.assertNotIn(".", ag.V4_PATHS)
        self.assertTrue(self.tracked(".self-local"))


# ---------------------------------------------------------------------------
# Mutation tests: a weakened gate must fail
# ---------------------------------------------------------------------------


class MutationTest(unittest.TestCase):
    """Weaken each check at the source level; require the weakening to show.

    Every mutation below is a plausible edit -- the kind made to silence a false
    positive or to "simplify" a regex -- and each is paired with the fixture test
    that pins the behaviour it destroys. If a mutation ever stops producing a
    different verdict, either the check has been rewritten (``load_mutated``
    raises, because the target text is gone) or the gate has genuinely lost that
    power and the paired test must fail.
    """

    # -- V1 ---------------------------------------------------------------

    def test_v1_regex_without_modifiers_goes_blind(self) -> None:
        """Dropping the modifier group hides ``private axiom``."""
        mutant = load_mutated(
            (
                '_AXIOM_RE = re.compile(\n'
                '    r"^\\s*(?:@\\[[^\\]]*\\]\\s*)?"\n'
                '    r"(?:(?:private|protected|noncomputable|unsafe)\\s+"\n'
                '    r"|(?:scoped|local)(?:\\s*\\[[^\\]]*\\])?\\s+)*"\n'
                '    r"axiom\\b"\n'
                ')',
                '_AXIOM_RE = re.compile(r"^axiom\\b")',
            )
        )
        source = {"F.lean": "private axiom bad : True\n"}
        with library(source, module=mutant):
            self.assertEqual(mutant.check_v1(), [], "mutation did not weaken V1")
        with library(source):
            self.assertEqual(len(ag.check_v1()), 1, "V1 must catch what the mutant misses")

    def test_v1_without_comment_stripping_produces_false_positives(self) -> None:
        """Skipping ``strip_noncode`` turns commented-out prose into failures."""
        mutant = load_mutated(
            (
                "        text = strip_noncode(path.read_text(encoding=\"utf-8\"))\n"
                "        for lineno, line in enumerate(text.splitlines(), start=1):\n"
                "            if _AXIOM_RE.match(line):",
                "        text = path.read_text(encoding=\"utf-8\")\n"
                "        for lineno, line in enumerate(text.splitlines(), start=1):\n"
                "            if _AXIOM_RE.match(line):",
            )
        )
        source = {"F.lean": "-- historical note\n/-\naxiom old : True\n-/\n"}
        with library(source, module=mutant):
            self.assertEqual(len(mutant.check_v1()), 1)
        with library(source):
            self.assertEqual(ag.check_v1(), [])

    # -- V2 ---------------------------------------------------------------

    def test_v2_with_a_trimmed_token_list_goes_blind(self) -> None:
        """Dropping ``admit``/``native_decide`` from the tuple hides both."""
        mutant = load_mutated(
            ('tokens = ("sorry", "admit", "native_decide")', 'tokens = ("sorry",)')
        )
        source = {"F.lean": "theorem a : True := by admit\nexample : True := by native_decide\n"}
        with library(source, module=mutant):
            self.assertEqual(mutant.check_v2(), [])
        with library(source):
            self.assertEqual(len(ag.check_v2()), 2)

    def test_v2_with_a_file_wide_allowlist_hides_sorry(self) -> None:
        """Turning the per-token exemption into a per-file one is the worst case."""
        mutant = load_mutated(
            (
                'if tok == "native_decide" and relpath in V2_NATIVE_DECIDE_FILE_ALLOWLIST:',
                "if relpath in V2_NATIVE_DECIDE_FILE_ALLOWLIST:",
            )
        )
        listed = next(iter(ag.V2_NATIVE_DECIDE_FILE_ALLOWLIST)).split("/", 1)[1]
        source = {listed: "theorem a : True := by sorry\n"}
        with library(source, module=mutant):
            self.assertEqual(mutant.check_v2(), [])
        with library(source):
            self.assertEqual(len(ag.check_v2()), 1)

    def test_v2_without_word_boundaries_produces_false_positives(self) -> None:
        """Relaxing to substring search flags ``sorryAx_free``."""
        mutant = load_mutated(
            (
                'word_res = {tok: re.compile(rf"\\b{re.escape(tok)}\\b") for tok in tokens}',
                "word_res = {tok: re.compile(re.escape(tok)) for tok in tokens}",
            )
        )
        source = {"F.lean": "def sorryAx_free := 1\n"}
        with library(source, module=mutant):
            self.assertEqual(len(mutant.check_v2()), 1)
        with library(source):
            self.assertEqual(ag.check_v2(), [])

    def test_shared_stripper_weakening_hides_a_sorry(self) -> None:
        """The scanner-shared primitive matters to V2 too.

        Removing the string state makes ``def m := "/-"`` open a block comment,
        so every proof after it becomes invisible -- the exact two-pass hole the
        single-scanner design closed.
        """
        mutant = load_mutated(
            ("            if ch == '\"':\n                state = \"string\"", "            if False:\n                state = \"string\""),
        )
        source = {"F.lean": 'def m := "/-"\ntheorem t : True := by sorry\n'}
        with library(source, module=mutant):
            self.assertEqual(mutant.check_v2(), [])
        with library(source):
            self.assertEqual(len(ag.check_v2()), 1)

    # -- V3 ---------------------------------------------------------------

    def test_v3_with_a_widened_axiom_set_accepts_sorry_ax(self) -> None:
        """Adding one name to ``ALLOWED_AXIOMS`` silently legalises it."""
        mutant = load_mutated(
            (
                'ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})',
                'ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound", "sorryAx"})',
            )
        )
        output = "'IsingModel.a' depends on axioms: [propext, sorryAx]"
        with capstones("IsingModel.a\n", module=mutant), stub_lean(output):
            self.assertEqual(mutant.check_v3()[0], [])
        with capstones("IsingModel.a\n"), stub_lean(output):
            self.assertEqual(len(ag.check_v3()[0]), 1)

    def test_v3_without_the_empty_list_guard_passes_vacuously(self) -> None:
        """An emptied capstone list is the cheapest way to make V3 meaningless."""
        mutant = load_mutated(
            (
                '        return (["capstones.txt lists no theorems (V3 has nothing to audit)"], observed)',
                "        return ([], observed)",
            )
        )
        with capstones("# nothing\n", module=mutant):
            self.assertEqual(mutant.check_v3()[0], [])
        with capstones("# nothing\n"):
            self.assertEqual(len(ag.check_v3()[0]), 1)

    def test_v3_without_the_missing_result_check_ignores_silence(self) -> None:
        """A capstone Lean never reported on must not pass by omission."""
        mutant = load_mutated(
            (
                '            failures.append(f"V3: no `#print axioms` result for `{name}`")\n'
                "            continue",
                "            continue",
            )
        )
        output = "'IsingModel.a' depends on axioms: [propext]"
        with capstones("IsingModel.a\nIsingModel.b\n", module=mutant), stub_lean(output):
            self.assertEqual(mutant.check_v3()[0], [])
        with capstones("IsingModel.a\nIsingModel.b\n"), stub_lean(output):
            self.assertEqual(len(ag.check_v3()[0]), 1)

    def test_v3_without_the_unknown_identifier_hard_failure_loses_its_diagnosis(self) -> None:
        """Removing the hard failure degrades a stale name to a vague report."""
        mutant = load_mutated(
            (
                '    if re.search(r"unknown (identifier|constant)", combined):',
                "    if False:",
            )
        )
        canned = {"stderr": "error: unknown identifier 'IsingModel.gone'", "returncode": 1}
        with capstones("IsingModel.gone\n", module=mutant), stub_lean(**canned):
            self.assertFalse(any("unknown identifier" in f for f in mutant.check_v3()[0]))
        with capstones("IsingModel.gone\n"), stub_lean(**canned):
            self.assertTrue(any("unknown identifier" in f for f in ag.check_v3()[0]))

    # -- V4 ---------------------------------------------------------------

    def test_v4_narrowed_to_the_legacy_class_misses_the_residue(self) -> None:
        """The manual ``rg`` class (kana plus common kanji) is what V4 replaced."""
        mutant = load_mutated(
            (
                "_JAPANESE_RANGES = (\n"
                "    (0x2E80, 0x303F),\n"
                "    (0x3041, 0x309F),\n"
                "    (0x30A0, 0x30FF),\n"
                "    (0x3190, 0x33FF),\n"
                "    (0x3400, 0x4DBF),\n"
                "    (0x4E00, 0x9FFF),\n"
                "    (0xF900, 0xFAFF),\n"
                "    (0xFE10, 0xFE1F),\n"
                "    (0xFE30, 0xFE6F),\n"
                "    (0xFF00, 0xFFEF),\n"
                "    (0x20000, 0x2FFFF),\n"
                "    (0xE0100, 0xE01EF),\n"
                ")",
                "_JAPANESE_RANGES = (\n"
                "    (0x3041, 0x309F),\n"
                "    (0x30A0, 0x30FF),\n"
                "    (0x4E00, 0x9FAF),\n"
                ")",
            )
        )
        residue = (
            IDEOGRAPHIC_SPACE,
            KANGXI_RADICAL,
            SQUARED_ERA_NAME,
            VERTICAL_COMMA,
            HALFWIDTH_KATAKANA,
            EXT_A_IDEOGRAPH,
            IVS_SELECTOR,
        )
        for char in residue:
            with self.subTest(char=hex(ord(char))):
                self.assertIsNone(mutant._JAPANESE_RE.search(char))
                self.assertIsNotNone(ag._JAPANESE_RE.search(char))

    def test_v4_with_any_single_range_dropped_goes_blind_on_it(self) -> None:
        """Every range earns its place: removing it loses a real character."""
        witnesses = {
            (0x2E80, 0x303F): KANGXI_RADICAL,
            (0x3041, 0x309F): HIRAGANA_A,
            (0x30A0, 0x30FF): KATAKANA_A,
            (0x3190, 0x33FF): SQUARED_ERA_NAME,
            (0x3400, 0x4DBF): EXT_A_IDEOGRAPH,
            (0x4E00, 0x9FFF): KANJI,
            (0xF900, 0xFAFF): chr(0xF900),
            (0xFE10, 0xFE1F): VERTICAL_COMMA,
            (0xFE30, 0xFE6F): CJK_COMPAT_FORM,
            (0xFF00, 0xFFEF): HALFWIDTH_KATAKANA,
            (0x20000, 0x2FFFF): EXT_B_IDEOGRAPH,
            (0xE0100, 0xE01EF): IVS_SELECTOR,
        }
        self.assertEqual(tuple(witnesses), ag._JAPANESE_RANGES)
        for bounds, char in witnesses.items():
            with self.subTest(range=bounds):
                mutant = load_mutated(drop_range(*bounds))
                self.assertIsNone(mutant._JAPANESE_RE.search(char))
                self.assertIsNotNone(ag._JAPANESE_RE.search(char))

    def test_v4_that_skips_undecodable_files_goes_fail_open(self) -> None:
        """Turning the decode failure into a ``continue`` hides the file."""
        mutant = load_mutated(
            (
                "        except UnicodeDecodeError:\n"
                '            failures.append(f"{rel(path)}: not valid UTF-8 text (cannot be scanned)")\n'
                "            continue",
                "        except UnicodeDecodeError:\n            continue",
            )
        )
        files: dict[str, str | bytes] = {"docs/a.bin": b"\xff\xfe\x00\x01"}
        with tracked_repo(files, module=mutant):
            self.assertEqual(mutant.check_v4()[0], [])
        with tracked_repo(files):
            self.assertEqual(len(ag.check_v4()[0]), 1)

    def test_v4_that_tolerates_an_empty_file_list_goes_fail_open(self) -> None:
        """"Nothing matched" must never read as "nothing wrong"."""
        mutant = load_mutated(
            (
                '        return ([], ["V4: `git ls-files` matched no file (V4 has nothing to scan)"])',
                "        return ([], [])",
            )
        )
        files: dict[str, str | bytes] = {"docs/a.md": "English\n"}
        with tracked_repo(files, paths=("no_such_dir",), module=mutant):
            self.assertEqual(mutant.check_v4()[0], [])
        with tracked_repo(files, paths=("no_such_dir",)):
            self.assertTrue(ag.check_v4()[0])

    def test_v4_with_a_shrunken_path_list_stops_scanning(self) -> None:
        """The scope list is part of the gate: shrinking it must be visible.

        ``ScopeCoverageTest`` is what catches this in the real tree; here the
        mechanism is pinned directly.
        """
        mutant = load_mutated(('    "lean-toolchain",\n', ""))
        self.assertNotIn("lean-toolchain", mutant.V4_PATHS)
        self.assertIn("lean-toolchain", ag.V4_PATHS)
        tracked = subprocess.run(
            ["git", "ls-files", "-z", "--", *mutant.V4_PATHS],
            cwd=str(ag.REPO_ROOT),
            capture_output=True,
            text=True,
            check=True,
        ).stdout
        self.assertNotIn("lean-toolchain", tracked.split("\0"))


# ---------------------------------------------------------------------------
# End-to-end
# ---------------------------------------------------------------------------


class MainTest(unittest.TestCase):
    """The command-line surface CI and the hook depend on."""

    def test_the_argument_parser_accepts_the_documented_flags(self) -> None:
        """``--full`` (CI) and ``--self-test`` (this suite) must stay wired."""
        source = AUDIT_GATE_PATH.read_text(encoding="utf-8")
        self.assertIn('"--full"', source)
        self.assertIn('"--self-test"', source)

    def test_ci_runs_the_gate_in_full_mode(self) -> None:
        """V3 is only mandatory where the oleans exist; CI is that place."""
        workflow = (ag.REPO_ROOT / ".github" / "workflows" / "lean_action_ci.yml").read_text(
            encoding="utf-8"
        )
        self.assertIn("scripts/audit_gate.py --full", workflow)

    def test_the_gate_passes_on_the_current_tree(self) -> None:
        """V1, V2 and V4 are green here and now (V3 is CI's job)."""
        v1, v2, v4, _ = real_tree_results()
        self.assertEqual((v1, v2, v4), ([], [], []))


def run_suite() -> int:
    """Run every test. Return ``0`` on success, ``1`` otherwise."""
    loader = unittest.TestLoader()
    suite = loader.loadTestsFromModule(sys.modules[__name__])
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    return 0 if result.wasSuccessful() else 1


if __name__ == "__main__":
    sys.exit(run_suite())

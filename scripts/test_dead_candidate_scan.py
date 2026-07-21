#!/usr/bin/env python3
"""Tests for ``scripts/dead_candidate_scan.py``.

Run directly (``python3 scripts/test_dead_candidate_scan.py``) or through the
scanner's own ``--self-test`` flag. The suite is the reason the scanner is worth
trusting: the failures it pins down -- a Unicode-splitting tokenizer, a LaTeX
channel that silently matches nothing, a line-anchored declaration parser --
are the three defects that produced three bad deletion sweeps.

Fast unit tests use synthetic strings. The tree-dependent tests (canary,
fixtures, exit codes, determinism, performance) parse the real repository once
and share it.
"""

from __future__ import annotations

import io
import sys
import time
import unittest
from contextlib import redirect_stdout
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import dead_candidate_scan as dcs  # noqa: E402  (path bootstrap first)
from audit_gate import strip_noncode  # noqa: E402

_TREE: dcs.Tree | None = None
_DOCS: list[dcs.DocSource] | None = None
_LOAD_SECONDS = 0.0


def tree() -> dcs.Tree:
    """Return the parsed repository, parsed at most once per process."""
    global _TREE, _LOAD_SECONDS
    if _TREE is None:
        started = time.time()
        _TREE = dcs.load_tree()
        _LOAD_SECONDS = time.time() - started
    return _TREE


def docs() -> list[dcs.DocSource]:
    """Return the normalised documentation sources, loaded at most once."""
    global _DOCS
    if _DOCS is None:
        _DOCS = dcs.load_docs()
    return _DOCS


class CharClassTest(unittest.TestCase):
    """The identifier class must mirror Lean's, in both directions."""

    def test_lean_reserved_letters_are_excluded(self) -> None:
        """Lambda, Pi and Sigma are syntax in Lean, not identifier characters."""
        for char in "λΠΣ":
            self.assertFalse(dcs.is_id_rest(char), char)

    def test_identifier_characters_are_included(self) -> None:
        """Capital Lambda, Greek minuscules, blackboard bold and subscripts are."""
        for char in "Λβσℝℕ₀ₐ_'!?aZ0":
            self.assertTrue(dcs.is_id_rest(char), char)

    def test_separators_are_excluded(self) -> None:
        """Whitespace, brackets, dots and logical symbols end an identifier."""
        for char in " \n().,:¬⟨⟩":
            self.assertFalse(dcs.is_id_rest(char), char)

    def test_is_id_first_rejects_digits(self) -> None:
        """A digit cannot start an identifier, though it can continue one."""
        self.assertFalse(dcs.is_id_first("0"))
        self.assertTrue(dcs.is_id_first("_"))
        self.assertTrue(dcs.is_id_first("Λ"))

    def test_char_class_selftest_passes(self) -> None:
        """The scanner's own start-up assertion agrees with this suite."""
        dcs.char_class_selftest()


class BoundaryTest(unittest.TestCase):
    """Fixed-string search plus boundary predicate, on real repository names."""

    def matches(self, haystack: str, needle: str) -> int:
        """Return the number of boundary-accepted matches."""
        return len(dcs.find_occurrences(haystack, needle))

    def test_longer_identifier_does_not_match_its_prefix(self) -> None:
        """``_of_ferromagnetic`` continues the identifier, so it is not a match."""
        self.assertEqual(self.matches("freeEnergyΛ_nonneg_of_ferromagnetic", "freeEnergyΛ_nonneg"), 0)

    def test_sibling_suffix_pair_is_separated(self) -> None:
        """The #4641 sharpest case: ``pseudoMassG_analyticAt`` vs ``..._of_even``."""
        self.assertEqual(self.matches("pseudoMassG_analyticAt_of_even", "pseudoMassG_analyticAt"), 0)
        self.assertEqual(
            self.matches("exact pseudoMassG_analyticAt h", "pseudoMassG_analyticAt"), 1
        )

    def test_delimiters_accept(self) -> None:
        """Parentheses and spaces are not identifier characters."""
        self.assertEqual(self.matches("(freeEnergyΛ_nonneg h)", "freeEnergyΛ_nonneg"), 1)

    def test_identifier_char_on_the_left_rejects(self) -> None:
        """A match inside a longer name is not a reference to the shorter one."""
        self.assertEqual(self.matches("xΛ_nonneg", "Λ_nonneg"), 0)

    def test_unicode_name_finds_itself(self) -> None:
        """The signature failure: a Greek letter must not break self-matching."""
        name = "freeEnergyΛ_nonneg_of_ferromagnetic"
        self.assertEqual(self.matches(f"theorem {name} : True := trivial", name), 1)

    def test_dot_contexts(self) -> None:
        """A dot on the left qualifies; a dot on the right projects."""
        occs = dcs.find_occurrences("Ambient.foo_bar", "foo_bar")
        self.assertEqual([occ[1] for occ in occs], [dcs.CTX_DOTTED])
        self.assertEqual(occs[0][2], "Ambient")
        occs = dcs.find_occurrences("foo_bar.symm", "foo_bar")
        self.assertEqual([occ[1] for occ in occs], [dcs.CTX_PLAIN])
        occs = dcs.find_occurrences("hf.foo_bar", "foo_bar")
        self.assertEqual(occs[0][2], "hf")

    def test_subscript_boundary(self) -> None:
        """A subscript digit continues an identifier (``m₀`` is not ``m``)."""
        self.assertEqual(self.matches("m₀ = 0", "m"), 0)


class DeclExtractionTest(unittest.TestCase):
    """Declaration heads, including the ones that broke earlier sweeps."""

    def extract(self, source: str) -> list[dcs.Decl]:
        """Extract declarations from synthetic source text."""
        path = dcs.REPO_ROOT / "IsingModel" / "Synthetic.lean"
        return dcs.extract_decls(path, strip_noncode(source))

    def test_name_on_the_next_line(self) -> None:
        """A name on the line after the keyword must still be found."""
        decls = self.extract("theorem\n    long_name_on_next_line (h : True) : True := h\n")
        self.assertEqual([d.name for d in decls], ["long_name_on_next_line"])
        self.assertFalse(decls[0].anonymous)

    def test_attributes_and_modifiers(self) -> None:
        """Attribute blocks and modifier prefixes are recorded, not skipped."""
        decls = self.extract(
            "@[simp]\nprivate theorem foo_simp : True := trivial\n"
            "noncomputable def bar : Nat := 0\n"
            "scoped[Ising] instance inst_baz : Inhabited Nat := ⟨0⟩\n"
        )
        self.assertEqual([d.name for d in decls], ["foo_simp", "bar", "inst_baz"])
        self.assertEqual(decls[0].attrs, ("simp",))
        self.assertEqual(decls[1].kind, "def")

    def test_anonymous_instance_is_an_owner(self) -> None:
        """Anonymous heads consume references even though nothing names them."""
        decls = self.extract("instance : Inhabited Nat := ⟨0⟩\n")
        self.assertEqual(len(decls), 1)
        self.assertTrue(decls[0].anonymous)

    def test_namespace_qualification(self) -> None:
        """The fully-qualified name follows namespace/section nesting."""
        decls = self.extract(
            "namespace IsingModel\nsection Local\ntheorem foo : True := trivial\nend Local\n"
            "end IsingModel\n"
        )
        self.assertEqual(decls[0].full, "IsingModel.foo")
        self.assertEqual(decls[0].final, "foo")

    def test_multiline_attribute_block(self) -> None:
        """An attribute block spanning lines does not hide the declaration."""
        decls = self.extract("@[simp,\n  norm_cast]\ntheorem foo : True := trivial\n")
        self.assertEqual([d.name for d in decls], ["foo"])
        self.assertIn("simp", decls[0].attrs)


class CommentIsolationTest(unittest.TestCase):
    """A name mentioned only in prose is not a Lean reference."""

    def test_doc_comment_and_line_comment_contribute_nothing(self) -> None:
        """Both comment forms are blanked before matching."""
        source = "/-- mentions foo_bar -/\n-- foo_bar again\ntheorem baz : True := trivial\n"
        cleaned = strip_noncode(source)
        self.assertEqual(dcs.find_occurrences(cleaned, "foo_bar"), [])

    def test_nested_block_comment(self) -> None:
        """Nested block comments are consumed as a unit."""
        cleaned = strip_noncode("/- /- foo_bar -/ foo_bar -/\ntheorem baz : True := trivial\n")
        self.assertEqual(dcs.find_occurrences(cleaned, "foo_bar"), [])

    def test_string_literal_body(self) -> None:
        """A block-comment opener inside a string does not swallow real code."""
        cleaned = strip_noncode('def m := "/-"\ntheorem uses_foo_bar : True := trivial\n')
        self.assertEqual(len(dcs.find_occurrences(cleaned, "uses_foo_bar")), 1)


class TexNormalisationTest(unittest.TestCase):
    """The second Unicode defect: names are LaTeX-mangled in the proof guide."""

    def test_escaped_underscore_and_math_lambda(self) -> None:
        """``\\_`` and both math-mode spellings of Lambda normalise to the name."""
        text = (
            r"\texttt{log\_partitionFunction\(\Lambda\)\_latticeGraph}"
            "\n"
            r"\texttt{freeEnergy$\Lambda$\_eq\_tsum}"
        )
        normalized, _warnings = dcs.normalize_tex(text)
        self.assertIn("log_partitionFunctionΛ_latticeGraph", normalized)
        self.assertIn("freeEnergyΛ_eq_tsum", normalized)

    def test_repo_local_macro_and_break_hints(self) -> None:
        """``\\LeanLambda`` and ``\\allowbreak`` occur *inside* names in this repo."""
        normalized, _warnings = dcs.normalize_tex(
            r"\texttt{magnetization\LeanLambda\_non\allowbreak neg}"
        )
        self.assertIn("magnetizationΛ_nonneg", normalized)

    def test_comments_are_dropped_but_escaped_percent_is_not(self) -> None:
        """A LaTeX comment is not a citation; ``\\%`` is ordinary text."""
        normalized, _warnings = dcs.normalize_tex("visible % hidden_name\n" + r"100\% sure")
        self.assertNotIn("hidden_name", normalized)
        self.assertIn("100% sure", normalized)

    def test_residual_macro_is_reported(self) -> None:
        """An unnormalised macro inside a code citation must not fail silently."""
        _normalized, warnings = dcs.normalize_tex(r"\texttt{foo\unknownmacro bar}")
        self.assertEqual(len(warnings), 1)

    def test_real_guide_contains_the_mangled_names(self) -> None:
        """End-to-end on the real file: both fixture names must be found."""
        tex = next(doc for doc in docs() if doc.label.endswith("proof-guide.tex"))
        for name in (
            "log_partitionFunctionΛ_latticeGraph_biUnion_super_additive",
            "freeEnergyΛ_eq_tsum_mayer_of_high_temp",
        ):
            self.assertTrue(dcs.find_occurrences(tex.text, name), name)


class DocTokenTest(unittest.TestCase):
    """Brace alternation, wildcards and the family-label threshold."""

    def test_brace_expansion(self) -> None:
        """The empty alternative and multi-brace products are both handled."""
        self.assertEqual(
            dcs.expand_braces("correlation_convergent{,_h,_beta}"),
            ["correlation_convergent", "correlation_convergent_beta", "correlation_convergent_h"],
        )
        self.assertEqual(len(dcs.expand_braces("a{1,2}_b{x,y}")), 4)

    def test_glob_regex(self) -> None:
        """Ellipsis and star citations become anchored regexes."""
        pattern = dcs.glob_to_regex("..._J_deriv_eq_le")
        self.assertIsNotNone(pattern)
        self.assertTrue(pattern.match("foo_J_deriv_eq_le"))
        self.assertFalse(pattern.match("foo_J_deriv_eq_le_extra"))
        self.assertIsNone(dcs.glob_to_regex("plain_name"))

    def test_family_label_threshold(self) -> None:
        """``_ferromagnetic`` labels a family; it may never rescue one lemma."""
        cache: dict[str, list[dcs.Decl] | None] = {}
        many = dcs._resolve_fragment(tree(), "_ferromagnetic", cache)
        self.assertIsNotNone(many)
        self.assertGreaterEqual(len(many), 2)


class CanaryTest(unittest.TestCase):
    """The cheapest possible regression detector, run on every invocation."""

    def test_unicode_declarations_find_themselves(self) -> None:
        """Every Lambda/beta/sigma-bearing declaration matches its own name."""
        count, per_char = dcs.run_canary(tree())
        self.assertGreater(count, 1000)
        for char, hits in per_char.items():
            self.assertGreater(hits, 0, char)


class FixtureTest(unittest.TestCase):
    """The measured expectations of the design, replayed against the tree."""

    def test_expect_suite_passes(self) -> None:
        """All fixture rows classify as recorded (the 7/3 acceptance split)."""
        buffer = io.StringIO()
        with redirect_stdout(buffer):
            code = dcs.run_expect(tree(), docs(), dcs.FIXTURES_FILE)
        self.assertEqual(code, dcs.EXIT_OK, buffer.getvalue())

    def test_lean_only_rescues_seven_docs_only_rescues_three(self) -> None:
        """The design in miniature: neither channel alone saves all ten keepers."""
        keepers = [
            row[0]
            for row in dcs.read_fixtures(dcs.FIXTURES_FILE)
            if row[2].startswith("#4641 keeper") or row[2].startswith("docs/index.md:")
        ]
        self.assertEqual(len(keepers), 10)
        verdicts, _cascade, _labels = dcs.classify(tree(), keepers, docs(), allow_homonym=False)
        self.assertTrue(all(v.verdict != dcs.SAFE for v in verdicts))
        with_lean_consumers = [v for v in verdicts if v.consumers]
        self.assertEqual(len(with_lean_consumers), 7)
        docs_only = [v for v in verdicts if not v.consumers]
        self.assertEqual(len(docs_only), 3)
        self.assertTrue(all(v.doc_citations for v in docs_only))


class ExitCodeTest(unittest.TestCase):
    """The contract a PR script depends on."""

    def run_main(self, argv: list[str]) -> tuple[int, str]:
        """Run the CLI, returning ``(exit code, stdout)``."""
        buffer = io.StringIO()
        with redirect_stdout(buffer):
            code = dcs.main(argv)
        return code, buffer.getvalue()

    def test_keeper_exits_one(self) -> None:
        """A candidate that is not safe fails the run."""
        code, _out = self.run_main(["--name", "freeEnergyAlongExhaustion_nonneg_of_ferromagnetic"])
        self.assertEqual(code, dcs.EXIT_NOT_SAFE)

    def test_isolated_candidate_exits_zero(self) -> None:
        """The exit-0 path must stay reachable, or the tool blocks everything."""
        code, out = self.run_main(
            [
                "--name",
                "Ambient.correlationAlongExhaustion_latticeGraph_h_zero_at_pair"
                "_ge_tanh_div_two_pow_edges_ferromagnetic",
            ]
        )
        self.assertEqual(code, dcs.EXIT_OK, out)
        self.assertIn("safe-to-delete: 1", out)

    def test_report_only_exits_zero_with_the_non_evidential_banner(self) -> None:
        """Exploration mode is allowed, but must announce that it is not evidence."""
        code, out = self.run_main(
            ["--report-only", "--name", "freeEnergyAlongExhaustion_nonneg_of_ferromagnetic"]
        )
        self.assertEqual(code, dcs.EXIT_OK)
        self.assertIn("NON-EVIDENTIAL", out)

    def test_unknown_name_is_a_hard_failure(self) -> None:
        """A stale candidate list must never be reported as deletable."""
        code, _out = self.run_main(["--name", "no_such_declaration_anywhere_xyzzy"])
        self.assertEqual(code, dcs.EXIT_INCONSISTENT)

    def test_no_candidates_is_a_hard_failure(self) -> None:
        """An empty candidate set is a misuse, not a vacuous success."""
        code, _out = self.run_main([])
        self.assertEqual(code, dcs.EXIT_INCONSISTENT)

    def test_limitation_banner_travels_with_every_verdict(self) -> None:
        """The caveats must reach the PR body together with the evidence."""
        _code, out = self.run_main(["--name", "freeEnergyAlongExhaustion_nonneg_of_ferromagnetic"])
        self.assertIn("LIMITS: this scan is textual.", out)


class DeterminismAndCostTest(unittest.TestCase):
    """Two runs must agree byte for byte, and the scan must stay linear."""

    def test_classification_is_deterministic(self) -> None:
        """No set-iteration order leaks into the verdicts."""
        names = ["pseudoMassG_analyticAt", "freeEnergyAlongExhaustion_nonneg_of_ferromagnetic"]
        first = dcs.classify(tree(), names, docs(), allow_homonym=False)
        second = dcs.classify(tree(), names, docs(), allow_homonym=False)
        self.assertEqual(
            [(v.name, v.verdict, sorted(v.reasons)) for v in first[0]],
            [(v.name, v.verdict, sorted(v.reasons)) for v in second[0]],
        )
        self.assertEqual(first[1], second[1])

    def test_candidate_scan_cost_is_linear(self) -> None:
        """Scanning 40 candidates must not cost 40 tree parses.

        The guard is a ratio against the one-off parse rather than an absolute
        wall-clock bound: this machine runs Lean builds concurrently, so an
        absolute threshold would flake while a quadratic blow-up in the number
        of candidates -- the real risk -- shows up in the ratio regardless.
        """
        parsed = tree()  # ensures _LOAD_SECONDS is set
        names = sorted(
            decl.full for decl in parsed.decls[:2000] if decl.name.endswith("_ferromagnetic")
        )[:40]
        self.assertGreaterEqual(len(names), 10)
        started = time.time()
        dcs.classify(parsed, names, docs(), allow_homonym=False)
        self.assertLess(time.time() - started, max(_LOAD_SECONDS, 1.0) * 4)


def run_suite() -> int:
    """Run every test. Return ``0`` on success, ``1`` otherwise."""
    loader = unittest.TestLoader()
    suite = loader.loadTestsFromModule(sys.modules[__name__])
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    return 0 if result.wasSuccessful() else 1


if __name__ == "__main__":
    sys.exit(run_suite())

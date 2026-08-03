#!/usr/bin/env python3
"""Tests for ``scripts/dead_candidate_scan.py``.

Run directly (``python3 scripts/test_dead_candidate_scan.py``) or through the
scanner's own ``--self-test`` flag. The suite is the reason the scanner is worth
trusting: the failures it pins down -- a Unicode-splitting tokenizer, a LaTeX
channel that silently matches nothing, a line-anchored declaration parser --
are the three defects that produced three bad deletion sweeps.

Every route to a **false ``safe-to-delete``** has a test aimed at it, because
that is the only verdict of this tool that can destroy work:
:class:`DeleteClosureTest` (a candidate consumed only by a candidate the same run
retains), :class:`SameLineAttributeTest` (``@[simp] theorem foo`` vanishing from
the declaration table, which turns its consumers into self-references),
:class:`TexCoverageTest` (a citation the LaTeX channel cannot read must warn, not
disappear), :class:`UnreadableCitationTest` (that warning must also *classify*,
or coverage is fail-open exactly where it claims to be fail-closed),
:class:`MissingDocumentationTest` (a documentation file that vanishes must abort
the run instead of silently emptying its channel),
:class:`MarkdownBacktickParityTest` (one unbalanced backtick inverts the parity of
its whole line, so the tokenizer swaps prose for citations without warning),
:class:`ElidedFragmentTest` (a suffix citation whose elided prefix is spelled out
on the same line is a shorthand, not a family label),
:class:`NarrowGlobCitationTest` (the same exoneration on the *glob* channel: a
citation naming two to eight declarations must be charged to all of them) and
:class:`CharClassTest` (the identifier class must never be a superset of Lean's).
:class:`CanaryTest` carries the unconditional Unicode guard in both directions:
a fixture holding one name per canary character (so per-character coverage does
not depend on which names the library happens to hold) and two mutations -- a
cleaner that drops a Greek letter, and a tree with no Unicode names at all --
that must abort the run rather than lower a count.
:class:`FamilyCalibrationTest` asserts the calibration integers that used to live
only in a fixtures comment. :class:`ProseMentionTest` guards the opposite
direction: a docstring mention is reported but must never rescue a lemma.

Fast unit tests use synthetic strings. The tree-dependent tests (canary,
fixtures, exit codes, determinism, performance) parse the real repository once
and share it.
"""

from __future__ import annotations

import io
import sys
import tempfile
import time
import unittest
from contextlib import redirect_stderr, redirect_stdout
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
        for char in "Λβσℝℕ₀ₐⱼÀÿĀſ_'!?aZ0":
            self.assertTrue(dcs.is_id_rest(char), char)

    def test_class_is_not_a_superset_of_leans(self) -> None:
        """Wide is the catastrophic direction, and these three are Lean's edges.

        ``Init/Meta/Defs.lean:101-118`` of the pinned toolchain has no superscript
        range at all (``ⁿ``), and cuts the multiplication and division signs out
        of the Latin-1 letter block.
        """
        for char in "ⁿ×÷":
            self.assertFalse(dcs.is_id_rest(char), char)

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
        self.assertEqual(dcs.expand_braces("a{2,1,2}"), ["a1", "a2"])

    def test_unbalanced_braces_are_preserved_verbatim(self) -> None:
        """An unreadable group must never make an existing token disappear."""
        for token in ("family_{left,right", "family_left,right}", "family_{{left,right}"):
            self.assertEqual(dcs.expand_braces(token), [token])

    def test_glob_regex(self) -> None:
        """Ellipsis and star citations become anchored regexes."""
        pattern = dcs.glob_to_regex("..._J_deriv_eq_le")
        self.assertIsNotNone(pattern)
        self.assertTrue(pattern.match("foo_J_deriv_eq_le"))
        self.assertFalse(pattern.match("foo_J_deriv_eq_le_extra"))
        self.assertIsNone(dcs.glob_to_regex("plain_name"))

    def test_trailing_punctuation_does_not_swallow_a_brace_citation(self) -> None:
        """A citation carrying its sentence punctuation is still a token.

        ``_nameish`` was applied *before* the punctuation was trimmed, so a
        brace shorthand written mid-sentence (`` `foo{,_bar}:` ``) failed the
        test on the colon and dropped out. A complete name survived only because
        the verbatim search rescues it; a brace shorthand has no such fallback.
        """
        scratch = dcs.REPO_ROOT / ".self-local" / "tmp"  # gitignored, and inside the root
        scratch.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=scratch) as tmp:
            path = Path(tmp) / "note.md"
            path.write_text("see `synthetic{,_h}_xyzzy:` and `plain_xyzzy`.\n", encoding="utf-8")
            tokens = [token for token, _line in dcs._markdown_source(path).tokens]
        self.assertEqual(tokens, ["synthetic{,_h}_xyzzy", "plain_xyzzy"])

    def test_the_name_shape_is_tested_before_and_after_trimming(self) -> None:
        """Either order alone drops a shorthand, so both forms are tested.

        Trimming first loses a citation whose only ``_``/``.`` *is* the sentence
        punctuation (`` `foo{,bar}.` ``); testing first loses one that merely
        carries punctuation (`` `foo{,_bar}:` ``). Both are brace shorthands, so
        neither has a verbatim search to fall back on. The token kept is always
        the trimmed one -- the punctuation belongs to the prose.
        """
        self.assertEqual(dcs._citation_tokens("foo{,bar}."), ["foo{,bar}"])
        self.assertEqual(dcs._citation_tokens("synthetic{,_h}_xyzzy:"), ["synthetic{,_h}_xyzzy"])
        self.assertEqual(dcs._citation_tokens("(plain_xyzzy)"), ["plain_xyzzy"])
        self.assertEqual(dcs._citation_tokens("..."), [])  # never an empty token
        self.assertEqual(dcs._citation_tokens("prose here"), [])

    def test_family_label_threshold(self) -> None:
        """``_ferromagnetic`` labels a family; it may never rescue one lemma."""
        cache: dict[str, list[dcs.Decl] | None] = {}
        many = dcs._resolve_fragment(tree(), "_ferromagnetic", cache)
        self.assertIsNotNone(many)
        self.assertGreaterEqual(len(many), 2)


class NestedBraceCitationTest(unittest.TestCase):
    """The exact F-1 citation must reach every declaration it denotes.

    At the pinned base, :func:`dead_candidate_scan.expand_braces` processes the
    innermost ``{J,h,beta,abs_h}`` group and then recurses over only the suffix.
    The outer ``{neg_h,eq_abs_h,monotone_...}`` group is consequently left in
    every result, so none of the three declarations from
    ``PartitionFunctionSymmetryLogCubic.lean`` receives a documentation charge.
    """

    PREFIX = "log_partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_"
    TOKEN = PREFIX + "{neg_h,eq_abs_h,monotone_{J,h,beta,abs_h}}"
    EXPANDED = sorted(
        [
            PREFIX + "neg_h",
            PREFIX + "eq_abs_h",
            PREFIX + "monotone_J",
            PREFIX + "monotone_h",
            PREFIX + "monotone_beta",
            PREFIX + "monotone_abs_h",
        ]
    )
    TARGETS = [
        "IsingModel.Ambient." + PREFIX + "neg_h",
        "IsingModel.Ambient." + PREFIX + "eq_abs_h",
        "IsingModel.Ambient." + PREFIX + "monotone_abs_h",
    ]

    def test_nested_group_expands_to_six_concrete_names(self) -> None:
        """Processing an inner group must not strand the enclosing group."""
        expanded = dcs.expand_braces(self.TOKEN)
        self.assertEqual(expanded, self.EXPANDED)
        self.assertTrue(all("{" not in name and "}" not in name for name in expanded))

    def test_depth_1000_balanced_singleton_terminates(self) -> None:
        """Every balanced token accepted by the citation grammar must terminate."""
        token = "family_" + "{" * 1000 + "left" + "}" * 1000
        self.assertIn(token, dcs._citation_tokens(token))
        expanded = dcs.expand_braces(token)
        self.assertEqual(expanded, ["family_left"])
        self.assertTrue(all("{" not in name and "}" not in name for name in expanded))

    def test_real_nested_citation_publishes_the_three_excluded_declarations(self) -> None:
        """End to end on the exact ``docs/index.md:1412`` citation shape."""
        index = next(source for source in docs() if source.label == "docs/index.md")
        self.assertIn((self.TOKEN, 1412), index.tokens)

        verdicts, _cascade, _labels = dcs.classify(
            tree(), self.TARGETS, docs(), allow_homonym=False
        )
        self.assertEqual([verdict.decl.full for verdict in verdicts], self.TARGETS)
        for verdict in verdicts:
            self.assertEqual(verdict.verdict, dcs.PUBLISHED, verdict.decl.full)
            self.assertTrue(
                any(
                    citation.startswith("exact docs/index.md:1412:")
                    and self.TOKEN in citation
                    for citation in verdict.doc_citations
                ),
                (verdict.decl.full, verdict.doc_citations),
            )
            self.assertIn(
                "cited verbatim in the public documentation",
                verdict.reasons,
                verdict.decl.full,
            )


class SlashAlternationCitationTest(unittest.TestCase):
    """The two row-1399 numeric shorthands must reach all six declarations.

    The pinned base drops both citation bodies during tokenization. Applying
    only brace expansion is insufficient too: every spelling retains ``3/4``
    and therefore names no declaration.
    """

    BETA_TOKEN = (
        "truncated3/4Infinite_latticeGraph_"
        "{beta_zero,J_zero_of_pairwise_distinct}"
    )
    NONPOS_TOKEN = "truncated3/4Infinite_latticeGraph_{nonpos{,_h_zero}}"
    PREFIX = "truncated3/4Infinite_latticeGraph_"
    TOKENS = [BETA_TOKEN, NONPOS_TOKEN]
    BRACE_ONLY = {
        BETA_TOKEN: sorted(
            [
                "truncated3/4Infinite_latticeGraph_beta_zero",
                "truncated3/4Infinite_latticeGraph_J_zero_of_pairwise_distinct",
            ]
        ),
        NONPOS_TOKEN: sorted(
            [
                "truncated3/4Infinite_latticeGraph_nonpos",
                "truncated3/4Infinite_latticeGraph_nonpos_h_zero",
            ]
        ),
    }
    EXPANDED = {
        BETA_TOKEN: sorted(
            [
                f"truncated{arity}Infinite_latticeGraph_{suffix}"
                for arity in (3, 4)
                for suffix in ("beta_zero", "J_zero_of_pairwise_distinct")
            ]
        ),
        NONPOS_TOKEN: sorted(
            [
                f"truncated{arity}Infinite_latticeGraph_{suffix}"
                for arity in (3, 4)
                for suffix in ("nonpos", "nonpos_h_zero")
            ]
        ),
    }
    TARGET_TOKENS = {
        "IsingModel.Ambient.truncated3Infinite_latticeGraph_beta_zero": BETA_TOKEN,
        "IsingModel.Ambient.truncated3Infinite_latticeGraph_J_zero_of_pairwise_distinct": (
            BETA_TOKEN
        ),
        "IsingModel.Ambient.truncated4Infinite_latticeGraph_beta_zero": BETA_TOKEN,
        "IsingModel.Ambient.truncated4Infinite_latticeGraph_J_zero_of_pairwise_distinct": (
            BETA_TOKEN
        ),
        "IsingModel.Ambient.truncated3Infinite_latticeGraph_nonpos": NONPOS_TOKEN,
        "IsingModel.Ambient.truncated4Infinite_latticeGraph_nonpos_h_zero": NONPOS_TOKEN,
    }
    TARGETS = list(TARGET_TOKENS)
    NONPOS_EXISTING = sorted(
        [
            "truncated3Infinite_latticeGraph_nonpos",
            "truncated4Infinite_latticeGraph_nonpos_h_zero",
        ]
    )
    OUT_OF_SCOPE_NUMERIC_TOKENS = [
        "truncated2/3Infinite_latticeGraph_{beta_zero,J_zero_of_pairwise_distinct}",
        "truncated4/3Infinite_latticeGraph_{beta_zero,J_zero_of_pairwise_distinct}",
        "truncated0/9Infinite_latticeGraph_{beta_zero,J_zero_of_pairwise_distinct}",
        "truncated3/5Infinite_latticeGraph_{beta_zero,J_zero_of_pairwise_distinct}",
        "truncated3/3Infinite_latticeGraph_{beta_zero,J_zero_of_pairwise_distinct}",
    ]
    MALFORMED_OUTER_ALTERNATIVES = [
        "truncated3/4Infinite_latticeGraph_"
        "{beta_zero,,J_zero_of_pairwise_distinct}",
        "truncated3/4Infinite_latticeGraph_{,beta_zero}",
        "truncated3/4Infinite_latticeGraph_{beta_zero,}",
        "truncated3/4Infinite_latticeGraph_{}",
    ]
    UNSUPPORTED_PAYLOAD_TOKENS = MALFORMED_OUTER_ALTERNATIVES + [
        PREFIX + "{nonpos{,,_h_zero}}",
        PREFIX + "{nonpos{,_h_zero,}}",
        PREFIX + "{nonpos{}}",
        PREFIX + "{{beta_zero}}",
        PREFIX + "{{}}",
        PREFIX + "{beta_zero,{}}",
        PREFIX + "{beta_zero,{,J_zero_of_pairwise_distinct}}",
        PREFIX + "{beta_zero,{J_zero_of_pairwise_distinct,}}",
        PREFIX + "{nonpos{,_h_zero}{}}",
        PREFIX + "{beta_zero,J_zero_of_pairwise_distinct,nonpos}",
        PREFIX + "{J_zero_of_pairwise_distinct,beta_zero}",
        PREFIX
        + "{beta_zero,J_zero_of_pairwise_distinct}"
        + "{nonpos{,_h_zero}}",
        PREFIX + "{nonpos{,{,_h_zero}}}",
        PREFIX + "{" + "a" * 74 + "}",
        PREFIX
        + "{beta_zero,J_zero_of_pairwise_distinct,nonpos,nonpos_h_zero}",
    ]
    NON_CITATIONS = [
        "https://example.test/truncated3/4Infinite_latticeGraph_beta_zero",
        "docs/truncated3/4Infinite_latticeGraph_beta_zero",
        "ratio_3/4_value",
        "IsingModel.truncated3/4Infinite_latticeGraph_beta_zero",
        "truncated3/4Infinite_latticeGraph_*",
        "_truncated3/4Infinite_latticeGraph_beta_zero",
    ]
    UNSUPPORTED = NON_CITATIONS + [
        "family3/4Infinite_name",
        "family3/4Infinite_{left,right}",
        "truncated3/4/5Infinite_latticeGraph_beta_zero",
        "truncated3/4Infinite_latticeGraph_beta/zero",
        "truncated/4Infinite_latticeGraph_beta_zero",
        "truncated3/Infinite_latticeGraph_beta_zero",
        "truncatedthree/fourInfinite_latticeGraph_beta_zero",
        "truncated3/fourInfinite_latticeGraph_beta_zero",
        "truncated3/3Infinite_latticeGraph_beta_zero",
        "truncated3/4Infinite_latticeGraph_{beta_zero,J_zero",
        "truncated3/4Infinite_latticeGraph_beta_zero}",
    ]

    def verdicts(self) -> list[dcs.Verdict]:
        """Classify the six row-1399 declarations against the real docs."""
        return dcs.classify(tree(), self.TARGETS, docs(), allow_homonym=False)[0]

    def test_exact_bodies_are_each_one_citation_token(self) -> None:
        """Both slash-family spellings must survive the real tokenizer whole."""
        for token in self.TOKENS:
            self.assertEqual(dcs._citation_tokens(token), [token], token)

    def test_slash_expansion_precedes_brace_expansion(self) -> None:
        """Brace-only retains the slash; slash-then-brace yields both products."""
        for token in self.TOKENS:
            self.assertEqual(dcs.expand_braces(token), self.BRACE_ONLY[token], token)
            self.assertEqual(dcs.expand_citation_token(token), self.EXPANDED[token], token)
            self.assertTrue(
                all(
                    "/" not in name and "{" not in name and "}" not in name
                    for name in self.EXPANDED[token]
                ),
                token,
            )
        existing_finals = {decl.final for decl in tree().decls}
        self.assertEqual(
            sorted(set(self.EXPANDED[self.NONPOS_TOKEN]) & existing_finals),
            self.NONPOS_EXISTING,
        )

    def test_real_row_attaches_one_exact_charge_to_each_target(self) -> None:
        """Every target receives the exact public citation at row 1399."""
        counts = [
            sum(
                citation.startswith("exact docs/index.md:1399:")
                and self.TARGET_TOKENS[verdict.decl.full] in citation
                for citation in verdict.doc_citations
            )
            for verdict in self.verdicts()
        ]
        self.assertEqual(counts, [1, 1, 1, 1, 1, 1])

    def test_real_row_publishes_all_six_targets(self) -> None:
        """The four base-safe targets must no longer remain safe to delete."""
        self.assertEqual(
            [verdict.verdict for verdict in self.verdicts()],
            [dcs.PUBLISHED] * 6,
        )

    def test_unsupported_slashes_are_preserved_without_partial_expansion(self) -> None:
        """Ambiguous syntax remains one original token and invents no variants."""
        for token in self.UNSUPPORTED:
            self.assertEqual(dcs.expand_slash_alternation(token), [token], token)
            self.assertEqual(dcs.expand_citation_token(token), [token], token)

    def test_non_citation_slashes_stay_out_of_the_tokenizer(self) -> None:
        """URLs, paths, division, qualified names, globs and suffixes stay inert."""
        for token in self.NON_CITATIONS:
            self.assertEqual(dcs._citation_tokens(token), [], token)

    def test_out_of_scope_numeric_pairs_are_inert(self) -> None:
        """Only the exact documented 3/4 pair is a supported numeric stem."""
        for token in self.OUT_OF_SCOPE_NUMERIC_TOKENS:
            self.assertEqual(dcs.expand_slash_alternation(token), [token], token)
            self.assertEqual(dcs.expand_citation_token(token), [token], token)
            self.assertEqual(dcs._citation_tokens(token), [], token)

    def test_out_of_scope_numeric_pairs_charge_no_declaration(self) -> None:
        """Neighboring or reversed numeric pairs invent no documentation charge."""
        synthetic = dcs.DocSource(
            label="synthetic.md",
            text="",
            starts=[0],
            tokens=[
                (token, lineno)
                for lineno, token in enumerate(self.OUT_OF_SCOPE_NUMERIC_TOKENS, 1)
            ],
            unreadable=[],
        )
        real_tree = tree()
        verdicts = [
            dcs.Verdict(name=name, decl=dcs.resolve_candidate(real_tree, name, False)[0])
            for name in self.TARGETS
        ]
        dcs._apply_doc_channel(real_tree, verdicts, [synthetic], {})
        self.assertEqual(
            {verdict.decl.full: verdict.doc_citations for verdict in verdicts},
            {name: [] for name in self.TARGETS},
        )

    def test_empty_outer_alternatives_are_inert(self) -> None:
        """Empty outer alternatives make an exact-stem slash token malformed."""
        for token in self.MALFORMED_OUTER_ALTERNATIVES:
            self.assertEqual(dcs.expand_slash_alternation(token), [token], token)
            self.assertEqual(dcs.expand_citation_token(token), [token], token)
            self.assertEqual(dcs._citation_tokens(token), [], token)

    def test_empty_outer_alternatives_charge_no_declaration(self) -> None:
        """Malformed outer products may not exact-publish their valid siblings."""
        synthetic = dcs.DocSource(
            label="synthetic.md",
            text="",
            starts=[0],
            tokens=[
                (token, lineno)
                for lineno, token in enumerate(self.MALFORMED_OUTER_ALTERNATIVES, 1)
            ],
            unreadable=[],
        )
        real_tree = tree()
        verdicts = [
            dcs.Verdict(name=name, decl=dcs.resolve_candidate(real_tree, name, False)[0])
            for name in self.TARGETS
        ]
        dcs._apply_doc_channel(real_tree, verdicts, [synthetic], {})
        self.assertEqual(
            {verdict.decl.full: verdict.doc_citations for verdict in verdicts},
            {name: [] for name in self.TARGETS},
        )

    def test_only_the_two_observed_payloads_are_supported(self) -> None:
        """Balanced BNF lookalikes and every budget violation remain inert."""
        self.assertLessEqual(max(map(len, self.TOKENS)), 73)
        for token in self.TOKENS:
            self.assertEqual(len(self.EXPANDED[token]), 4, token)
        for token in self.UNSUPPORTED_PAYLOAD_TOKENS:
            self.assertEqual(dcs.expand_slash_alternation(token), [token], token)
            self.assertEqual(dcs.expand_citation_token(token), [token], token)
            self.assertEqual(dcs._citation_tokens(token), [], token)

    def test_unsupported_payloads_charge_no_declaration(self) -> None:
        """No rejected payload may exact-publish or fragment-charge any result."""
        synthetic = dcs.DocSource(
            label="synthetic.md",
            text="",
            starts=[0],
            tokens=[
                (token, lineno)
                for lineno, token in enumerate(self.UNSUPPORTED_PAYLOAD_TOKENS, 1)
            ],
            unreadable=[],
        )
        real_tree = tree()
        verdicts = [
            dcs.Verdict(name=decl.full, decl=decl)
            for decl in real_tree.decls
            if not decl.anonymous
        ]
        dcs._apply_doc_channel(real_tree, verdicts, [synthetic], {})
        charged = [
            (verdict.decl.full, verdict.doc_citations)
            for verdict in verdicts
            if verdict.doc_citations
        ]
        self.assertEqual(charged, [])


class SpacedBraceCitationTest(unittest.TestCase):
    """A brace alternation spaced like prose is one citation, not several words.

    ``docs/index.md`` and ``tex/proof-guide.tex`` both write
    ``freeEnergyAlongExhaustion_latticeGraph_{continuousAt, differentiableAt}_{beta,
    field, J, joint}`` -- one shorthand for eight results, with the spacing of an
    English list. Splitting the citation body on every whitespace run cut it at
    each comma-space into pieces that name nothing: ``..._{continuousAt`` has no
    closing brace, so :func:`dead_candidate_scan.expand_braces` finds no group
    and returns it unchanged, and ``field,``/``J,`` carry no ``_`` for
    :func:`dead_candidate_scan._nameish`. A brace shorthand has no verbatim
    search to fall back on, so the eight results reached no verdict at all.

    Measured at ``2380eb36``: 133 name-shaped tokens of this shape (102 in
    ``docs/index.md``, 31 in ``tex/proof-guide.tex``) expand onto 307
    declarations, 160 of which a whole-library sweep called ``safe-to-delete``
    -- among them ``freeEnergyAlongExhaustion_latticeGraph_continuousAt_J``,
    cited at ``docs/index.md:1979`` and ``tex/proof-guide.tex:21095``. That is
    the fatal error class, so the split is pinned here from both sides: the
    spaced citation must survive whole, and the plain whitespace split must keep
    every token it produced before.
    """

    SPACED = (
        "freeEnergyAlongExhaustion_latticeGraph_{continuousAt, differentiableAt}"
        "_{beta, field, J, joint}"
    )

    def test_a_spaced_brace_alternation_survives_as_one_token(self) -> None:
        """The whole citation is tokenized and expands to all eight names."""
        tokens = dcs._citation_tokens(self.SPACED)
        whole = [token for token in tokens if token.endswith("}")]
        self.assertEqual(len(whole), 1, tokens)
        self.assertEqual(
            dcs.expand_braces(whole[0]),
            [
                f"freeEnergyAlongExhaustion_latticeGraph_{regularity}_{parameter}"
                for regularity in ("continuousAt", "differentiableAt")
                for parameter in ("J", "beta", "field", "joint")
            ],
        )

    def test_unspaced_brace_citations_are_untouched(self) -> None:
        """The spellings that already worked must produce exactly what they did."""
        self.assertEqual(
            dcs._citation_tokens("correlationΛ_{,latticeGraph_}continuous_joint"),
            ["correlationΛ_{,latticeGraph_}continuous_joint"],
        )
        self.assertEqual(dcs._citation_tokens("foo{,bar}."), ["foo{,bar}"])
        self.assertEqual(dcs._citation_tokens("a_one b_two"), ["a_one", "b_two"])
        self.assertEqual(dcs._citation_tokens("a_dup a_dup"), ["a_dup", "a_dup"])

    def test_the_brace_split_only_ever_adds(self) -> None:
        """Brace depth is an approximation, so it may not remove a plain token.

        A body with an unclosed ``{`` never returns to depth 0, so a brace-aware
        split *alone* would swallow every later whitespace run and lose the
        plain names after it -- the fail-open direction. Both splits are taken
        and concatenated, so the previous token list is always a prefix of the
        new one.
        """
        for body in (
            "foo_bar { unclosed and_more here",
            "closes_only } here_after",
            self.SPACED,
            "plain_one plain_two",
        ):
            plain = [
                piece.strip(",.;:()")
                for piece in body.split()
                if piece.strip(",.;:()")
                and (dcs._nameish(piece) or dcs._nameish(piece.strip(",.;:()")))
            ]
            self.assertEqual(dcs._citation_tokens(body)[: len(plain)], plain, body)

    def test_whitespace_inside_a_brace_group_is_layout(self) -> None:
        """Only the whitespace outside braces separates tokens."""
        self.assertEqual(
            dcs._brace_grouped_pieces("a_{x, y}_b  c_{p , q}"),
            ["a_{x,y}_b", "c_{p,q}"],
        )

    def test_the_real_documentation_cites_the_measured_example(self) -> None:
        """End-to-end: the two real citation sites reach the declaration."""
        target = "freeEnergyAlongExhaustion_latticeGraph_continuousAt_J"
        labels = {
            doc.label
            for doc in docs()
            for token, _line in doc.tokens
            if "{" in token and target in dcs.expand_braces(token)
        }
        self.assertEqual(labels, {"docs/index.md", "tex/proof-guide.tex"})

    def test_the_measured_example_is_not_safe_to_delete(self) -> None:
        """The verdict the defect inverted, replayed against the real tree."""
        verdicts, _cascade, _labels = dcs.classify(
            tree(),
            ["freeEnergyAlongExhaustion_latticeGraph_continuousAt_J"],
            docs(),
            allow_homonym=False,
        )
        self.assertEqual(len(verdicts), 1)
        self.assertEqual(verdicts[0].verdict, dcs.PUBLISHED)


class MarkdownBacktickParityTest(unittest.TestCase):
    """One unbalanced backtick swaps prose for citations for the rest of its line.

    Markdown code spans are paired positionally, so an unbalanced backtick does
    not lose only its own span: everything after it is read with the parity
    inverted. ``docs/index.md:1832`` spells ``ContinuousOn`.continuousAt`` with
    three backticks where two were meant, and from that column on the line's
    real citations sat outside every span the tokenizer saw -- 218 tokens, none
    of them naming ``magnetizationAlongExhaustion``, which the raw line spells
    six times. Nothing warned, and
    ``magnetizationAlongExhaustion_differentiable_beta_gen`` came out
    ``safe-to-delete``.

    Skipping such a line is the fail-open repair: what it drops is exactly the
    citations with no verbatim fallback (brace alternations, globs, elided
    suffixes). The line is therefore re-read without pairing -- a superset of
    every pairing -- and the defect is reported.

    The fenced alternative is the same hole one level up. It is ``re.DOTALL``
    and unbounded, so an unbalanced run of three or more backticks pairs with
    the next run anywhere in the file. Crediting a fenced match with its whole
    span therefore let the match that hides the citations certify their
    backticks as read, and the tests below used to assert exactly that silence.
    A fence now vouches for its two delimiters only.
    """

    def markdown(self, text: str) -> dcs.DocSource:
        """Return the ``DocSource`` of a scratch Markdown file carrying ``text``."""
        scratch = dcs.REPO_ROOT / ".self-local" / "tmp"  # gitignored, inside the root
        scratch.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=scratch) as tmp:
            path = Path(tmp) / "note.md"
            path.write_text(text, encoding="utf-8")
            return dcs._markdown_source(path)

    #: The real defect, in miniature: the stray backtick after ``ContinuousOn``
    #: inverts the parity, so the brace citation that follows is read as prose.
    FLIPPED = (
        "see `ContinuousOn`.continuousAt` and then "
        "`synth_alpha{,_beta}_xyzzy` + `_delta_gen` done\n"
    )

    #: An unbalanced fence run: the first ``` pairs with the last one, and every
    #: citation in between lands inside a body the whole-span reading called read.
    SWALLOWED = (
        "start ```\ncite `_alpha_gen` here\nand `beta{,_two}_gen`\nend ```\n"
    )

    def test_balanced_lines_and_backtick_free_fences_raise_nothing(self) -> None:
        """The check is silent on healthy Markdown whose fences quote no backtick."""
        self.assertEqual(dcs.unpaired_backticks("a `x_y` b\n```lean\ndef z_w\n```\n"), {})
        self.assertEqual(dcs.unpaired_backticks("plain prose, no code span\n"), {})

    def test_a_backtick_inside_a_fence_is_charged_not_exonerated(self) -> None:
        """A fenced match vouches for its delimiters, never for its body.

        Crediting the whole match is the fail-open move: the fenced alternative
        is unbounded and ``re.DOTALL``, so the match that swallows a citation is
        also the match that certifies its backticks as read.
        """
        self.assertEqual(dcs.unpaired_backticks(self.SWALLOWED), {2: 2, 3: 2})
        # A four-backtick run does it with a single well-formed fence after it.
        four = "a ````\ncite `_alpha_gen`\nb ```\n"
        self.assertEqual(dcs.unpaired_backticks(four), {1: 1, 2: 2})
        # A well-formed fence that quotes a backtick is charged too: keep-only.
        self.assertEqual(dcs.unpaired_backticks("```lean\n`z_w`\n```\n"), {2: 2})

    def test_the_swallowed_citations_are_recovered_and_reported(self) -> None:
        """End to end on the swallowed block: both fragment citations come back."""
        source = self.markdown(self.SWALLOWED)
        tokens = [token for token, _line in source.tokens]
        self.assertIn("_alpha_gen", tokens)
        self.assertIn("beta{,_two}_gen", tokens)
        self.assertEqual(len(source.malformed), 2)
        self.assertTrue(all("pair into no code span" in item for item in source.malformed))

    def test_an_odd_number_of_fence_runs_is_reported(self) -> None:
        """The run left over opens a block that ends wherever the next run is."""
        self.assertIsNone(dcs.unbalanced_fence_run("```\ncode\n```\n"))
        self.assertIsNone(dcs.unbalanced_fence_run("no fence here\n"))
        self.assertEqual(dcs.unbalanced_fence_run("```\ncode\n```\nprose\n```\n"), 5)
        warnings = self.markdown("```\ncode\n```\nprose\n```\n").malformed
        self.assertEqual(len(warnings), 2)  # the leftover run is unpairable *and* odd
        self.assertTrue(all(":5:" in item for item in warnings))
        self.assertTrue(
            any("odd number of fenced-block delimiters" in item for item in warnings)
        )

    def test_the_fence_parity_check_catches_what_the_backtick_count_cannot(self) -> None:
        """A six-backtick run is one odd fence run whose backticks all pair off.

        ``_MD_TOKEN_RE`` reads it as a fenced match with an empty body, so both
        delimiters are accounted for and :func:`unpaired_backticks` is silent;
        only the run count says the file is malformed.
        """
        self.assertEqual(dcs.unpaired_backticks("a ``````\nb\n"), {})
        self.assertEqual(dcs.unbalanced_fence_run("a ``````\nb\n"), 1)
        (warning,) = self.markdown("a ``````\nb\n").malformed
        self.assertIn("odd number of fenced-block delimiters", warning)

    def test_an_unpairable_backtick_is_reported_with_its_line(self) -> None:
        """Both live shapes are caught: a stray backtick and a span across lines."""
        self.assertEqual(dcs.unpaired_backticks(self.FLIPPED), {1: 1})
        # docs/index.md:1223-1224: a span opened on one line, closed on the next.
        across = "bound `|edges d r| <=\nO(r)` (`alpha_card_le_beta` + `gamma_le'`),\n"
        self.assertEqual(dcs.unpaired_backticks(across), {1: 1, 2: 1})

    def test_the_flip_hides_the_citations_from_the_span_grammar(self) -> None:
        """Pin the defect itself: plain pairing sees neither citation after the flip."""
        paired = [
            token
            for match in dcs._MD_TOKEN_RE.finditer(self.FLIPPED)
            for token in dcs._citation_tokens(
                match.group(1) if match.group(1) is not None else (match.group(2) or "")
            )
        ]
        self.assertEqual(paired, [])

    def test_the_recovery_finds_every_pairing_the_line_admits(self) -> None:
        """Re-reading without pairing restores both hidden citations.

        They are the two shapes with no verbatim fallback: a brace alternation
        and an elided suffix. Neither can be rescued by the literal search that
        saves a complete name, so losing the token loses the citation outright.
        """
        tokens = [token for token, _line in self.markdown(self.FLIPPED).tokens]
        self.assertIn("synth_alpha{,_beta}_xyzzy", tokens)
        self.assertIn("_delta_gen", tokens)

    def test_the_defect_is_reported_not_only_repaired(self) -> None:
        """A silent repair leaves the Markdown broken for every other reader."""
        (warning,) = self.markdown(self.FLIPPED).malformed
        self.assertIn(":1:", warning)
        self.assertIn("pair into no code span", warning)

    def test_the_real_index_raises_its_three_warnings(self) -> None:
        """Measured on the current index: :1223, :1224 and :1832, nothing else.

        The three lines are the same three rows throughout; only their numbers
        move. The #4787 status reconciliation added 25 lines before these
        anchors and the stale-issue-reference correction added 2 more; this
        fixture follows their resulting positions.
        """
        index = next(source for source in docs() if source.label == "docs/index.md")
        self.assertEqual(
            sorted(dcs.unpaired_backticks(index.text)), [1223, 1224, 1832]
        )
        self.assertEqual(len(index.malformed), 3)
        self.assertTrue(any("docs/index.md:1832" in item for item in index.malformed))

    def test_the_real_index_recovers_the_line_1832_citations(self) -> None:
        """The elided suffixes of the Step 213 row are tokens again.

        The row reads `` `magnetizationAlongExhaustion_continuous_beta_gen` +
        `_differentiable_beta_gen` + ... ``; before the repair the line
        contributed 218 tokens and not one of them was any of these. The row now
        sits at :1832, after the #4787 documentation reconciliation and the later
        stale-issue-reference correction.
        """
        index = next(source for source in docs() if source.label == "docs/index.md")
        tokens = {token for token, line in index.tokens if line == 1832}
        for token in (
            "_differentiable_beta_gen",
            "_continuous_field_gen",
            "magnetizationAlongExhaustion_{continuous,differentiable}_beta_general_h_gen",
        ):
            self.assertIn(token, tokens)

    def test_the_hidden_declaration_is_no_longer_safe_to_delete(self) -> None:
        """End to end, on the declaration the defect offered up for deletion."""
        name = "Ambient.magnetizationAlongExhaustion_differentiable_beta_gen"
        verdicts, _cascade, _labels = dcs.classify(
            tree(), [name], docs(), allow_homonym=False
        )
        self.assertNotEqual(verdicts[0].verdict, dcs.SAFE, verdicts[0].reasons)


class ElidedFragmentTest(unittest.TestCase):
    """A suffix whose elided prefix is cited on the same line is not a family label.

    ``docs/index.md`` abbreviates a run of siblings by spelling the first in full
    and eliding the shared prefix of the rest. ``_differentiable_beta_gen``
    matches three declarations, so the family-label rule attributed it to nobody
    and the magnetization member came out ``safe-to-delete`` although the line
    cited it. Charging every match of every family label instead was measured
    (it touches 5895 of 11000 declarations and collapses ``safe-to-delete`` from
    1458 verdicts to 232, an 84% collapse, with ``--expect`` red) and rejected;
    the rule kept is the one the notation states.
    """

    TREE = {
        "IsingModel/SynthElision.lean": (
            "namespace IsingModel\n"
            "theorem alpha_xyzzy_continuous_gen : True := trivial\n"
            "theorem alpha_xyzzy_differentiable_gen : True := trivial\n"
            "theorem gamma_xyzzy_differentiable_gen : True := trivial\n"
            "end IsingModel\n"
        )
    }

    def doc(self, text: str, tokens: list[tuple[str, int]]) -> dcs.DocSource:
        """Return a documentation source carrying ``text`` and ``tokens``."""
        return dcs.DocSource(
            label="docs/index.md",
            text=text,
            starts=dcs.line_starts(text),
            tokens=tokens,
            unreadable=[],
        )

    def verdicts(self, text: str, tokens: list[tuple[str, int]]) -> list[dcs.Verdict]:
        """Classify both ``_differentiable_gen`` declarations against one doc line."""
        synthetic = synthetic_tree(self.TREE)
        names = [
            "IsingModel.alpha_xyzzy_differentiable_gen",
            "IsingModel.gamma_xyzzy_differentiable_gen",
        ]
        return dcs.classify(synthetic, names, [self.doc(text, tokens)], allow_homonym=False)[0]

    def test_the_elided_prefix_charges_only_the_sibling_that_shares_it(self) -> None:
        """``alpha_...`` cited in full lends its prefix to ``_differentiable_gen``."""
        text = "`alpha_xyzzy_continuous_gen` + `_differentiable_gen`\n"
        tokens = [("alpha_xyzzy_continuous_gen", 1), ("_differentiable_gen", 1)]
        by_name = {v.decl.final: v for v in self.verdicts(text, tokens)}
        self.assertEqual(by_name["alpha_xyzzy_differentiable_gen"].verdict, dcs.UNCERTAIN)
        self.assertEqual(by_name["gamma_xyzzy_differentiable_gen"].verdict, dcs.SAFE)

    def test_a_bare_family_label_still_rescues_nobody(self) -> None:
        """Without a cited prefix the fragment stays a label, and the exit-0 path stays open."""
        text = "the `_differentiable_gen` lemmas\n"
        verdicts = self.verdicts(text, [("_differentiable_gen", 1)])
        self.assertEqual([v.verdict for v in verdicts], [dcs.SAFE, dcs.SAFE])

    def test_the_helper_reads_the_prefix_and_not_the_suffix(self) -> None:
        """``elided_prefix_matches`` is exact about where the elision starts."""
        matched = [
            decl
            for final, decl in synthetic_tree(self.TREE).finals
            if final.endswith("_differentiable_gen")
        ]
        self.assertEqual(len(matched), 2)
        charged = dcs.elided_prefix_matches(
            "_differentiable_gen", matched, {"alpha_xyzzy_continuous_gen"}
        )
        self.assertEqual([decl.final for decl in charged], ["alpha_xyzzy_differentiable_gen"])
        self.assertEqual(
            dcs.elided_prefix_matches("_differentiable_gen", matched, {"delta_unrelated"}), []
        )


class NarrowGlobCitationTest(unittest.TestCase):
    """A glob citation naming few declarations is charged to all of them.

    Same fail-open shape as :class:`ElidedFragmentTest`, one channel over. Until
    :data:`dead_candidate_scan.MAX_CHARGED_GLOB_MATCHES` landed, *every*
    glob/ellipsis token resolving to two or more declarations was filed as a
    family label and attributed to nobody, so a citation that resolves exactly
    -- ``docs/index.md:1427`` expands to
    ``freeEnergyAlongExhaustion_latticeGraph_ge_log_two*`` (2 declarations),
    ``docs/index.md:1328`` writes ``freeEnergy_*_tendsto_of_abs_h``
    (4 declarations) -- left every declaration it names printing "no citation in
    the scanned documentation", the sentence that licenses a deletion. Neither
    has a verbatim fallback: the brace/glob spelling means the full name is
    nowhere in the file.

    The threshold is a cost knob, so it is pinned from both sides: at or below
    it every match is charged, above it nothing is and the label is *reported*.
    """

    NARROW_TREE = {
        "IsingModel/SynthGlobPair.lean": (
            "namespace IsingModel\n"
            "theorem synth_glob_ge_log_two_left : True := trivial\n"
            "theorem synth_glob_ge_log_two_right : True := trivial\n"
            "end IsingModel\n"
        )
    }

    @staticmethod
    def wide_tree(count: int) -> dict[str, str]:
        """Return a tree of ``count`` siblings that one glob names together."""
        body = "".join(
            f"theorem synth_wide_{index}_tendsto : True := trivial\n" for index in range(count)
        )
        return {"IsingModel/SynthGlobWide.lean": f"namespace IsingModel\n{body}end IsingModel\n"}

    def doc(self, text: str, tokens: list[tuple[str, int]]) -> dcs.DocSource:
        """Return a documentation source carrying ``text`` and ``tokens``."""
        return dcs.DocSource(
            label="docs/index.md",
            text=text,
            starts=dcs.line_starts(text),
            tokens=tokens,
            unreadable=[],
        )

    def classify(
        self, sources: dict[str, str], names: list[str], token: str
    ) -> tuple[list[dcs.Verdict], dict[str, list[str]]]:
        """Classify ``names`` against a single documentation line citing ``token``."""
        text = f"the `{token}` results\n"
        verdicts, _cascade, labels = dcs.classify(
            synthetic_tree(sources), names, [self.doc(text, [(token, 1)])], allow_homonym=False
        )
        return verdicts, labels

    def pair_names(self) -> list[str]:
        """The two declarations of :attr:`NARROW_TREE`."""
        return [
            "IsingModel.synth_glob_ge_log_two_left",
            "IsingModel.synth_glob_ge_log_two_right",
        ]

    def test_a_glob_naming_two_declarations_charges_both(self) -> None:
        """The ``ge_log_two*`` shape: both matches are cited, so neither is safe."""
        verdicts, labels = self.classify(
            self.NARROW_TREE, self.pair_names(), "synth_glob_ge_log_two*"
        )
        self.assertEqual([v.verdict for v in verdicts], [dcs.UNCERTAIN, dcs.UNCERTAIN])
        self.assertEqual(labels, {})
        for verdict in verdicts:
            self.assertTrue(
                any("synth_glob_ge_log_two*" in cit for cit in verdict.doc_citations),
                verdict.doc_citations,
            )

    def test_a_glob_naming_four_declarations_charges_all_four(self) -> None:
        """The ``freeEnergy_*_tendsto_of_abs_h`` shape, one slot in the middle."""
        names = [f"IsingModel.synth_wide_{index}_tendsto" for index in range(4)]
        verdicts, labels = self.classify(self.wide_tree(4), names, "synth_wide_*_tendsto")
        self.assertEqual([v.verdict for v in verdicts], [dcs.UNCERTAIN] * 4)
        self.assertEqual(labels, {})

    def test_a_glob_above_the_threshold_charges_nobody_and_is_reported(self) -> None:
        """One match past the knob the citation is a family label again.

        ``correlation_*_*`` names 219 declarations in the real documentation;
        charging such a label would drag whole subsystems into ``uncertain``.
        The residue is fail-open by construction, so it must at least be
        *printed*: the label lands in ``family_labels``, which :func:`report`
        renders on every run.
        """
        count = dcs.MAX_CHARGED_GLOB_MATCHES + 1
        names = [f"IsingModel.synth_wide_{index}_tendsto" for index in range(count)]
        verdicts, labels = self.classify(self.wide_tree(count), names, "synth_wide_*_tendsto")
        self.assertEqual([v.verdict for v in verdicts], [dcs.SAFE] * count)
        self.assertEqual(list(labels), ["docs/index.md:1 `synth_wide_*_tendsto`"])
        self.assertEqual(labels["docs/index.md:1 `synth_wide_*_tendsto`"], [f"{count} declarations"])

    def test_the_old_exoneration_would_turn_this_red(self) -> None:
        """Mutation test: with the knob at 1, every multi-match glob is exonerated.

        ``MAX_CHARGED_GLOB_MATCHES = 1`` is exactly the rule this class repairs
        (the branch read ``else []`` for every ``len(matched) >= 2``), so the
        pinned verdicts above must depend on the threshold and not on some other
        part of the pipeline.
        """
        original = dcs.MAX_CHARGED_GLOB_MATCHES
        dcs.MAX_CHARGED_GLOB_MATCHES = 1
        try:
            verdicts, labels = self.classify(
                self.NARROW_TREE, self.pair_names(), "synth_glob_ge_log_two*"
            )
        finally:
            dcs.MAX_CHARGED_GLOB_MATCHES = original
        self.assertEqual([v.verdict for v in verdicts], [dcs.SAFE, dcs.SAFE])
        self.assertEqual(list(labels), ["docs/index.md:1 `synth_glob_ge_log_two*`"])

    def test_a_charged_glob_never_publishes(self) -> None:
        """A glob is evidence of a citation, not of a verbatim one.

        The charge string keeps the ``shorthand `` prefix, which is what makes
        the repair monotone: only ``exact `` promotes to ``published-result``
        (and ``published-result`` leaves the delete-closure seed alone), while
        ``shorthand `` forces ``uncertain``. A glob charged as ``exact `` would
        assert a verbatim citation that is not in the file.
        """
        verdicts, _labels = self.classify(
            self.NARROW_TREE, self.pair_names(), "synth_glob_ge_log_two*"
        )
        for verdict in verdicts:
            self.assertNotEqual(verdict.verdict, dcs.PUBLISHED)
            self.assertTrue(
                all(not cit.startswith("exact ") for cit in verdict.doc_citations),
                verdict.doc_citations,
            )

    def test_the_glob_token_survives_the_real_tokenizer(self) -> None:
        """The synthetic tokens above are what the Markdown channel really produces."""
        self.assertEqual(
            dcs._citation_tokens("freeEnergy_*_tendsto_of_abs_h"),
            ["freeEnergy_*_tendsto_of_abs_h"],
        )
        self.assertEqual(
            dcs.expand_braces("freeEnergyAlongExhaustion_latticeGraph_{nonneg*,ge_log_two*}"),
            [
                "freeEnergyAlongExhaustion_latticeGraph_ge_log_two*",
                "freeEnergyAlongExhaustion_latticeGraph_nonneg*",
            ],
        )

    def test_the_two_real_citations_still_resolve(self) -> None:
        """End to end on the real tree: the six declarations of the report exist.

        Pinned because the repair is worth nothing if the globs stop resolving:
        both tokens are read off the real ``docs/index.md`` rows, and their
        matches are the declarations that used to print "no citation".
        """
        cache: dict[str, list[dcs.Decl] | None] = {}
        pair = dcs._resolve_fragment(
            tree(), "freeEnergyAlongExhaustion_latticeGraph_ge_log_two*", cache
        )
        quad = dcs._resolve_fragment(tree(), "freeEnergy_*_tendsto_of_abs_h", cache)
        self.assertEqual(len(pair), 2)
        self.assertEqual(len(quad), 4)
        for matched in (pair, quad):
            self.assertLessEqual(len(matched), dcs.MAX_CHARGED_GLOB_MATCHES)

    def test_the_six_declarations_are_no_longer_safe_to_delete(self) -> None:
        """The named regression, on the real tree and the real documentation."""
        names = [
            "Ambient.freeEnergyAlongExhaustion_latticeGraph_ge_log_two",
            "Ambient.freeEnergyAlongExhaustion_latticeGraph_ge_log_two_cosh",
            "Concrete.freeEnergy_centeredSlab_tendsto_of_abs_h",
            "Concrete.freeEnergy_linearBox_tendsto_of_abs_h",
            "Concrete.freeEnergy_slabBrick_tendsto_of_abs_h",
            "Concrete.freeEnergy_stripeBrick2D_tendsto_of_abs_h",
        ]
        verdicts, _cascade, _labels = dcs.classify(tree(), names, docs(), allow_homonym=False)
        for verdict in verdicts:
            self.assertNotEqual(verdict.verdict, dcs.SAFE, verdict.name)
            self.assertTrue(
                any(
                    cit.startswith("shorthand ") and "*" in cit
                    for cit in verdict.doc_citations
                ),
                (verdict.name, verdict.doc_citations),
            )


class QualifiedGlobCitationTest(unittest.TestCase):
    """Fully-qualified ``IsingModel.`` globs resolve against full names only."""

    ROW_3867_TOKEN = (
        "IsingModel.{magnetization,truncated2,susceptibility,"
        "magnetization_total}_convergent_*"
    )
    ROW_3867 = {
        "IsingModel.magnetization_convergent_*": [
            "IsingModel.magnetization_convergent_subgraph",
            "IsingModel.magnetization_convergent_J",
            "IsingModel.magnetization_convergent_beta",
            "IsingModel.magnetization_convergent_h",
        ],
        "IsingModel.magnetization_total_convergent_*": [
            "IsingModel.magnetization_total_convergent_subgraph",
        ],
        "IsingModel.susceptibility_convergent_*": [
            "IsingModel.susceptibility_convergent_J",
            "IsingModel.susceptibility_convergent_h",
            "IsingModel.susceptibility_convergent_beta",
            "IsingModel.susceptibility_convergent_subgraph",
        ],
        "IsingModel.truncated2_convergent_*": [
            "IsingModel.truncated2_convergent_J",
            "IsingModel.truncated2_convergent_h",
            "IsingModel.truncated2_convergent_beta",
            "IsingModel.truncated2_convergent_subgraph",
        ],
    }
    ROW_27030_TOKEN = (
        "IsingModel.Ambient."
        "pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_*"
    )
    ROW_27030 = [
        "IsingModel.Ambient."
        "pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_pseudoMassG",
        "IsingModel.Ambient."
        "pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_exp_smallReg",
        "IsingModel.Ambient."
        "pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_exp_div_pow_largeReg",
        "IsingModel.Ambient."
        "pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_tanh_pow_smallReg",
        "IsingModel.Ambient."
        "pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_exp_trichotomy",
        "IsingModel.Ambient."
        "pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_exp_div_max_pow",
        "IsingModel.Ambient."
        "pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_tanh_exp_trichotomy",
    ]
    HOMONYM_TREE = {
        "IsingModel/SynthQualifiedGlob.lean": (
            "namespace IsingModel\n"
            "theorem foo_same : True := trivial\n"
            "namespace Ambient\n"
            "theorem foo_same : True := trivial\n"
            "end Ambient\n"
            "end IsingModel\n"
            "namespace Elsewhere\n"
            "theorem foo_same : True := trivial\n"
            "end Elsewhere\n"
        )
    }

    @staticmethod
    def doc(tokens: list[tuple[str, int]]) -> dcs.DocSource:
        """Return a synthetic token-only documentation source."""
        return dcs.DocSource(
            label="docs/index.md",
            text="",
            starts=[0],
            tokens=tokens,
            unreadable=[],
        )

    def real_names(self) -> list[str]:
        """Return the exact 20 declarations named at the two real sites."""
        return [
            name
            for names in self.ROW_3867.values()
            for name in names
        ] + self.ROW_27030

    def test_the_two_real_sites_resolve_to_13_and_7_declarations(self) -> None:
        """Brace composition yields 4/1/4/4 matches, then the second site 7."""
        guide = next(source for source in docs() if source.label == "tex/proof-guide.tex")
        self.assertIn((self.ROW_3867_TOKEN, 3867), guide.tokens)
        self.assertIn((self.ROW_27030_TOKEN, 27030), guide.tokens)
        patterns = dcs.expand_citation_token(self.ROW_3867_TOKEN)
        self.assertEqual(patterns, sorted(self.ROW_3867))

        cache: dict[str, list[dcs.Decl] | None] = {}
        resolved = [dcs._resolve_fragment(tree(), pattern, cache) for pattern in patterns]
        resolved.append(dcs._resolve_fragment(tree(), self.ROW_27030_TOKEN, cache))
        self.assertEqual([len(matches or []) for matches in resolved], [4, 1, 4, 4, 7])
        expected = [self.ROW_3867[pattern] for pattern in patterns] + [self.ROW_27030]
        self.assertEqual(
            [[decl.full for decl in matches or []] for matches in resolved],
            expected,
        )

    def test_the_two_real_sites_add_exactly_20_shorthand_charges(self) -> None:
        """The raw row tokens charge 13 plus 7 declarations, never as exact."""
        verdicts = dcs.classify(
            tree(), self.real_names(), docs(), allow_homonym=False
        )[0]
        counts = {3867: 0, 27030: 0}
        for verdict in verdicts:
            for citation in verdict.doc_citations:
                for line, token in (
                    (3867, self.ROW_3867_TOKEN),
                    (27030, self.ROW_27030_TOKEN),
                ):
                    if citation.startswith(f"shorthand tex/proof-guide.tex:{line}:"):
                        self.assertIn(token, citation)
                        counts[line] += 1
                    self.assertFalse(
                        citation.startswith(f"exact tex/proof-guide.tex:{line}:")
                        and token in citation,
                        (verdict.decl.full, citation),
                    )
        self.assertEqual(counts, {3867: 13, 27030: 7})

    def test_qualified_resolution_is_namespace_exact_and_cache_separated(self) -> None:
        """A qualified glob selects the root namespace, while bare keeps finals."""
        synthetic = synthetic_tree(self.HOMONYM_TREE)
        expected_bare = [
            "IsingModel.foo_same",
            "IsingModel.Ambient.foo_same",
            "Elsewhere.foo_same",
        ]
        for qualified_first in (False, True):
            cache: dict[str, list[dcs.Decl] | None] = {}
            names = (
                ["IsingModel.foo_*", "foo_*"]
                if qualified_first
                else ["foo_*", "IsingModel.foo_*"]
            )
            resolved = {
                name: dcs._resolve_fragment(synthetic, name, cache)
                for name in names
            }
            self.assertEqual(
                [decl.full for decl in resolved["IsingModel.foo_*"] or []],
                ["IsingModel.foo_same"],
            )
            self.assertEqual(
                [decl.full for decl in resolved["foo_*"] or []],
                expected_bare,
            )

    def test_qualified_globs_keep_the_1_2_10_11_threshold(self) -> None:
        """At most ten matches are shorthand-only; eleven is a family label."""
        groups = ((1, "one"), (2, "two"), (10, "ten"), (11, "eleven"))
        body = "namespace IsingModel\n"
        names_by_count: dict[int, list[str]] = {}
        for count, label in groups:
            names_by_count[count] = [
                f"IsingModel.qglob_{label}_{index}" for index in range(count)
            ]
            body += "".join(
                f"theorem qglob_{label}_{index} : True := trivial\n"
                for index in range(count)
            )
        body += "end IsingModel\n"
        synthetic = synthetic_tree({"IsingModel/SynthQualifiedThreshold.lean": body})
        tokens = [
            (f"IsingModel.qglob_{label}_*", lineno)
            for lineno, (_count, label) in enumerate(groups, 1)
        ]
        names = [name for count, _label in groups for name in names_by_count[count]]
        verdicts, _cascade, labels = dcs.classify(
            synthetic, names, [self.doc(tokens)], allow_homonym=False
        )
        by_name = {verdict.decl.full: verdict for verdict in verdicts}
        for count, label in groups[:3]:
            token = f"IsingModel.qglob_{label}_*"
            for name in names_by_count[count]:
                verdict = by_name[name]
                self.assertEqual(verdict.verdict, dcs.UNCERTAIN, name)
                self.assertEqual(len(verdict.doc_citations), 1, name)
                self.assertTrue(verdict.doc_citations[0].startswith("shorthand "))
                self.assertIn(token, verdict.doc_citations[0])
        for name in names_by_count[11]:
            self.assertEqual(by_name[name].verdict, dcs.SAFE, name)
            self.assertEqual(by_name[name].doc_citations, [], name)
        key = "docs/index.md:4 `IsingModel.qglob_eleven_*`"
        self.assertEqual(labels, {key: ["11 declarations"]})

    def test_unsupported_relative_and_broad_patterns_remain_conservative(self) -> None:
        """Relative/malformed prose stays inert; the broad real glob is a label."""
        synthetic = synthetic_tree(self.HOMONYM_TREE)
        for token in (
            "Unknown.foo_*",
            "Ambient.foo_*",
            "IsingModel..foo_*",
            "IsingModel.*.foo_*",
            "IsingModel.foo_**",
        ):
            self.assertEqual(dcs._resolve_fragment(synthetic, token, {}), [], token)
        for token in (
            "https://example.test/IsingModel.foo_*",
            "docs/IsingModel.foo_*",
        ):
            self.assertEqual(dcs._citation_tokens(token), [], token)

        broad = dcs._resolve_fragment(tree(), "IsingModel.*", {})
        # Census pin.  10571 before PR #4839, which is a net -4 on the library:
        # eight `magnetizationAlongExhaustion` regularity wrappers left
        # `AmbientLattice/BetaDerivativeMagnetization.lean` (six retired as
        # duplicates, two re-homed) and four declarations were added (the two
        # re-homed corollaries plus the two `correlationAlongExhaustion`
        # family equations in `AmbientLattice/Exhaustion.lean`).  PR #4859 is a
        # further net -1 (10567 -> 10566): `Inequalities/Lebowitz/FourfoldSite.lean`
        # declared a duplicate `Lebowitz.sum_spin`, a specialization
        # (`α := ℝ`) of the imported general `IsingModel.sum_spin`, and it is
        # retired.  Issue #4869 is a further net -1 (10566 -> 10565):
        # `AscoliData/ClosedBallConversions/DeviationDirect.lean` declared
        # `toRangeRelCompactData_viaLocal_direct` as a byte-identical twin of
        # `toRangeRelCompactData_direct` in the same namespace, and the #4854
        # pilot left it with no consumer, so it is retired.
        self.assertEqual(len(broad or []), 10565)
        selected = [
            dcs.Verdict(name=name, decl=dcs.resolve_candidate(tree(), name, False)[0])
            for name in self.real_names()
        ]
        labels: dict[str, list[str]] = {}
        dcs._apply_doc_channel(
            tree(), selected, [self.doc([("IsingModel.*", 1)])], labels
        )
        self.assertTrue(all(not verdict.doc_citations for verdict in selected))
        self.assertEqual(
            labels,
            {"docs/index.md:1 `IsingModel.*`": ["10565 declarations"]},
        )


class ResolvedGlobElisionHeadTest(unittest.TestCase):
    """F6: a chargeable resolved glob head may seed a same-line sibling suffix."""

    ROW_HEAD = "freeEnergyInfinite_..._bounds"
    ROW_SUFFIX = "_monotone_{J,h,beta}"
    ROW_PREFIX = "freeEnergyInfinite_latticeGraph_cubicExhaustion"
    ROW_TARGETS = [
        "IsingModel.Ambient."
        f"freeEnergyInfinite_latticeGraph_cubicExhaustion_monotone_{parameter}"
        for parameter in ("J", "h", "beta")
    ]

    @staticmethod
    def synthetic_tree(finals: list[str]) -> dcs.Tree:
        """Return a one-file tree containing independent theorems named by ``finals``."""
        body = "".join(f"theorem {final} : True := trivial\n" for final in finals)
        return synthetic_tree(
            {
                "IsingModel/SynthResolvedGlobElision.lean": (
                    f"namespace IsingModel\n{body}end IsingModel\n"
                )
            }
        )

    @staticmethod
    def doc(label: str, tokens: list[tuple[str, int]]) -> dcs.DocSource:
        """Return token-only documentation with enough physical lines for ``tokens``."""
        line_count = max((lineno for _token, lineno in tokens), default=1)
        text = "citation\n" * line_count
        return dcs.DocSource(
            label=label,
            text=text,
            starts=dcs.line_starts(text),
            tokens=tokens,
            unreadable=[],
        )

    def classify(
        self,
        finals: list[str],
        candidates: list[str],
        docs_list: list[dcs.DocSource],
    ) -> tuple[list[dcs.Verdict], dict[str, list[str]]]:
        """Classify ``candidates`` in a synthetic tree and return verdicts and labels."""
        verdicts, _cascade, labels = dcs.classify(
            self.synthetic_tree(finals),
            [f"IsingModel.{candidate}" for candidate in candidates],
            docs_list,
            allow_homonym=False,
        )
        return verdicts, labels

    def test_F6_HEAD_RESOLVE_unqualified_ellipsis_seeds_shorthand_in_either_order(
        self,
    ) -> None:
        """A resolved head licenses its three immediate siblings, never exact evidence."""
        head = "alpha_xyzzy_bounds"
        targets = [f"alpha_xyzzy_monotone_{parameter}" for parameter in ("J", "h", "beta")]
        decoys = [f"gamma_xyzzy_monotone_{parameter}" for parameter in ("J", "h", "beta")]
        finals = [head, *targets, *decoys]
        token_orders = (
            [("alpha_..._bounds", 1), ("_monotone_{J,h,beta}", 1)],
            [("_monotone_{J,h,beta}", 1), ("alpha_..._bounds", 1)],
        )

        observed = []
        for tokens in token_orders:
            verdicts, _labels = self.classify(
                finals, targets, [self.doc("docs/f6-order.md", tokens)]
            )
            observed.append(
                [
                    (
                        verdict.verdict,
                        sum(
                            citation.startswith("shorthand docs/f6-order.md:1:")
                            and "`_monotone_{J,h,beta}`" in citation
                            for citation in verdict.doc_citations
                        ),
                        any(
                            citation.startswith("exact ")
                            for citation in verdict.doc_citations
                        ),
                    )
                    for verdict in verdicts
                ]
            )

        expected = [[(dcs.UNCERTAIN, 1, False)] * 3] * 2
        self.assertEqual(observed, expected)

    def test_F6_REAL_1393_resolved_head_protects_the_exact_target_triple(self) -> None:
        """The real row adds one suffix shorthand, and no exact claim, to each target."""
        index = next(source for source in docs() if source.label == "docs/index.md")
        self.assertIn((self.ROW_HEAD, 1393), index.tokens)
        self.assertIn((self.ROW_SUFFIX, 1393), index.tokens)
        resolved = dcs._resolve_fragment(tree(), self.ROW_HEAD, {})
        self.assertEqual(
            [decl.full for decl in resolved or []],
            [f"IsingModel.Ambient.{self.ROW_PREFIX}_bounds"],
        )

        verdicts = dcs.classify(
            tree(), self.ROW_TARGETS, docs(), allow_homonym=False
        )[0]
        observed = []
        for verdict in verdicts:
            row_shorthand = [
                citation
                for citation in verdict.doc_citations
                if citation.startswith("shorthand docs/index.md:1393:")
                and f"`{self.ROW_SUFFIX}`" in citation
            ]
            observed.append(
                (
                    verdict.decl.full,
                    verdict.verdict,
                    len(row_shorthand),
                    any(
                        citation.startswith("exact ")
                        for citation in verdict.doc_citations
                    ),
                )
            )
        self.assertEqual(
            observed,
            [(name, dcs.UNCERTAIN, 1, False) for name in self.ROW_TARGETS],
        )

    def test_F6_HEAD_RESOLVE_ten_match_head_seeds_an_immediate_sibling(self) -> None:
        """The positive threshold edge is eligible to establish a suffix prefix."""
        heads = ["limit_seed_bounds"] + [
            f"limit_extra_{index}_bounds"
            for index in range(dcs.MAX_CHARGED_GLOB_MATCHES - 1)
        ]
        targets = ["limit_seed_monotone_J", "decoy_seed_monotone_J"]
        synthetic = self.synthetic_tree([*heads, *targets])
        token = "limit_..._bounds"
        resolved = dcs._resolve_fragment(synthetic, token, {})
        self.assertEqual(len(resolved or []), dcs.MAX_CHARGED_GLOB_MATCHES)
        verdicts, _cascade, _labels = dcs.classify(
            synthetic,
            [f"IsingModel.{target}" for target in targets],
            [self.doc("docs/f6-ten.md", [(token, 1), ("_monotone_J", 1)])],
            allow_homonym=False,
        )
        self.assertEqual(
            [
                (
                    verdict.verdict,
                    any(
                        citation.startswith("shorthand docs/f6-ten.md:1:")
                        and "`_monotone_J`" in citation
                        for citation in verdict.doc_citations
                    ),
                )
                for verdict in verdicts
            ],
            [(dcs.UNCERTAIN, True), (dcs.SAFE, False)],
        )

    def test_F6_PREFIX_BOUNDARY_blocks_divergent_and_colliding_heads(self) -> None:
        """Resolved heads cannot cross the immediate-component or family boundary."""
        cases = (
            (
                ["alpha_xyzzy_monotone_bounds", "alpha_xyzzy_monotone_J",
                 "gamma_xyzzy_monotone_J"],
                "alpha_..._monotone_bounds",
                "_monotone_J",
                "alpha_xyzzy_monotone_J",
            ),
            (
                ["alphabet_any_bounds", "alpha_xyzzy_monotone_J",
                 "gamma_xyzzy_monotone_J"],
                "alphabet_..._bounds",
                "_xyzzy_monotone_J",
                "alpha_xyzzy_monotone_J",
            ),
            (
                ["delta_xyzzy_bounds", "alpha_xyzzy_monotone_J",
                 "gamma_xyzzy_monotone_J"],
                "delta_..._bounds",
                "_monotone_J",
                "alpha_xyzzy_monotone_J",
            ),
        )
        observed = []
        for finals, head, suffix, target in cases:
            verdicts, _labels = self.classify(
                finals,
                [target],
                [self.doc("docs/f6-boundary.md", [(head, 1), (suffix, 1)])],
            )
            observed.append((verdicts[0].verdict, verdicts[0].doc_citations))
        self.assertEqual(observed, [(dcs.SAFE, [])] * len(cases))

    def test_F6_PREFIX_BOUNDARY_blocks_adjacent_lines_and_other_sources(self) -> None:
        """A head seed cannot cross a physical line or a documentation source."""
        finals = [
            "alpha_xyzzy_bounds",
            "alpha_xyzzy_monotone_J",
            "gamma_xyzzy_monotone_J",
        ]
        separated = (
            [
                self.doc(
                    "docs/f6-lines.md",
                    [("alpha_..._bounds", 1), ("_monotone_J", 2)],
                )
            ],
            [
                self.doc("docs/f6-head.md", [("alpha_..._bounds", 1)]),
                self.doc("docs/f6-suffix.md", [("_monotone_J", 1)]),
            ],
        )
        observed = []
        for docs_list in separated:
            verdicts, _labels = self.classify(
                finals, ["alpha_xyzzy_monotone_J"], docs_list
            )
            observed.append((verdicts[0].verdict, verdicts[0].doc_citations))
        self.assertEqual(observed, [(dcs.SAFE, []), (dcs.SAFE, [])])

    def test_F6_CONSERVATIVE_bad_or_broad_heads_do_not_license_suffixes(self) -> None:
        """Unresolved, malformed, zero, relative, and eleven-match heads stay inert."""
        base_finals = [
            "alpha_xyzzy_bounds",
            "alpha_xyzzy_monotone_J",
            "gamma_xyzzy_monotone_J",
        ]
        bad_heads = (
            "alpha_missing_bounds",
            "IsingModel.",
            "missing_..._bounds",
            "Ambient.alpha_..._bounds",
        )
        observed = []
        for index, head in enumerate(bad_heads):
            verdicts, _labels = self.classify(
                base_finals,
                ["alpha_xyzzy_monotone_J"],
                [
                    self.doc(
                        f"docs/f6-bad-{index}.md",
                        [(head, 1), ("_monotone_J", 1)],
                    )
                ],
            )
            observed.append((verdicts[0].verdict, verdicts[0].doc_citations))

        broad_heads = ["limit_seed_bounds"] + [
            f"limit_extra_{index}_bounds"
            for index in range(dcs.MAX_CHARGED_GLOB_MATCHES)
        ]
        broad_targets = ["limit_seed_monotone_J", "decoy_seed_monotone_J"]
        broad_tree = self.synthetic_tree([*broad_heads, *broad_targets])
        broad_token = "limit_..._bounds"
        self.assertEqual(
            len(dcs._resolve_fragment(broad_tree, broad_token, {}) or []),
            dcs.MAX_CHARGED_GLOB_MATCHES + 1,
        )
        broad_verdicts, _cascade, labels = dcs.classify(
            broad_tree,
            [f"IsingModel.{target}" for target in broad_targets],
            [
                self.doc(
                    "docs/f6-eleven.md",
                    [(broad_token, 1), ("_monotone_J", 1)],
                )
            ],
            allow_homonym=False,
        )
        observed.append(
            (broad_verdicts[0].verdict, broad_verdicts[0].doc_citations)
        )

        self.assertEqual(observed, [(dcs.SAFE, [])] * (len(bad_heads) + 1))
        self.assertEqual(
            labels["docs/f6-eleven.md:1 `limit_..._bounds`"],
            ["11 declarations"],
        )


class DocScopeTest(unittest.TestCase):
    """Which files the documentation channel reads.

    A ``safe-to-delete`` verdict prints "no citation in the scanned
    documentation". While only ``docs/index.md`` and the guide were read, that
    sentence was a claim about two files: ``README.md`` cites
    ``ConvergenceRegion.derivativeLimit_on_window`` and was invisible.
    """

    def test_readme_and_every_docs_markdown_are_scanned(self) -> None:
        """The scanned set is README.md, docs/**/*.md and the TeX guide."""
        labels = {source.label for source in docs()}
        self.assertIn("README.md", labels)
        self.assertIn("docs/index.md", labels)
        self.assertIn("tex/proof-guide.tex", labels)
        for path in dcs.DOCS_DIR.rglob("*.md"):
            self.assertIn(dcs.rel(path), labels)

    def test_readme_citation_is_seen(self) -> None:
        """The real README citation reaches the channel, verbatim and as a token."""
        readme = next(source for source in docs() if source.label == "README.md")
        name = "ConvergenceRegion.derivativeLimit_on_window"
        self.assertIn(name, readme.text)
        self.assertIn(name, [token for token, _line in readme.tokens])


class MissingDocumentationTest(unittest.TestCase):
    """A documentation channel that vanishes must stop the run, not shrink it.

    Every citation lives in one of three tracked files. If one of them is gone
    -- moved, renamed, checked out partially -- the channel contributes no token
    and no literal text, so every name cited *only* there becomes uncited, and
    the run still prints "no citation in the scanned documentation": a
    ``safe-to-delete`` verdict resting on evidence that was never read. So the
    absence is a hard failure (exit 2), like the canaries.
    """

    def missing(self, attribute: str, replacement: Path) -> list[str]:
        """Run ``require_documentation`` with one path redirected to a missing file."""
        original = getattr(dcs, attribute)
        setattr(dcs, attribute, replacement)
        try:
            with self.assertRaises(dcs.Inconsistency) as caught:
                dcs.require_documentation()
            return [str(caught.exception)]
        finally:
            setattr(dcs, attribute, original)

    def test_each_channel_is_required(self) -> None:
        """The guide, the README and the progress index each abort when absent."""
        for attribute, replacement, expected in (
            ("TEX_GUIDE", dcs.REPO_ROOT / "tex" / "no-such-guide.tex", "tex/no-such-guide.tex"),
            ("README", dcs.REPO_ROOT / "no-such-readme.md", "no-such-readme.md"),
            ("DOCS_DIR", dcs.REPO_ROOT / "no-such-docs", "no-such-docs/index.md"),
        ):
            (message,) = self.missing(attribute, replacement)
            self.assertIn(expected, message)

    def test_the_real_documentation_satisfies_the_requirement(self) -> None:
        """The check must not fire on a healthy tree."""
        dcs.require_documentation()

    def test_a_missing_guide_fails_the_whole_run(self) -> None:
        """End to end: the CLI exits 2 rather than reporting a silent tex channel."""
        original = dcs.TEX_GUIDE
        dcs.TEX_GUIDE = dcs.REPO_ROOT / "tex" / "no-such-guide.tex"
        try:
            out, err = io.StringIO(), io.StringIO()
            with redirect_stdout(out), redirect_stderr(err):
                code = dcs.main(["--name", "freeEnergyAlongExhaustion_nonneg_of_ferromagnetic"])
        finally:
            dcs.TEX_GUIDE = original
        self.assertEqual(code, dcs.EXIT_INCONSISTENT, out.getvalue())
        self.assertIn("no-such-guide.tex", err.getvalue())
        self.assertNotIn("safe-to-delete", out.getvalue())


def synthetic_tree(sources: dict[str, str]) -> dcs.Tree:
    """Build a tree from ``{repo-relative path: source text}``."""
    return dcs.build_tree([(dcs.REPO_ROOT / path, text) for path, text in sources.items()])


def synthetic_doc(text: str, label: str = "docs/index.md") -> dcs.DocSource:
    """Return a documentation source carrying ``text`` and no citation token."""
    return dcs.DocSource(
        label=label, text=text, starts=dcs.line_starts(text), tokens=[], unreadable=[]
    )


class DeleteClosureTest(unittest.TestCase):
    """The delete-closure may only excuse references from candidates that go away.

    The failure this pins down: a candidate retained by the very same run
    (published, uncertain, attribute- or kind-driven) was still counted as
    deleted by the closure, so a lemma consumed *only* by that keeper came out
    ``safe-to-delete``. False safe is the one fatal verdict of this tool.
    """

    BASE = "IsingModel.synthetic_closure_base_xyzzy"
    USER = "IsingModel.synthetic_closure_user_xyzzy"

    def build(self) -> dcs.Tree:
        """Return a two-file tree where ``USER`` is the sole consumer of ``BASE``."""
        return synthetic_tree(
            {
                "IsingModel/SynthClosureA.lean": (
                    "namespace IsingModel\n"
                    "theorem synthetic_closure_base_xyzzy : True := trivial\n"
                    "end IsingModel\n"
                ),
                "IsingModel/SynthClosureB.lean": (
                    "namespace IsingModel\n"
                    "theorem synthetic_closure_user_xyzzy : True :=\n"
                    "  synthetic_closure_base_xyzzy\n"
                    "end IsingModel\n"
                ),
            }
        )

    def classify(self, docs_list: list[dcs.DocSource]) -> dict[str, str]:
        """Classify both synthetic candidates against ``docs_list``."""
        verdicts, _cascade, _labels = dcs.classify(
            self.build(), [self.BASE, self.USER], docs_list, allow_homonym=False
        )
        return {verdict.decl.full: verdict.verdict for verdict in verdicts}

    def test_both_deleted_together_is_still_safe(self) -> None:
        """The closure must keep working: nothing retains either candidate here."""
        result = self.classify([])
        self.assertEqual(result[self.BASE], dcs.SAFE)
        self.assertEqual(result[self.USER], dcs.SAFE)

    def test_candidate_consumed_by_a_retained_candidate_is_not_safe(self) -> None:
        """A module citation retains the consumer, so the consumed lemma stays."""
        # The citation names the *consumer's* module only, which is what makes
        # the consumer uncertain while leaving the base candidate untouched.
        result = self.classify([synthetic_doc("see SynthClosureB.lean for the proof")])
        self.assertEqual(result[self.USER], dcs.UNCERTAIN)
        self.assertNotEqual(result[self.BASE], dcs.SAFE)
        self.assertEqual(result[self.BASE], dcs.LOAD_BEARING)

    def test_no_safe_candidate_is_consumed_by_a_retained_one_on_the_real_family(self) -> None:
        """The same invariant, over the 245-candidate ``_ferromagnetic`` family."""
        verdicts = family_verdicts()
        safe_keys = {v.decl.key for v in verdicts if v.verdict == dcs.SAFE}
        for verdict in verdicts:
            if verdict.verdict != dcs.SAFE:
                continue
            for occ in verdict.consumers:
                self.assertIsNotNone(occ.owner, f"{verdict.name}: file-level consumer")
                self.assertIn(
                    occ.owner.key,
                    safe_keys,
                    f"{verdict.name} is safe-to-delete but consumed by the retained "
                    f"{occ.owner.full} ({occ.file}:{occ.line})",
                )


class SameLineAttributeTest(unittest.TestCase):
    """``@[simp] theorem foo`` declares ``foo`` on the attribute line.

    Dropping the rest of that line deletes ``foo`` from the declaration table,
    which silently re-attributes its body to the *previous* declaration; every
    reference in that body then looks like a self-reference and is discarded --
    the second route to a false ``safe-to-delete``.
    """

    SOURCE = (
        "namespace IsingModel\n"
        "theorem synthetic_attr_base_xyzzy : True := trivial\n"
        "@[simp] theorem synthetic_attr_user_xyzzy : True :=\n"
        "  synthetic_attr_base_xyzzy\n"
        "end IsingModel\n"
    )

    def test_declaration_is_extracted_with_its_attributes(self) -> None:
        """Both the name and the attribute survive the same-line form."""
        decls = dcs.extract_decls(
            dcs.REPO_ROOT / "IsingModel" / "SynthAttr.lean", strip_noncode(self.SOURCE)
        )
        self.assertEqual(
            [decl.name for decl in decls],
            ["synthetic_attr_base_xyzzy", "synthetic_attr_user_xyzzy"],
        )
        self.assertEqual(decls[1].attrs, ("simp",))
        self.assertEqual(decls[1].line, 3)

    def test_multiline_block_closing_before_the_declaration(self) -> None:
        """The closing ``]`` may share its line with the declaration keyword."""
        decls = dcs.extract_decls(
            dcs.REPO_ROOT / "IsingModel" / "SynthAttr.lean",
            strip_noncode("@[simp,\n  norm_cast] theorem foo_multiline : True := trivial\n"),
        )
        self.assertEqual([decl.name for decl in decls], ["foo_multiline"])
        self.assertEqual(decls[0].attrs, ("norm_cast", "simp"))

    def test_body_is_owned_by_the_same_line_declaration(self) -> None:
        """The reference belongs to the attributed lemma, not to its predecessor."""
        tree_obj = synthetic_tree({"IsingModel/SynthAttr.lean": self.SOURCE})
        source = tree_obj.file_of("IsingModel/SynthAttr.lean")
        self.assertEqual(source.owner_of(4).final, "synthetic_attr_user_xyzzy")

    def test_the_reference_is_counted_as_a_consumer(self) -> None:
        """End to end: the base lemma must not be reported as deletable."""
        tree_obj = synthetic_tree({"IsingModel/SynthAttr.lean": self.SOURCE})
        verdicts, _cascade, _labels = dcs.classify(
            tree_obj, ["IsingModel.synthetic_attr_base_xyzzy"], [], allow_homonym=False
        )
        self.assertEqual(verdicts[0].verdict, dcs.LOAD_BEARING)
        self.assertEqual(len(verdicts[0].consumers), 1)
        self.assertTrue(
            all(occ.owner.attrs == ("simp",) for occ in verdicts[0].consumers)
        )


class TexCoverageTest(unittest.TestCase):
    """Coverage must be fail-closed: an unreadable citation is a warning, not a gap."""

    def test_brace_alternation_inside_a_citation_is_read(self) -> None:
        """A ``\\texttt`` body carrying braces used to match nothing, silently."""
        text = r"\texttt{magnetization\_convergent\_\{J,h,beta\}\_latticeGraph}"
        normalized, warnings = dcs.normalize_tex(text)
        self.assertIn("magnetization_convergent_{J,h,beta}_latticeGraph", normalized)
        self.assertEqual(warnings, [])

    def test_unreadable_citation_raises_a_warning_instead_of_vanishing(self) -> None:
        """Deeper nesting is not parsed -- but it must be *counted*."""
        _normalized, warnings = dcs.normalize_tex(r"\texttt{deep {a {b}} tail}")
        self.assertEqual(len(warnings), 1)
        self.assertEqual(warnings[0].kind, dcs.UNPARSABLE_BRACES)
        self.assertIn("unparsable braces", warnings[0].message)

    def test_nested_citation_is_not_residue_of_its_wrapper(self) -> None:
        """The inner span is read recursively, so the outer one is not a gap.

        Ten of the guide's warnings were this self-inflicted false positive, and
        a coverage count is worthless if the tool inflates it itself.
        """
        _normalized, warnings = dcs.normalize_tex(
            r"\texttt{(removed; archived \texttt{archive/branch-name})}"
        )
        self.assertEqual([w.message for w in warnings], [])

    def test_nested_citation_still_yields_the_inner_token(self) -> None:
        """The outer span consumes the inner one, so extraction recurses."""
        spans = dcs.code_citation_spans(r"\texttt{prose \texttt{inner_name_here} tail}")
        self.assertIn("inner_name_here", [body for body, _offset in spans])

    def test_real_guide_yields_its_brace_family_citations(self) -> None:
        """End to end: the guide's brace families are tokens, not blind spots."""
        tex = next(doc for doc in docs() if doc.label.endswith("proof-guide.tex"))
        tokens = {token for token, _line in tex.tokens}
        self.assertIn("magnetization_convergent_{J,h,beta}_latticeGraph", tokens)
        self.assertGreater(len([t for t in tokens if "{" in t]), 50)


class EnsureMathTest(unittest.TestCase):
    """``\\ensuremath`` wraps the blackboard-bold macros that spell ``ℂ``."""

    def test_two_stage_unwrap(self) -> None:
        """Dropping the wrapper and spelling the character must compose."""
        normalized, warnings = dcs.normalize_tex(
            r"\texttt{fieldPolymerZ\ensuremath{\mathbb{C}}\_ofReal}"
        )
        self.assertIn("fieldPolymerZℂ_ofReal", normalized)
        self.assertEqual(warnings, [])

    def test_real_guide_has_no_name_shaped_blind_spot(self) -> None:
        """Every span the guide leaves unreadable is prose, not a name citation.

        The measured state of main: no unreadable span at all (the three type
        signatures written with ``\\to`` are read since the macro table carries
        the arrow), and therefore nothing charged to any declaration. A failure
        here is a maintenance signal, not a flake -- the macro table needs the
        entry, or those names go out as ``uncertain``.
        """
        tex = next(doc for doc in docs() if doc.label.endswith("proof-guide.tex"))
        self.assertLessEqual(len(tex.unreadable), 5, [w.message for w in tex.unreadable])
        charged = [
            (span.line, decl.final)
            for span in tex.unreadable
            for decl in tree().decls
            if not decl.anonymous and span.could_cite_decl(decl)
        ]
        self.assertEqual(charged, [])

    def test_real_guide_publishes_the_complex_family(self) -> None:
        """The 16 ``...ℂ...`` names of section 18 were invisible before the unwrap."""
        tex = next(doc for doc in docs() if doc.label.endswith("proof-guide.tex"))
        for name in (
            "fieldPolymerZℂ_ne_zero",
            "norm_fieldMayerExpansionTermℂ_le_tree_activity_pow",
        ):
            self.assertTrue(dcs.find_occurrences(tex.text, name), name)


class UnreadableCitationTest(unittest.TestCase):
    """Coverage must reach the *verdict*, not only the warning count.

    A warning that changes no verdict and no exit code is fail-open where the
    docstring claimed fail-closed: 16 real published names were invisible to the
    TeX channel while the run printed 45 warnings and exited 0 regardless.

    The channel is **charge-only**: :attr:`dcs.UnreadableSpan.refutes` is
    ``False`` for every span, so an unread citation is charged to every
    candidate and can never deny one. Seven rounds of refutation rules each
    closed one leak and opened the next, always of the same shape -- text the
    normaliser had not explained was read as literal name evidence and refuted
    the very name it spelled -- so the refutation surface was removed rather
    than patched again. :data:`MEASURED_LEAKS` is every one of those leaks as
    measured on the real code; each entry must charge the name it hid.
    """

    #: ``(span source, the name that span really cites)``: the seven rounds'
    #: worth of measured fail-open shapes, ordered as they were found.
    MEASURED_LEAKS = (
        (r"\texttt{fieldPolymerZ\ensuremath{\mathbb{X}}}", "fieldPolymerZ𝕏"),
        (r"\texttt{le\_div\_iff\textsubscript{k}}", "le_div_iffₖ"),
        (r"\texttt{caf\'{e}\_lemma}", "café_lemma"),
        (r"\texttt{pre\ensuremath{\mathfrak{{{X}}}}post}", "pre𝔛post"),
        ("\\texttt{Ambient.foo\n", "IsingModel.Ambient.foo"),
        ("\\texttt{prose {deep {nest}} name_xyzzy}\n", "IsingModel.name_xyzzy"),
        ("\\texttt{prose{x}foo\\_bar\n", "foo_bar"),
        ("\\texttt{see\\/foo\\_bar\n", "foo_bar"),
        (r"\texttt{myLemma\unknown deprecated}", "myLemma"),
        (r"\texttt{foo\unknown{arg text}bar}", "fooXbar"),
        (r"\texttt{foo\'{e x}bar}", "fooébar"),
        # Round seven, the one that ended refutation: a macro's argument was
        # swallowed with it only when *braced*, so the standard unbraced accent
        # left its argument (``e``) behind as a readable fragment, and the span
        # refuted ``café_lemma`` -- the very name the macro spells.
        (r"\texttt{caf\'e\_lemma}", "café_lemma"),
    )

    def test_every_measured_leak_charges_the_name_it_hid(self) -> None:
        """The whole table: an unread span is charged to the name it cites."""
        for source, name in self.MEASURED_LEAKS:
            with self.subTest(source=source):
                _normalized, warnings = dcs.normalize_tex(source)
                self.assertEqual(len(warnings), 1, [w.message for w in warnings])
                self.assertTrue(warnings[0].could_cite(name), warnings[0].message)

    def test_unbracketed_accent_is_charged(self) -> None:
        """The round-seven leak, isolated: ``\\'e`` must not refute ``café_lemma``.

        ``\\'{e}`` was rescued by swallowing the macro's brace group, but the
        LaTeX-standard unbraced spelling carries no braces to swallow: the
        argument ``e`` survived as a readable fragment, the span refuted the
        name it spelled, no literal search could find that name either, and the
        declaration came out ``safe-to-delete``. It is charged now because no
        span refutes anything.
        """
        _normalized, warnings = dcs.normalize_tex(r"\texttt{caf\'e\_lemma}")
        self.assertEqual(len(warnings), 1)
        self.assertFalse(warnings[0].refutes)
        self.assertTrue(warnings[0].could_cite("café_lemma"), warnings[0].message)

    def test_no_span_shape_may_refute(self) -> None:
        """Charge-only is a property of the class, not of a span's shape.

        Every shape that used to decide refutation one way or the other -- a
        clean parse, an unparsable body, a brace no macro swallowed -- now
        charges, and charges names that have nothing to do with the citation.
        Over-charging can only produce ``uncertain``, never a false
        ``safe-to-delete``.
        """
        shapes = (
            (dcs.MACRO_RESIDUE, r"foo\unknownmacro bar"),
            (dcs.MACRO_RESIDUE, r"pre{X}post\unknown"),
            (dcs.MACRO_RESIDUE, r"pre\unknown{X}post"),
            (dcs.MACRO_RESIDUE, r"prefix\unknown{Z} (see)"),
            (dcs.UNPARSABLE_BRACES, r"\texttt{deep {a {b}} tail}"),
            (dcs.UNPARSABLE_BRACES, r"\texttt{\unknownmacro"),
            (dcs.UNPARSABLE_BRACES, r"\texttt{ \foo bar"),
        )
        for kind, text in shapes:
            with self.subTest(text=text):
                span = dcs.UnreadableSpan("tex", 1, kind, text)
                self.assertFalse(span.refutes)
                for name in ("fooXbar", "IsingModel.αX", "zzz_unrelated"):
                    self.assertTrue(span.could_cite(name), name)

    def test_qualified_citation_is_charged_under_either_spelling(self) -> None:
        """Both the bare and the qualified spelling keep the declaration charged."""
        span = dcs.UnreadableSpan("tex", 1, dcs.MACRO_RESIDUE, r"IsingModel.foo\unknownX")
        decl = synthetic_tree(
            {
                "IsingModel/SynthQualified.lean": (
                    "namespace IsingModel\n"
                    "theorem foo_x_bar : True := trivial\n"
                    "end IsingModel\n"
                )
            }
        ).decls[0]
        self.assertEqual(decl.full, "IsingModel.foo_x_bar")
        self.assertTrue(span.could_cite(decl.final))
        self.assertTrue(span.could_cite_decl(decl))


class TexChannelLimitTest(unittest.TestCase):
    """The shapes charge-only does *not* reach, pinned as they behave today.

    Charging fixes every leak that produced an :class:`dcs.UnreadableSpan`, but
    a citation that leaves **nothing to charge and no literal hit** never reaches
    the charging step at all: it leaves the TeX channel silently, and the name it
    cites can still come out ``safe-to-delete``. There are three, not two, and
    they escape differently: a ``%`` comment inside a citation (``L7a``) and a
    bare line break inside one (``L7c``) parse into a clean span, so there is no
    residue to charge, while an unrecognised wrapper (``L7b``) yields no span at
    all. The first two are properties
    of the *parser* only, because :func:`dcs.run_tex_canary` forbids them in the
    guide (see :class:`CanaryTest`); the tests below pin the parser behaviour so
    that a future fix is noticed as a *test failure* instead of shipping
    unremarked.
    """

    def test_a_comment_inside_a_citation_is_a_silent_gap(self) -> None:
        """``%`` splices two lines in TeX; the normaliser leaves a newline.

        ``\\texttt{foo% c\\n\\beta bar}`` typesets ``fooβbar``, but comment
        stripping keeps the line break, so the span parses cleanly (no warning)
        and normalises to ``foo\\nβbar``, which no literal search for
        ``fooβbar`` finds. Nothing is charged: this is the counterexample to
        "an unreadable citation is always charged".
        """
        normalized, warnings = dcs.normalize_tex("\\texttt{foo% c\n\\beta bar}")
        self.assertEqual(warnings, [])
        self.assertIn("foo\nβbar", normalized)
        self.assertEqual(dcs.find_occurrences(normalized, "fooβbar"), [])

    def test_a_bare_line_break_inside_a_citation_is_a_silent_gap(self) -> None:
        """The same gap without a comment: the newline alone hides the name.

        ``\\texttt{foo\\_`` + newline + ``bar}`` is one clean span, so nothing is
        charged, and the normalised text spells ``foo_``+newline+``bar``, which
        no search for ``foo_bar`` finds. Unlike ``L7a`` it also typesets wrongly,
        TeX turning the break into a space inside the name.
        """
        normalized, warnings = dcs.normalize_tex("\\texttt{foo\\_\nbar}")
        self.assertEqual(warnings, [])
        self.assertIn("foo_\nbar", normalized)
        self.assertEqual(dcs.find_occurrences(normalized, "foo_bar"), [])

    def test_an_unrecognised_code_wrapper_hides_only_macro_spelt_names(self) -> None:
        """Charging applies inside a *recognised* citation; the literal search does not.

        ``{\\tt ...}`` is not in :data:`dcs._TEX_CODE_CMDS`, so it is no span and
        raises no warning. That alone does not hide the name: normalisation runs
        over the whole document, so a plain ASCII name in such a wrapper is still
        found verbatim. What escapes is the intersection -- an unrecognised
        wrapper *and* a macro-spelt character the normaliser leaves as residue.
        """
        readable, warnings = dcs.normalize_tex(r"{\tt plain\_lemma}")
        self.assertEqual(warnings, [])
        self.assertTrue(dcs.find_occurrences(readable, "plain_lemma"))
        hidden, warnings = dcs.normalize_tex(r"{\tt caf\'{e}\_lemma}")
        self.assertEqual(warnings, [])
        self.assertEqual(dcs.find_occurrences(hidden, "café_lemma"), [])

    def test_every_gap_is_documented_as_a_limitation(self) -> None:
        """A silent gap must be written down where the report prints its limits."""
        self.assertIn("%", dcs.LIMITATIONS)
        self.assertIn(r"{\tt", dcs.LIMITATIONS)
        self.assertIn("L7c", dcs.LIMITATIONS)
        self.assertIn("run_tex_canary", dcs.LIMITATIONS)

    def test_unreadable_citation_blocks_safe_to_delete(self) -> None:
        """End to end: an unread span downgrades the name it might be citing."""
        tree_ = synthetic_tree(
            {
                "IsingModel/SynthUnreadable.lean": (
                    "namespace IsingModel\n"
                    "theorem synthetic_unreadableβ_xyzzy : True := trivial\n"
                    "end IsingModel\n"
                )
            }
        )
        name = "IsingModel.synthetic_unreadableβ_xyzzy"
        blind = synthetic_doc("nothing here")
        self.assertEqual(dcs.classify(tree_, [name], [blind], False)[0][0].verdict, dcs.SAFE)
        blind.unreadable.append(
            dcs.UnreadableSpan("tex", 7, dcs.MACRO_RESIDUE, r"synthetic_unreadable\beta\_xyzzy")
        )
        verdict = dcs.classify(tree_, [name], [blind], False)[0][0]
        self.assertEqual(verdict.verdict, dcs.UNCERTAIN)
        self.assertTrue(any("cannot read" in reason for reason in verdict.reasons))


class ProseMentionTest(unittest.TestCase):
    """Module docstrings that list a name: reported, never classifying."""

    SOURCES = {
        "IsingModel/SynthProseA.lean": (
            "namespace IsingModel\n"
            "theorem synthetic_prose_target_xyzzy : True := trivial\n"
            "end IsingModel\n"
        ),
        "IsingModel/SynthProseB.lean": (
            "/-! ## Siblings\n"
            "This module continues `synthetic_prose_target_xyzzy`.\n"
            "-/\n"
            "namespace IsingModel\n"
            "theorem synthetic_prose_other_xyzzy : True := trivial\n"
            "end IsingModel\n"
        ),
    }

    def verdict(self) -> dcs.Verdict:
        """Classify the target against the two-file synthetic tree."""
        tree_ = synthetic_tree(self.SOURCES)
        return dcs.classify(
            tree_, ["IsingModel.synthetic_prose_target_xyzzy"], [synthetic_doc("")], False
        )[0][0]

    def test_docstring_mention_is_reported_but_does_not_rescue(self) -> None:
        """Prose is not a reference: the verdict stays safe, with a warning."""
        verdict = self.verdict()
        self.assertEqual(verdict.verdict, dcs.SAFE)
        self.assertTrue(any("module docstring" in item for item in verdict.info))
        self.assertTrue(any("leaves that text stale" in item for item in verdict.info))

    def test_one_character_prose_line_is_recovered(self) -> None:
        """A blanked run of length one is prose too, not code spacing.

        Newlines survive the mask, so a line carrying a single character inside a
        block comment blanks to exactly one space; requiring two silently dropped
        such a line, and with it any one-character name written on it.
        """
        raw = "/-! ## Doc\nx\n-/\ntheorem t : True := trivial\n"
        cleaned = strip_noncode(raw)
        prose, regions = dcs.extract_prose(raw, cleaned, dcs.line_starts(raw))
        self.assertIn("x", prose.splitlines())
        self.assertIn(2, [line for _offset, line, _kind in regions])

    def test_prose_channel_sees_every_non_code_occurrence(self) -> None:
        """On the real tree, no textual occurrence falls between the channels."""
        parsed = tree()
        name = "freeEnergyAlongExhaustion_nonneg_of_ferromagnetic"
        prose_lines = {site for site in dcs.scan_prose(parsed, name)}
        code_lines = {f"{occ.file}:{occ.line}" for occ in dcs.scan_name(parsed, name)}
        for source in parsed.files:
            raw = source.path.read_text(encoding="utf-8")
            if name not in raw:
                continue
            for offset, _ctx, _prefix in dcs.find_occurrences(raw, name):
                line = dcs.offset_to_line(source.starts, offset)
                where = f"{source.relpath}:{line}"
                self.assertTrue(
                    where in code_lines or any(site.startswith(where + " ") for site in prose_lines),
                    where,
                )


_FAMILY: list[dcs.Verdict] | None = None


def family_verdicts() -> list[dcs.Verdict]:
    """Classify the whole ``_ferromagnetic`` family, at most once per process."""
    global _FAMILY
    if _FAMILY is None:
        names = sorted(
            decl.full
            for decl in tree().decls
            if not decl.anonymous and decl.name.endswith("_ferromagnetic")
        )
        _FAMILY = dcs.classify(tree(), names, docs(), allow_homonym=False)[0]
    return _FAMILY


class FamilyCalibrationTest(unittest.TestCase):
    """The calibration integers recorded in the fixtures header, asserted.

    They were prose in a comment, so nothing noticed when the delete-closure
    defect moved 15 candidates into ``safe-to-delete``.
    """

    def test_ferromagnetic_family_counts(self) -> None:
        """223 candidates -> 19 safe / 88 uncertain / 81 load-bearing / 35 published.

        Recalibrated by the resolved-glob elision-head repair
        (:class:`ResolvedGlobElisionHeadTest`). On the same documentation line,
        a supported glob head resolving to at most ten declarations can now
        establish the immediate-sibling prefix of a suffix citation. Exactly
        24 formerly-safe family members leave ``safe-to-delete``: 15 receive
        shorthand evidence directly and nine become load-bearing because their
        newly retained latticeGraph consumers receive it. Six previously
        uncertain members become load-bearing through the same closure. Thus
        the pre-closure distribution 19/103/66/35 becomes the final
        19/88/81/35; the 223 total, 35 published results, and
        :meth:`test_zero_consumer_count` (112) are unchanged. Whole-library
        evidence is additive (+205 shorthand, zero removals), the safe set only
        shrinks (49 safe-to-delete -> uncertain, 11 safe-to-delete ->
        load-bearing, 12 uncertain -> load-bearing), and family labels move
        387 -> 381 as six formerly-unattributed suffixes acquire concrete
        targets.

        Recalibrated by the narrow-glob repair
        (:class:`NarrowGlobCitationTest`): a glob citation naming at most
        :data:`dead_candidate_scan.MAX_CHARGED_GLOB_MATCHES` declarations is
        charged to all of them instead of being attributed to nobody. Exactly
        four candidates move and not one moves toward ``safe-to-delete``:
        ``correlationΛ_latticeGraph_high_temp_h_zero_at_singleton_ferromagnetic``
        and ``log_partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_
        deviation_pos_ferromagnetic`` go ``safe-to-delete -> uncertain`` (charged
        by ``docs/index.md:2193`` ``correlationΛ_latticeGraph_..._ferromagnetic``,
        5 matches, and by ``docs/index.md:2117`` / ``tex/proof-guide.tex:23284``
        ``log_*_deviation_pos_ferromagnetic``, 5 matches);
        ``correlationΛ_high_temp_h_zero_at_singleton_ferromagnetic``
        ``safe-to-delete -> load-bearing`` and
        ``log_partitionFunctionΛ_high_temp_expansion_h_zero_deviation_pos_
        ferromagnetic`` ``uncertain -> load-bearing``, both because the
        delete-closure no longer excuses their only consumer. ``SAFE`` 46 -> 43,
        ``UNCERTAIN`` 78 -> 79, ``LOAD_BEARING`` 64 -> 66; ``PUBLISHED`` (35),
        the 223 total and :meth:`test_zero_consumer_count` (112) are unchanged.
        Measured across the whole library the same way: 1091 -> 976
        ``safe-to-delete``, 691 -> 761 ``uncertain``, 2081 -> 2126
        ``load-bearing``, ``published-result`` unchanged at 7009, and the
        ``safe-to-delete`` key set only shrinks (139 movers -- 94
        ``safe-to-delete -> uncertain``, 21 ``safe-to-delete -> load-bearing``,
        24 ``uncertain -> load-bearing`` -- none toward ``safe-to-delete``).
        The four integers asserted below are threshold-insensitive across
        ``MAX_CHARGED_GLOB_MATCHES`` 8, 9 and 10; only the whole-library
        ``safe-to-delete`` count moves (980 at 8, 976 at 9 and 10), which is why
        raising the knob to its fixture ceiling of 10 needed no recalibration
        here.

        Previously recalibrated by PR #4754 (safe-to-delete batch 4), which moved
        exactly one
        candidate and moved it *away* from ``safe-to-delete``:
        ``freeEnergyAlongExhaustion_latticeGraph_nonneg_of_ferromagnetic``
        ``safe-to-delete -> uncertain``. Batch 4 deleted the zero-consumer
        ``freeEnergyAlongExhaustion_latticeGraph_nonneg``, which was the other
        member of the ``nonneg*`` component of the ``freeEnergyAlongExhaustion_
        latticeGraph_{eq_inv_*,eq_log_div_card,nonneg*,ge_log_two*}`` family label
        in ``docs/index.md``; with the sibling gone the component's shorthand
        citation now charges to the ferromagnetic wrapper alone. ``SAFE`` 47 -> 46
        and ``UNCERTAIN`` 77 -> 78; ``LOAD_BEARING`` (64), ``PUBLISHED`` (35), the
        223 total and :meth:`test_zero_consumer_count` (112) are unchanged. This is
        the healthy direction -- a deletion may only add protection to survivors.

        Previously recalibrated when the elided-prefix rule landed
        (:class:`ElidedFragmentTest`): a suffix citation whose elided prefix is
        spelled out on the same documentation line is charged to the siblings
        that share it. Exactly 45 candidates move, all of them out of
        ``safe-to-delete``: 33 to ``uncertain`` (charged directly) and 12 to
        ``load-bearing`` (their only consumer is now retained, so the
        delete-closure no longer excuses it), with ``published-result``
        unchanged at 35. That is the healthy signature -- the fix can add
        citations, never remove one. Measured across the whole library the same
        way: 235 of 11000 verdicts move, none of them toward ``safe-to-delete``.
        (Was 223 -> 92 safe / 44 uncertain / 52 load-bearing / 35 published, after
        PR #4690 dropped three safe-to-delete RatioLogFe ``_ferromagnetic``
        alongExhaustion bundle wrappers; 226 -> 95 safe before PR #4688.)
        """
        verdicts = family_verdicts()
        counts: dict[str, int] = {}
        for verdict in verdicts:
            counts[verdict.verdict] = counts.get(verdict.verdict, 0) + 1
        self.assertEqual(len(verdicts), 223)
        self.assertEqual(counts.get(dcs.SAFE), 19)
        self.assertEqual(counts.get(dcs.UNCERTAIN), 88)
        self.assertEqual(counts.get(dcs.LOAD_BEARING), 81)
        self.assertEqual(counts.get(dcs.PUBLISHED), 35)

    def test_zero_consumer_count(self) -> None:
        """112 of the 223 have no Lean consumer at all.

        Was 114 of 226 before PR #4690 dropped the three safe-to-delete
        RatioLogFe ``_ferromagnetic`` alongExhaustion bundle wrappers; two of the
        three were zero-consumer, so the count drops by two.
        """
        self.assertEqual(sum(1 for v in family_verdicts() if not v.consumers), 112)


# Anti-vacuity floor for the Unicode canary population.  The Unicode guarantee
# itself is the *universal* in ``run_canary`` -- every Lambda/beta/sigma-bearing
# declaration finds itself in its own defining file -- which holds at any
# population size, plus the synthetic fixtures below.  This number exists only so
# that universal cannot go trivially true because the population collapsed, and
# it is therefore deliberately far below the measured census.
#
# Derivation (main ``ddf332d9``, measured, not calibrated): the census is 1005
# (Lambda 1002, beta 1, sigma 2).  Of those, 457 live inside the #4746 Item A
# path allow-list and 2 more inside ``AmbientLattice/SpecialCases`` (#4563); no
# deletion batch is authorised to touch anything else, so no batch of that
# campaign can push the census below 1005 - 457 - 2 = 546, even in the
# counterfactual where every allow-listed module is deleted.  A cascade cannot
# defeat the bound: it can only promote modules that are already allow-listed.
# 500 is that bound rounded down; the measured remaining lane would only reach
# 926.  Predecessor: the same one-time re-derivation for the audit-gate file
# counts, PR #4766 (#4746 Item F1).  Note what the bound is and is not: it is an
# *authorisation* bound on the deletion campaign, not an invariant this file can
# enforce -- a deletion outside the allow-list is caught by review, not by this
# number.
#
# The floor was 1000 until #4746 batch 7, i.e. the census minus four.  A count
# floor set just under the current measurement describes the deletions instead
# of constraining them, and had to be lowered once per batch.  Standing rule, as
# for the audit-gate floors: **a batch that would trip this floor is a governance
# signal -- re-measure the lane and get a decision, do not lower the entry.**
CANARY_DECL_FLOOR = 500


class CanaryTest(unittest.TestCase):
    """The cheapest possible regression detector, run on every invocation."""

    def synthetic_tree(self, *sources: tuple[str, str]) -> dcs.Tree:
        """Build a tree from ``(relpath, text)`` pairs, through the real pipeline.

        Uses the scanner's own :func:`dead_candidate_scan.build_tree`, so the
        fixture exercises stripping, declaration extraction and indexing rather
        than a hand-built declaration table.  The paths need not exist on disk,
        but they must sit under ``REPO_ROOT`` for ``rel()`` to name them.
        """
        return dcs.build_tree([(dcs.REPO_ROOT / relpath, text) for relpath, text in sources])

    def canary_fixture(self) -> dcs.Tree:
        """Return a tree holding exactly one declaration per canary character."""
        names = [f"synthetic{char}_lemma" for char in dcs.CANARY_CHARS]
        text = "".join(f"theorem {name} : True := trivial\n" for name in names)
        return self.synthetic_tree(("IsingModel/Canary.lean", text))

    def test_unicode_declarations_find_themselves(self) -> None:
        """Every Lambda/beta/sigma-bearing declaration matches its own name.

        ``run_canary`` itself raises on the first declaration that cannot find
        itself, so this test adds only the anti-vacuity floor; see
        :data:`CANARY_DECL_FLOOR` for why it is loose, and
        :meth:`test_the_canary_passes_on_one_name_per_character` for where the
        per-character guarantee actually comes from.
        """
        count, per_char = dcs.run_canary(tree())
        self.assertGreaterEqual(count, CANARY_DECL_FLOOR)
        for char, hits in per_char.items():
            self.assertGreater(hits, 0, char)

    def test_the_canary_character_set_is_pinned(self) -> None:
        """Shrinking ``CANARY_CHARS`` must be an explicit, reviewed edit.

        Without this the fixture below is self-fulfilling: it derives both its
        names and its expectations from ``CANARY_CHARS``, so dropping ``β`` from
        the constant -- the cheapest way to silence the degeneracy abort when the
        library's single ``β``-bearing declaration is renamed -- would leave every
        canary assertion green while the character stopped being checked at all.
        Same reason the suite refuses to derive a calibration from the quantity
        it calibrates.
        """
        self.assertEqual(dcs.CANARY_CHARS, ("Λ", "β", "σ"))

    def test_the_canary_passes_on_one_name_per_character(self) -> None:
        """Each canary character is exercised by a fixture, not by the library.

        On the real tree ``beta`` and ``sigma`` are carried by three
        declarations in total (one of them unique), all of them incidental: the
        claim "the scanner handles beta" was guaranteed by the accident that one
        lemma in ``Inequalities/HighTemp`` happens to spell beta in its name.  A
        fixture makes the claim independent of which names the library holds, and
        of any deletion campaign.  All three characters must share one tree,
        because ``run_canary`` aborts on a character with no bearer.
        """
        count, per_char = dcs.run_canary(self.canary_fixture())
        self.assertEqual(count, len(dcs.CANARY_CHARS))
        self.assertEqual(per_char, dict.fromkeys(dcs.CANARY_CHARS, 1))

    def test_the_canary_rejects_a_cleaner_that_drops_a_greek_letter(self) -> None:
        """The failing direction the canary was written for, finally tested.

        Nothing used to prove ``run_canary`` can fail at all.  Dropping the Greek
        letter from the cleaned text -- the exact signature of the
        Unicode-splitting tokenizer that produced three bad deletion sweeps --
        must abort the run, not merely lower a count.  The tampering happens
        after ``build_tree`` on purpose: the declaration table is built *from*
        the cleaned text, so an extracted name always finds itself until the text
        underneath it changes.
        """
        broken = self.canary_fixture()
        for source in broken.files:
            source.cleaned = source.cleaned.replace("Λ", "")
        with self.assertRaises(dcs.Inconsistency) as caught:
            dcs.run_canary(broken)
        self.assertIn("cannot find itself", str(caught.exception))

    def test_the_canary_rejects_a_tree_with_no_unicode_declarations(self) -> None:
        """A population of zero must abort, not pass a vacuous universal.

        This is the degeneracy branch the loose :data:`CANARY_DECL_FLOOR` leans
        on: the floor guards against a *collapsed* population, this guards
        against an *empty* one, and neither is left to the count alone.
        """
        plain = self.synthetic_tree(
            ("IsingModel/Plain.lean", "theorem plain_lemma : True := trivial\n")
        )
        with self.assertRaises(dcs.Inconsistency) as caught:
            dcs.run_canary(plain)
        self.assertIn("degenerated", str(caught.exception))

    def test_no_guide_citation_is_broken_across_a_line(self) -> None:
        """The real guide keeps every code citation on one line.

        A citation split across lines is invisible to *both* halves of the TeX
        channel and warns about nothing (``L7a``/``L7c``), so the guard has to
        be a property of the guide rather than of the parser.
        """
        citations = dcs.run_tex_canary()
        self.assertGreater(citations, 1000)

    def test_the_canary_rejects_a_broken_citation(self) -> None:
        """Both flavours of the break -- with and without ``%`` -- are caught."""
        for source in ("\\texttt{foo\\_%\nbar}", "\\texttt{foo\\_\nbar}"):
            citations, broken = dcs.tex_citation_line_breaks(source)
            self.assertEqual(citations, 1, source)
            self.assertEqual([line for line, _body in broken], [1], source)
        self.assertEqual(dcs.tex_citation_line_breaks("\\texttt{foo\\_bar}")[1], [])

    def test_the_names_the_break_used_to_hide_are_visible(self) -> None:
        """The four published results the broken citations hid are found again.

        Each was cited only in a citation the guide split across a line, so the
        TeX channel saw nothing while reporting zero coverage warnings; only an
        unrelated ``docs/`` citation kept them off ``safe-to-delete``.
        """
        guide = next(source for source in docs() if source.label == "tex/proof-guide.tex")
        for name in (
            "gibbsExpectationBC_originObs_cubicExhaustion_boundary_influence_ball",
            "gibbsExpectationBC_originObs_cubicExhaustion_boundary_influence_uniform",
            "plusStateExpectation_eq_minusStateExpectation_originObs",
            "polymerFreeEnergy_analyticOnNhd_Ici_zero",
        ):
            self.assertTrue(dcs.find_occurrences(guide.text, name), name)
            self.assertIn(name, [token for token, _line in guide.tokens], name)


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

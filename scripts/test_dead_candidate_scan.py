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
or coverage is fail-open exactly where it claims to be fail-closed) and
:class:`CharClassTest` (the identifier class must never be a superset of Lean's).
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
        """The same invariant, over the 263-candidate ``_ferromagnetic`` family."""
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
    """

    def test_fragments_refute_a_name_or_keep_it(self) -> None:
        """Readable fragments must occur, in order, inside any name cited.

        Per *word*: an unknown macro may gobble the space after it, so the whole
        span can spell one name, but the trailing word may equally be prose while
        the macro spells the rest of the name -- ``foo_baz`` is therefore charged
        too. Only a name no single word can spell is refuted.
        """
        span = dcs.UnreadableSpan("tex", 1, dcs.MACRO_RESIDUE, r"foo\unknownmacro bar")
        self.assertTrue(span.could_cite("fooXbar"))
        self.assertTrue(span.could_cite("foo_lambda_bar"))
        self.assertTrue(span.could_cite("foo_baz"))
        self.assertFalse(span.could_cite("zzz_unrelated"))

    def test_a_prose_word_does_not_disown_the_cited_name(self) -> None:
        """A second word in the span must not refute the name the first one spells.

        Requiring *every* word's fragments inside one name refuted the real
        cited name whenever the citation carried a prose word, and a span
        charged to nobody is a citation that stops forcing `uncertain` -- the
        same fail-open route as reading a macro argument literally, reached
        without any argument at all.
        """
        span = dcs.UnreadableSpan("tex", 1, dcs.MACRO_RESIDUE, r"myLemma\unknown deprecated")
        self.assertTrue(span.could_cite("myLemma"))
        self.assertFalse(span.could_cite("zzz_unrelated"))
        _normalized, warnings = dcs.normalize_tex(r"\texttt{myLemma\unknown deprecated}")
        self.assertEqual(len(warnings), 1)
        decl = synthetic_tree(
            {
                "IsingModel/SynthProseWord.lean": (
                    "namespace IsingModel\ntheorem myLemma : True := trivial\nend IsingModel\n"
                )
            }
        ).decls[0]
        self.assertTrue(warnings[0].could_cite_decl(decl), warnings[0].message)

    def test_an_entirely_unreadable_span_keeps_everything(self) -> None:
        """No fragment left means no candidate can be excluded."""
        span = dcs.UnreadableSpan("tex", 1, dcs.MACRO_RESIDUE, r"\unknownmacro")
        self.assertTrue(span.could_cite("anything_at_all"))

    def test_unparsable_span_requires_only_one_of_its_identifier_runs(self) -> None:
        """Its end is not locatable, so no run can be required to open the name.

        ``shallow_lemma`` is charged because the one-character run ``a`` occurs
        in it: inside an unparsable region a short run refutes almost nothing,
        which is the conservative direction.
        """
        span = dcs.UnreadableSpan("tex", 1, dcs.UNPARSABLE_BRACES, r"\texttt{deep {a {b}} tail}")
        self.assertTrue(span.could_cite("deep_lemma"))
        self.assertTrue(span.could_cite("prefix_tail_of_it"))  # a run that does not open it
        self.assertTrue(span.could_cite("shallow_lemma"))
        self.assertFalse(span.could_cite("zzz_lemm"))

    def test_unparsable_span_is_charged_when_its_run_sits_inside_the_name(self) -> None:
        """Requiring the *opening* run as a prefix let two real shapes escape.

        A partially qualified citation and one opened by prose both show a run
        the name carries, and both were charged to nobody while `startswith`
        decided the question.
        """
        cases = (
            ("\\texttt{Ambient.foo\n", "IsingModel.Ambient.foo"),
            ("\\texttt{prose {deep {nest}} name_xyzzy}\n", "IsingModel.name_xyzzy"),
        )
        for source, name in cases:
            with self.subTest(source=source):
                _normalized, warnings = dcs.normalize_tex(source)
                self.assertEqual(len(warnings), 1)
                self.assertEqual(warnings[0].kind, dcs.UNPARSABLE_BRACES)
                self.assertTrue(warnings[0].could_cite(name), warnings[0].message)
                self.assertFalse(warnings[0].could_cite("zzz_qqq"))

    def test_macro_arguments_are_not_readable_fragments(self) -> None:
        """An unknown macro's argument is its input, never literal name text.

        Each of these spans is the shape the guide already uses for a *real*
        published name (``\\ensuremath{\\mathbb{C}}`` spells ``ℂ`` inside 16 of
        them). Reading the argument body as a literal fragment demanded that the
        cited name contain ``X`` / ``k`` / ``e``, which the name it actually
        spells never does, so the span refuted every candidate, was charged to
        nobody, and the name it hid could fall out as ``safe-to-delete``.
        """
        cases = (
            (r"\texttt{fieldPolymerZ\ensuremath{\mathbb{X}}}", "fieldPolymerZ𝕏"),
            (r"\texttt{le\_div\_iff\textsubscript{k}}", "le_div_iffₖ"),
            (r"\texttt{caf\'{e}\_lemma}", "café_lemma"),
        )
        for source, name in cases:
            with self.subTest(source=source):
                _normalized, warnings = dcs.normalize_tex(source)
                self.assertEqual(len(warnings), 1)
                self.assertTrue(warnings[0].could_cite(name), warnings[0].message)
                # Still discriminating: an unrelated name is refuted as before.
                self.assertFalse(warnings[0].could_cite("unrelated_lemma"))

    def test_prose_fragments_do_not_refute_every_candidate(self) -> None:
        """A fragment no identifier can contain is prose, not evidence.

        The identifier fragment of the same span keeps refuting, so ignoring the
        prose one loosens the test exactly where it was refuting by mistake.
        """
        span = dcs.UnreadableSpan("tex", 1, dcs.MACRO_RESIDUE, r"prefix\unknown{Z} (see)")
        self.assertTrue(span.could_cite("prefix_lemma"))
        self.assertFalse(span.could_cite("other_lemma"))

    def test_qualified_citation_is_matched_against_the_full_name(self) -> None:
        """A namespace-qualified fragment is refuted by the bare final component."""
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
        self.assertFalse(span.could_cite(decl.final))
        self.assertTrue(span.could_cite_decl(decl))

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
        """263 candidates -> 132 safe / 44 uncertain / 52 load-bearing / 35 published."""
        verdicts = family_verdicts()
        counts: dict[str, int] = {}
        for verdict in verdicts:
            counts[verdict.verdict] = counts.get(verdict.verdict, 0) + 1
        self.assertEqual(len(verdicts), 263)
        self.assertEqual(counts.get(dcs.SAFE), 132)
        self.assertEqual(counts.get(dcs.UNCERTAIN), 44)
        self.assertEqual(counts.get(dcs.LOAD_BEARING), 52)
        self.assertEqual(counts.get(dcs.PUBLISHED), 35)

    def test_zero_consumer_count(self) -> None:
        """143 of the 263 have no Lean consumer at all."""
        self.assertEqual(sum(1 for v in family_verdicts() if not v.consumers), 143)


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

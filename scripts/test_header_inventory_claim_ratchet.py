#!/usr/bin/env python3
"""Tests for the inventory-claim ratchet (``scripts/header_inventory_claim_ratchet.py``).

A ratchet is worth exactly as much as the proof that it can fail, and a
conservation law is worth exactly as much as the proof that it can catch a lost
record.  The suite is therefore built around **mutation canaries**
(:class:`MutationCanaryTest`): each one weakens the checker in the precise way a
maintainer under time pressure would, and requires the weakening to change the
verdict.  Every mutation is anti-vacuous -- :func:`load_mutant` raises when its
target text is absent, so a rename cannot quietly turn a canary into a no-op.

The structural fixtures are synthetic strings, so no test can be repaired by
editing ``IsingModel/``.  Three suites build a throwaway ``git`` repository
rather than reading this one -- :class:`ScratchRepoTest` for the tracked-set
discipline (``git ls-files``, never a filesystem walk) and :class:`DriftTest`
for the comparison against the base branch -- so they state properties of the
checker instead of properties of today's working tree.

:class:`RealTreeTest` is the one suite that reads the repository, and what it
asserts of the live tree is deliberately shape and not size.  A floor under the
live violation count reads like anti-vacuity but is a floor under the defect the
ratchet exists to remove: it would turn the suite red exactly when the campaign
succeeded, and the cheapest repair would be to loosen it inside the PR doing the
repairing.  Anti-vacuity lives on :data:`FIXTURES` instead, which keep proving
the detector is alive after the last real claim is gone.
"""

from __future__ import annotations

import contextlib
import io
import re
import shutil
import subprocess
import sys
import tempfile
import types
import unittest
from collections import Counter
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent
SCRIPT_FILE = SCRIPT_DIR / "header_inventory_claim_ratchet.py"
WORKFLOW_FILE = REPO_ROOT / ".github" / "workflows" / "lean_action_ci.yml"
sys.path.insert(0, str(SCRIPT_DIR))

import header_inventory_claim_ratchet as ratchet  # noqa: E402

#: Floor on the number of tracked targets, so a collapsed scan cannot make every
#: real-tree assertion below vacuously true.
TARGET_FLOOR = 1500

#: Ceiling on the pinned baseline.  A ceiling, not an equality: the campaign this
#: ratchet exists to serve drives the number down, and re-pinning after a repair
#: must not need a test edit -- but *raising* it has to, which is why every
#: correction below had to be made here in the open.
#:
#: * **713**, first measured on the commit that introduced the pin (main
#:   ``fd1cdd8a``).
#: * **740**, when ``NARROW_CHILD``'s anchor gained ``re.IGNORECASE``: 27
#:   lowercase occurrences that had always been in the tree became visible, so
#:   the 713 was an undercount of the tree, not a smaller population.
#: * **740** still, after the quantity grammar was closed (cardinals past
#:   ``fifty``, the ``~N``/``about N``/``N,NNN``/``N+`` idioms, the fail-closed
#:   digit-initial rule): byte-identical findings, because the corpus writes
#:   small numerals and the hole was a *future* bypass rather than a live
#:   undercount.
#: * **1391**, when the ``accounted`` bucket was retired.  ``RELOCATION`` now
#:   charges on its anchor (+648: 647 sentences that were recognized and free,
#:   plus one in a file that was outside the old scan), the scan took in
#:   ``IsingModel.lean``, ``README.md`` and the rest of ``docs/`` (+1 structural,
#:   +1 predicate), and the clause window went from 70 to 200 characters (+1
#:   predicate).  No prose was written and nothing regressed: this is the first
#:   measurement of a population that was always there.
#: * **1390**, when a clause window stopped crossing blank lines: three spans
#:   were borrowing a count from the paragraph above and all three were wrong.
#: * **1402**, when a ``NARROW_CHILD`` count stopped having to sit at position 0
#:   of its head clause.  12 headers that were reported as stating no size do
#:   state one, and a single adjective was enough to hide any of them --
#:   ``for the following 17 wrappers`` produced no key at all.  Raised here in
#:   the open, as this constant exists to force.
BASELINE_CEILING = 1402

#: A minimal declaration, so a fixture module is never accidentally an umbrella.
TRIVIAL = "theorem f : True := trivial\n"

#: The command lines CI must run, in this order.
SUITE_COMMAND = "python3 scripts/test_header_inventory_claim_ratchet.py"
GATE_COMMAND = "python3 scripts/header_inventory_claim_ratchet.py --check"
DRIFT_COMMAND = (
    "python3 scripts/header_inventory_claim_ratchet.py --check-baseline-drift "
    "--base-ref origin/main"
)

#: The workflow job the three commands above belong to.
CI_JOB = "header-inventory-claim-ratchet"


def source_text() -> str:
    """Return the checker's own source (the substrate every canary mutates)."""
    return SCRIPT_FILE.read_text(encoding="utf-8")


def load_mutant(*replacements: tuple[str, str]) -> types.ModuleType:
    """Return the checker re-imported with ``replacements`` applied to its source.

    Raises when a replacement's target is absent: a canary whose mutation no
    longer applies must fail loudly rather than pass by mutating nothing.  This
    is the anti-vacuity guarantee the whole class rests on.
    """
    text = source_text()
    for old, new in replacements:
        if old not in text:
            raise AssertionError(f"mutation target absent, canary would be vacuous: {old!r}")
        text = text.replace(old, new, 1)
    module = types.ModuleType("header_inventory_claim_ratchet_mutant")
    module.__file__ = str(SCRIPT_FILE)
    exec(compile(text, str(SCRIPT_FILE), "exec"), module.__dict__)  # noqa: S102
    return module


def lean_source(name: str, text: str, module=ratchet):
    """Return a synthetic Lean :class:`Source` for module ``name``.

    Keyed by its path, like every real source: ``target`` and ``path`` are the
    same string, so a fixture cannot demonstrate a property the production
    keying does not have.
    """
    path = name if name.endswith(".lean") else f"{name.replace('.', '/')}.lean"
    return module.Source(target=path, path=path, text=text, is_lean=True)


def doc_source(path: str, text: str, module=ratchet):
    """Return a synthetic document :class:`Source` at ``path``."""
    return module.Source(target=path, path=path, text=text, is_lean=False)


def charged(source, module=ratchet) -> list:
    """Return the charged claims of one source.

    Every row of ``claims`` is charged now; ``telemetry`` is the other ledger and
    nothing here may read it as a claim.
    """
    return list(module.scan_source(source).claims)


def telemetry(source, module=ratchet) -> list:
    """Return the non-authoritative records of one source."""
    return list(module.scan_source(source).telemetry)


def tokens(source, kind: str, module=ratchet) -> list[str]:
    """Return the charged tokens of class ``kind`` found in ``source``."""
    return [claim.token for claim in charged(source, module) if claim.kind == kind]


def header(body: str) -> str:
    """Wrap ``body`` in a module docstring on top of a trivial declaration."""
    return f"import IsingModel.Basic\n\n/-!\n# Fixture\n\n{body}\n-/\n\n{TRIVIAL}"


# --------------------------------------------------------------------------
# Recognized shapes
# --------------------------------------------------------------------------


class ShapeTest(unittest.TestCase):
    """One fixture per recognized claim shape, including the near-miss variants."""

    def test_narrow_child_with_the_article(self) -> None:
        """The dominant spelling: `Narrow child module for the 12 ... wrappers`."""
        source = lean_source("M", header("Narrow child module for the 12 foo wrappers."))
        self.assertEqual(tokens(source, "NARROW_CHILD"), ["12"])

    def test_narrow_child_without_the_article(self) -> None:
        """The article is optional, and one missing article cost Unit 4 40 % recall."""
        source = lean_source("M", header("Narrow child module for 12 foo wrappers."))
        self.assertEqual(tokens(source, "NARROW_CHILD"), ["12"])

    def test_narrow_child_with_a_word_number(self) -> None:
        """Word forms outnumber numerals almost three to one in this corpus."""
        source = lean_source("M", header("Narrow child module for four foo wrappers."))
        self.assertEqual(tokens(source, "NARROW_CHILD"), ["4"])

    def test_narrow_child_with_a_hyphenated_word_number(self) -> None:
        """`twenty-four` normalizes to the same token a numeral would produce."""
        source = lean_source("M", header("Narrow child module for twenty-four foo wrappers."))
        self.assertEqual(tokens(source, "NARROW_CHILD"), ["24"])

    def test_the_cardinal_vocabulary_does_not_stop_at_fifty(self) -> None:
        """The bypass this class was shipped with: `sixty` was silently free.

        `for twelve foo wrappers` was charged and `for sixty foo wrappers` was
        *accounted* -- no charge, no failure, no mention in the totals -- because
        the lexicon happened to stop where the corpus did.  English cardinals are
        a closed class, so the fix is to close it rather than to keep extending
        it one corpus at a time.
        """
        for word, expected in (
            ("sixty", "60"), ("seventy", "70"), ("eighty", "80"), ("ninety", "90"),
            ("hundred", "100"), ("ninety-nine", "99"), ("eighty-five", "85"),
        ):
            source = lean_source("M", header(f"Narrow child module for {word} foo wrappers."))
            self.assertEqual(tokens(source, "NARROW_CHILD"), [expected], word)

    def test_a_multi_word_cardinal_multiplies_rather_than_adds(self) -> None:
        """`two hundred` is 200; a sum over the words -- the old shape -- says 102."""
        source = lean_source("M", header("Narrow child module for two hundred foo wrappers."))
        self.assertEqual(tokens(source, "NARROW_CHILD"), ["200"])
        source = lean_source("M", header("Narrow child module for one thousand foo wrappers."))
        self.assertEqual(tokens(source, "NARROW_CHILD"), ["1000"])

    def test_two_adjacent_cardinals_are_not_one_number(self) -> None:
        """`the two three-part lemmas` is two, not five: the grammar is not a sum."""
        source = lean_source("M", header("Narrow child module for the two three-part lemmas."))
        self.assertEqual(tokens(source, "NARROW_CHILD"), ["2"])

    def test_hedged_and_grouped_numerals_are_charged(self) -> None:
        """`~12`, `about 12`, `1,024`, `12+` are counts and go stale like counts."""
        for phrase, expected in (
            ("~12", "~12"), ("about 12", "~12"), ("approximately 12", "~12"),
            ("at least 12", "~12"), ("1,024", "1024"), ("12+", "12+"),
            ("about twelve", "~12"),
        ):
            source = lean_source("M", header(f"Narrow child module for {phrase} foo wrappers."))
            self.assertEqual(tokens(source, "NARROW_CHILD"), [expected], phrase)

    def test_every_hedge_form_is_charged(self) -> None:
        """The hedges that were still free: an unlisted one is a silent bypass.

        Each of these reached the extractor, was told "not a quantity" and was
        *accounted* -- no charge, no mention in the totals -- because the
        head-quantity pattern falls back to a single token and an unlisted hedge
        is what that token turns out to be.
        """
        for phrase, expected in (
            ("a total of 12", "~12"), ("some 12", "~12"), ("circa 12", "~12"),
            ("no fewer than 12", "~12"), ("no more than 12", "~12"),
            ("over 12", "~12"), ("under 12", "~12"), ("exactly 12", "~12"),
            ("just 12", "~12"), ("only 12", "~12"), ("upwards of 12", "~12"),
            ("close to 12", "~12"), ("less than 12", "~12"),
        ):
            source = lean_source("M", header(f"Narrow child module for {phrase} foo wrappers."))
            self.assertEqual(tokens(source, "NARROW_CHILD"), [expected], phrase)

    def test_zero_and_dozens_are_counts(self) -> None:
        """`zero` and `a dozen` state a size exactly as `12` does."""
        for phrase, expected in (
            ("zero", "0"), ("a dozen", "12"), ("one dozen", "12"), ("two dozen", "24"),
            ("about a dozen", "~12"), ("a hundred", "100"),
        ):
            source = lean_source("M", header(f"Narrow child module for {phrase} foo wrappers."))
            self.assertEqual(tokens(source, "NARROW_CHILD"), [expected], phrase)

    def test_a_compound_cardinal_carries_place_value(self) -> None:
        """A truncated parse is worse than none: it charges a *different* number.

        The single-group grammar stopped after the first small tail, so `one
        thousand two hundred` was normalized to 1002 and `one hundred thousand`
        to 100 -- charged, fail-closed on the decision, and wrong on the key.
        """
        for phrase, expected in (
            ("one thousand two hundred", "1200"), ("one hundred thousand", "100000"),
            ("two hundred fifty", "250"), ("one hundred and five", "105"),
            ("twelve hundred", "1200"), ("three thousand", "3000"),
        ):
            source = lean_source("M", header(f"Narrow child module for {phrase} foo wrappers."))
            self.assertEqual(tokens(source, "NARROW_CHILD"), [expected], phrase)

    def test_a_decimal_head_is_unresolved_rather_than_truncated(self) -> None:
        """`1.5k` used to match the leading `1` and be charged as the number one."""
        source = lean_source("M", header("Narrow child module for 1.5k foo wrappers."))
        self.assertEqual(tokens(source, "NARROW_CHILD"), ["?1.5k"])

    def test_an_unnormalizable_numeric_head_is_charged_not_accounted(self) -> None:
        """Fail closed: a head word starting with a digit is a count either way.

        This is the residual the closed vocabulary cannot reach -- ``12-ish``,
        ``12k``, any future spelling -- and the rule for it is the same one the
        structural classes use: unparseable is charged, never skipped.
        """
        source = lean_source("M", header("Narrow child module for 12-ish foo wrappers."))
        self.assertEqual(tokens(source, "NARROW_CHILD"), ["?12-ish"])
        self.assertEqual(telemetry(source), [])

    #: Head phrases that carry numeric content the normalizer cannot resolve into
    #: one integer.  Every one of them was *accounted* -- recognized, free, and
    #: absent from the totals -- because the head capture took a single
    #: whitespace-delimited token and handed ``about`` to a resolver that
    #: correctly said "not a quantity".  The module docstring's own worked
    #: example of the fail-closed rule (``about 12ish``) was among them.
    UNRESOLVED_HEADS = (
        ("about 12ish", "?about 12ish"),
        ("about 1.5k", "?about 1.5k"),
        ("about 12-ish", "?about 12-ish"),
        ("between 10 and 12", "?between 10 and 12"),
        ("minus twelve", "?minus twelve"),
        ("half a dozen", "?half a dozen"),
        ("several dozen", "?several dozen"),
    )

    def test_a_multi_word_head_reaches_the_fail_closed_rule(self) -> None:
        """A quantity phrase is charged whole, not judged on its first word."""
        for phrase, expected in self.UNRESOLVED_HEADS:
            source = lean_source("M", header(f"Narrow child module for {phrase} foo wrappers."))
            self.assertEqual(tokens(source, "NARROW_CHILD"), [expected], phrase)
            self.assertEqual(telemetry(source), [], phrase)

    #: Determiners in front of a bare numeral.  ``RELOCATION``'s subject already
    #: accepted ``the|these|its|all`` while ``NARROW_CHILD``'s head accepted only
    #: ``the``, so ``All 12 wrappers now live in `X` `` was charged and ``Narrow
    #: child module for all 12 wrappers`` was not -- one lexical class, two
    #: verdicts, in one file.
    DETERMINED_HEADS = (
        "all 12", "these 12", "those 12", "our 12", "their 12", "its 12",
        "the same 12", "each of the 12", "this 12", "that 12",
    )

    def test_a_determiner_does_not_hide_a_bare_numeral(self) -> None:
        for phrase in self.DETERMINED_HEADS:
            source = lean_source("M", header(f"Narrow child module for {phrase} foo wrappers."))
            self.assertEqual(tokens(source, "NARROW_CHILD"), ["12"], phrase)

    def test_a_vague_quantifier_survives_an_article(self) -> None:
        """`a few` and `a couple of` state exactly what the bare word does."""
        for phrase, expected in (("a few", "few"), ("a couple of", "couple"),
                                 ("the remaining", "remaining"), ("several", "several")):
            source = lean_source("M", header(f"Narrow child module for {phrase} foo wrappers."))
            self.assertEqual(tokens(source, "NARROW_CHILD"), [expected], phrase)

    #: Head phrases that state no size, and that a "digit anywhere" rule would
    #: charge.  The section references are 52 live sites, so this is a measured
    #: cost and not a hypothetical one; the hyphenated cardinals are adjectives
    #: (`two-sided`, `three-part`, `four-point`) that the corpus is full of.
    NON_QUANTITY_HEADS = (
        "§17.5", "§18.3-§18.4", "concrete `latticeGraph` specializations",
        "ℤ^d", "along-exhaustion", "two-sided", "Step 241 interior", "a", "an",
    )

    def test_a_citation_or_an_adjective_is_not_a_quantity(self) -> None:
        for phrase in self.NON_QUANTITY_HEADS:
            source = lean_source("M", header(f"Narrow child module for {phrase} foo wrappers."))
            self.assertEqual(charged(source), [], phrase)
            self.assertEqual(len(telemetry(source)), 1, phrase)

    def test_narrow_child_claim_wrapped_across_lines(self) -> None:
        """Claims wrap; matching on unflattened text would see none of them."""
        source = lean_source("M", header("Narrow child module for\nthe 12 foo\nwrappers."))
        self.assertEqual(tokens(source, "NARROW_CHILD"), ["12"])

    def test_narrow_child_anchor_ignores_case(self) -> None:
        """A lowercase `n` must not buy silence: prose is not case-normalized.

        The anchor was case-sensitive when this class was introduced, which made
        the largest claim class -- 68 % of the pinned population -- bypassable by
        a one-character edit no reviewer would look at twice.
        """
        source = lean_source("M", header("narrow child module for the 12 foo wrappers."))
        self.assertEqual(tokens(source, "NARROW_CHILD"), ["12"])

    def test_relocation_anchor_ignores_case(self) -> None:
        """Sentence-initial `Now live in` is the same claim as `now live in`."""
        source = lean_source(
            "M", header("The 13 bridge wrappers\nNow live in `IsingModel.Other.TanhPowDist`.")
        )
        self.assertEqual(tokens(source, "RELOCATION"), ["13->IsingModel.Other.TanhPowDist"])

    #: The review's own table, verbatim.  Every one of these was FREE -- no key
    #: at all, so not even a coarse row a reviewer could see -- because the head
    #: extractor's three stages all read position 0 and one ordinary adjective
    #: is enough to move the number off it.  Widening the *determiner* list
    #: twice never touched this, because English puts whatever it likes between
    #: a determiner and a number.
    MODIFIED_HEADS = (
        ("Narrow child module for the following 12 foo wrappers.", "?12"),
        ("Narrow child module for concrete 12 foo wrappers.", "?12"),
        ("Narrow child module for Λ-level 12 foo wrappers.", "?12"),
        ("Narrow child module for a family of 12 foo wrappers.", "?12"),
        ("Narrow child module for the set of 12 foo wrappers.", "?12"),
        ("Narrow child module for a batch of twelve foo wrappers.", "?12"),
        ("Narrow child module for the following 17 along-exhaustion helper wrappers.", "?17"),
        ("Narrow child module for the concrete narrow Λ-level 12 foo wrappers.", "?12"),
        ("Narrow child module for the assorted twelve hundred foo wrappers.", "?1200"),
        ("Narrow child module for the concrete about 1.5k foo wrappers.", "?about 1.5k"),
        ("Narrow child module for the assorted several foo wrappers.", "?several"),
    )

    def test_a_count_behind_a_modifier_is_charged(self) -> None:
        """H1: a size the clause states is charged wherever in the clause it sits.

        Under a ``?`` token, because the extractor is not claiming to know which
        noun it counts -- and still sharp, so editing the number is a new key.
        """
        for body, expected in self.MODIFIED_HEADS:
            source = lean_source("M", header(body))
            self.assertEqual(tokens(source, "NARROW_CHILD"), [expected], body)
            self.assertEqual(telemetry(source), [], body)

    def test_a_head_position_count_is_still_charged_as_itself(self) -> None:
        """The sharper reading wins where it applies: no ``?`` on a head count."""
        source = lean_source("M", header("Narrow child module for all 12 foo wrappers."))
        self.assertEqual(tokens(source, "NARROW_CHILD"), ["12"])

    #: What must stay free, and every one of them is live in this corpus.  A
    #: number behind a citation word, in a code span, or in a relation is not an
    #: inventory count, and charging it would buy recall with false charges --
    #: which is what the head-position rule was defending against.
    UNCOUNTED_HEADS = (
        "Narrow child module for Step 241 interior wrappers.",
        "Narrow child module for PR 1861 interior wrappers.",
        "Narrow child module for Issue 4501 interior wrappers.",
        "Narrow child module for the §18.3 interior wrappers.",
        "Narrow child module for the #4501 interior wrappers.",
        "Narrow child module for lemma 17.5.2 wrappers.",
        "Narrow child module for the wrappers of section 3 and 4.",
        "Narrow child module for the `mayerPartialSum 0 ≤ f` comparison wrappers.",
        "Narrow child module for the `vdPolymerFamilies_sum - 1` tendsto-zero wrapper.",
        "Narrow child module for the susceptibilityInfinite J = 0 closed form wrappers.",
        "Narrow child module for the Λ-level odd-vanish at h=0 wrappers.",
        "Narrow child module for the two-sided foo wrappers.",
        "Narrow child module for the `zero`-boundary foo wrappers.",
    )

    def test_a_number_that_counts_nothing_stays_uncharged(self) -> None:
        """The other arm of H1, and the reason the fix is lexical and not positional."""
        for body in self.UNCOUNTED_HEADS:
            source = lean_source("M", header(body))
            self.assertEqual(tokens(source, "NARROW_CHILD"), [], body)
            self.assertEqual([claim.token for claim in telemetry(source)], ["-"], body)

    def test_two_counts_in_one_clause_are_charged_unresolved(self) -> None:
        """Ambiguity is charged, never dropped: R3.1 applies to *which* count too."""
        source = lean_source(
            "M", header("Narrow child module for concrete 3 foo and 4 bar wrappers.")
        )
        self.assertEqual(tokens(source, "NARROW_CHILD"), ["?3/4"])

    def test_a_quantity_phrase_is_read_once(self) -> None:
        """``twelve hundred`` opens at both its words; it is one count, not two."""
        self.assertEqual(ratchet.clause_quantities("assorted twelve hundred wrappers"), ("1200",))
        self.assertEqual(ratchet.clause_quantities("assorted about 1.5k wrappers"),
                         ("?about 1.5k",))

    def test_a_vague_quantifier_is_charged(self) -> None:
        """`the remaining wrappers` fails the split-stability test as a number does."""
        source = lean_source("M", header("Narrow child module for the remaining wrappers."))
        self.assertEqual(tokens(source, "NARROW_CHILD"), ["remaining"])

    def test_parenthetical_count(self) -> None:
        """`(13 theorems)` counts a subset of this module."""
        body = "Narrow child module for the basic wrappers (13 theorems):"
        source = lean_source("M", header(body))
        self.assertEqual(tokens(source, "PAREN_COUNT"), ["13:theorems"])

    def test_possessive_count(self) -> None:
        """`its 4 properties` counts a subset of this module."""
        source = lean_source("M", header("Defines `susceptibilityInfinite` and its 4 properties."))
        self.assertEqual(tokens(source, "POSSESSIVE_COUNT"), ["4:properties"])

    def test_predicate_count(self) -> None:
        """`contains ten wrappers` counts this module."""
        source = lean_source("M", header("Its entry-point package contains ten wrappers."))
        self.assertEqual(tokens(source, "PREDICATE_COUNT"), ["10:wrappers"])

    def test_relocation_names_the_other_module(self) -> None:
        """The one shape whose referent is a *different* module."""
        source = lean_source(
            "M", header("The 13 bridge wrappers now live in `IsingModel.Other.TanhPowDist`.")
        )
        self.assertEqual(tokens(source, "RELOCATION"), ["13->IsingModel.Other.TanhPowDist"])

    def test_a_relocation_subject_reaches_across_a_backticked_list(self) -> None:
        """This repository's house style, and what the 70-character cap cost.

        The count is written first and the noun it counts comes after a list of
        the names being moved, which is routinely more than 70 characters long.
        At 70 the claim was *accounted* -- charged nothing -- and 210 live sites
        on the tracked tree had exactly this shape.
        """
        source = lean_source(
            "M",
            header(
                "The 10 Λ-level h-symmetry, odd-vanish at h=0, J_zero, and tanh-power "
                "lower-bound wrappers now live in `IsingModel.Other.Bounds`."
            ),
        )
        self.assertEqual(tokens(source, "RELOCATION"), ["10->IsingModel.Other.Bounds"])

    def test_a_relocation_subject_may_carry_any_determiner(self) -> None:
        """The determiner list is shared with the head extractor, so both see these."""
        for determiner in ("The", "These", "Those", "Its", "All", "Our", "Their", "This"):
            source = lean_source(
                "M", header(f"{determiner} 13 bridge wrappers now live in `IsingModel.Other`.")
            )
            self.assertEqual(
                tokens(source, "RELOCATION"), ["13->IsingModel.Other"], determiner
            )

    #: A destination wrapped across a line break, verbatim from
    #: `SusceptibilityPointwiseRegularityAt.lean`.  This repository breaks a long
    #: module name at a dot and closes the backticks on each half, so a
    #: single-span destination read `IsingModel.AmbientLattice.SpecialCases.` --
    #: a namespace, not a module -- and four pinned rows were in that state.
    WRAPPED_DESTINATION = (
        "The three pointwise `SusceptibilityAt` regularity wrappers now live in\n"
        "`IsingModel.AmbientLattice.SpecialCases.`\n"
        "`SusceptibilityPointwiseRegularityAtDifferentiableAt`\n"
        "and are re-imported through this parent module."
    )

    def test_a_destination_wrapped_across_a_line_is_read_whole(self) -> None:
        """M2: the fact this class exists to pin has to be in the key."""
        source = lean_source("M", header(self.WRAPPED_DESTINATION))
        self.assertEqual(
            tokens(source, "RELOCATION"),
            ["3->IsingModel.AmbientLattice.SpecialCases."
             "SusceptibilityPointwiseRegularityAtDifferentiableAt"],
        )

    def test_a_second_reference_that_is_not_a_wrap_is_not_joined(self) -> None:
        """Only whitespace joins: a listed name, or a new sentence, is separate."""
        for body, expected in (
            ("The three foo wrappers now live in `IsingModel.A`, `IsingModel.B`.",
             "3->IsingModel.A"),
            ("The three foo wrappers now live in `IsingModel.A`. `IsingModel.B` is unchanged.",
             "3->IsingModel.A"),
            ("The three foo wrappers now live in `IsingModel.A` and `IsingModel.B`.",
             "3->IsingModel.A"),
        ):
            source = lean_source("M", header(body))
            self.assertEqual(tokens(source, "RELOCATION"), [expected], body)

    def test_a_texttt_or_path_destination_is_read(self) -> None:
        """The TeX guide writes most of its file names with `\\path`."""
        for markup in (r"\texttt{Foo/Bar.lean}", r"\path{Foo/Bar.lean}"):
            source = doc_source(
                "tex/proof-guide.tex",
                f"The three foo wrappers now live in {markup}.",
            )
            self.assertEqual(tokens(source, "RELOCATION"), ["3->Foo/Bar.lean"], markup)

    #: The live misattribution, verbatim from
    #: `AmbientLattice/SpecialCases/JointRegularityDifferentiable.lean`: a count
    #: in one paragraph and, after a bulleted list, a relocation of *one* wrapper
    #: in the next.  The noun-to-anchor gap is under 200 characters, so the
    #: widened window resolved the subject -- across a paragraph break -- and
    #: pinned the sentence `2->X`, a number it does not state.
    PARAGRAPH_CROSSING = (
        "Narrow child module for the two along-exhaustion joint\n"
        "`Differentiable` wrappers in the correlation / magnetization\n"
        "observables:\n\n"
        "* `correlationAlongExhaustion_differentiable_joint_gen`\n"
        "* `magnetizationAlongExhaustion_differentiable_joint`\n\n"
        "The corresponding susceptibility wrapper now lives in\n"
        "`IsingModel.Other.Susceptibility`."
    )

    def test_a_count_may_not_be_borrowed_across_a_paragraph_break(self) -> None:
        """M1: a clause window may cross a line wrap; it may never cross a blank line."""
        source = lean_source("M", header(self.PARAGRAPH_CROSSING))
        self.assertEqual(tokens(source, "RELOCATION"), ["->IsingModel.Other.Susceptibility"])
        self.assertEqual(tokens(source, "NARROW_CHILD"), ["2"], "the real count still charges")

    def test_a_subject_still_reaches_across_a_line_wrap(self) -> None:
        """Anti-vacuity for the rule above: an ordinary wrapped sentence resolves.

        Line wraps are how this repository writes every long claim, so a rule
        that refused them would be a recall collapse rather than a fix.
        """
        source = lean_source(
            "M",
            header(
                "The three `alpha`, `beta` and\n`gamma` wrappers\nnow live in\n"
                "`IsingModel.Other`."
            ),
        )
        self.assertEqual(tokens(source, "RELOCATION"), ["3->IsingModel.Other"])

    def test_relocation_survives_an_intervening_clause(self) -> None:
        """The docs/index.md:1393 archetype, with a PR reference in the middle."""
        source = doc_source(
            "docs/index.md",
            "the three `_cubicExhaustion_monotone_{h,beta,J}` wrappers were split out again "
            "in PR #2354 and now live in `Concrete/Two.lean`.",
        )
        self.assertEqual(tokens(source, "RELOCATION"), ["3->Concrete/Two.lean"])

    def test_a_claim_inside_a_nested_block_comment_is_seen(self) -> None:
        """Lean block comments nest; a first-`-/` parser would misplace this claim."""
        text = "/- outer /- inner -/ Narrow child module for the 5 foo wrappers. -/\n"
        source = lean_source("M", "/-!\n# F\n-/\n" + text)
        self.assertEqual(tokens(source, "NARROW_CHILD"), ["5"])

    def test_every_class_declares_one_of_the_three_referents(self) -> None:
        """The referent is part of the key: two shapes can mean two modules."""
        for claim_class in ratchet.CLAIM_CLASSES:
            self.assertIn(claim_class.referent, ratchet.REFERENTS, claim_class.name)
        self.assertEqual(
            {claim_class.referent for claim_class in ratchet.CLAIM_CLASSES},
            set(ratchet.REFERENTS),
            "the grammar's three referents must all be represented",
        )

    def test_the_recognized_class_set_is_pinned(self) -> None:
        """Dropping a shape must be an explicit, reviewed edit, not a silent one."""
        self.assertEqual(
            [claim_class.name for claim_class in ratchet.CLAIM_CLASSES],
            ["NARROW_CHILD", "PAREN_COUNT", "POSSESSIVE_COUNT", "PREDICATE_COUNT", "RELOCATION"],
        )


# --------------------------------------------------------------------------
# Negative fixtures
# --------------------------------------------------------------------------


class NegativeTest(unittest.TestCase):
    """Prose the convention permits must not be charged."""

    def test_a_purpose_only_header_is_not_charged(self) -> None:
        """The target style: intension, no extension."""
        source = lean_source(
            "M",
            header(
                "Provides lattice-graph specializations of ambient-subgraph monotonicity "
                "used by the infinite-volume correlation and magnetization APIs."
            ),
        )
        self.assertEqual(charged(source), [])

    def test_naming_an_upstream_dependency_is_not_charged(self) -> None:
        """Headers legitimately cite what they build on; that is not an inventory."""
        source = lean_source(
            "M",
            header("Builds on `Current.reachableCluster_confined_eq` and `pseudoMassG`."),
        )
        self.assertEqual(charged(source), [])

    def test_a_literature_count_is_not_charged(self) -> None:
        """A count of mathematical objects survives a module split, so it is out of scope."""
        source = doc_source(
            "docs/index.md",
            "GJ Theorem 17.5.1 has three parts; the proof needs two ingredients and "
            "four cases, and covers both signs.",
        )
        self.assertEqual(charged(source), [])

    def test_an_unquantified_narrow_child_header_is_telemetry_not_a_claim(self) -> None:
        """`for concrete latticeGraph specializations` states no size."""
        source = lean_source(
            "M", header("Narrow child module for concrete `latticeGraph` specializations of X.")
        )
        scanned = ratchet.scan_source(source)
        self.assertEqual(scanned.claims, ())
        self.assertEqual([claim.kind for claim in scanned.telemetry], ["NARROW_CHILD"])

    def test_an_unquantified_relocation_is_charged_on_its_anchor(self) -> None:
        """The ownership assertion is itself the claim, size or no size.

        This is the largest single correction the tool has had: 647 of the
        tree's 767 ``now live in X`` sentences were *accounted* -- recognized
        and free -- because the charge was made conditional on parsing an
        adjacent count, so the quantity extractor was deciding exemption.
        """
        source = lean_source("M", header("The basic wrappers now live in `IsingModel.Other`."))
        self.assertEqual(tokens(source, "RELOCATION"), ["->IsingModel.Other"])
        self.assertEqual(telemetry(source), [])

    def test_a_pr_reference_is_not_mistaken_for_a_quantity(self) -> None:
        """`Step 241 interior wrappers now live in X` must charge, but not 241."""
        source = lean_source(
            "M",
            header("The regularity wrappers (Step 241 interior `ContinuousAt` wrappers) "
                   "now live in `IsingModel.Other`."),
        )
        self.assertEqual(tokens(source, "RELOCATION"), ["->IsingModel.Other"])

    def test_a_hyphenated_cardinal_subject_is_not_a_count(self) -> None:
        """`The zero-boundary ... wrappers now live in X` must not be pinned as 0.

        Measured on the live tree: the relocation subject bound the cardinal
        ``zero`` out of ``zero-boundary`` and keyed a real claim under a number
        the sentence does not state.  The claim is charged either way -- only the
        sharpness of the key is at stake -- so a wrong number is pure loss.
        """
        source = lean_source(
            "M", header("The zero-boundary linear bound wrappers now live in `IsingModel.Other`.")
        )
        self.assertEqual(tokens(source, "RELOCATION"), ["->IsingModel.Other"])

    def test_a_declaration_line_matches_no_anchor(self) -> None:
        """Anti-scope: this checker cannot see declarations, by construction.

        The predecessor design's H2 (does a cited name exist in this module?) was
        measured at ~5 % signal-to-noise and deliberately not built; nothing here
        may drift back towards it.
        """
        line = "theorem foo_bar (n : Nat) : True := trivial"
        for claim_class in ratchet.CLAIM_CLASSES:
            self.assertIsNone(claim_class.anchor.search(line), claim_class.name)


# --------------------------------------------------------------------------
# Charged, never skipped
# --------------------------------------------------------------------------


class ChargedNotSkippedTest(unittest.TestCase):
    """An input the checker cannot inspect is a finding, not a free pass."""

    def test_a_module_without_a_docstring_is_charged(self) -> None:
        """There is no header to inspect, so the module is charged, not exonerated.

        It also closes the cheapest evasion: deleting the whole ``/-!`` block
        would otherwise be a way to make a claim disappear without writing the
        purpose statement that is supposed to replace it.
        """
        source = lean_source("M", "import IsingModel.Basic\n\ntheorem f : True := trivial\n")
        self.assertEqual([c.kind for c in charged(source)], [ratchet.MISSING_DOC])

    def test_an_unterminated_comment_is_charged(self) -> None:
        """A file whose comment structure does not close cannot be trusted."""
        source = lean_source("M", "/-! # F\n\nNarrow child module for the 3 foo wrappers.\n")
        kinds = [claim.kind for claim in charged(source)]
        self.assertIn(ratchet.UNTERMINATED, kinds)

    def test_an_anchor_outside_prose_is_charged(self) -> None:
        """A claim in a string literal is attributable to nothing; charge it."""
        source = lean_source(
            "M",
            '/-!\n# F\n-/\n\ndef s : String := "Narrow child module for the 3 foo wrappers"\n',
        )
        self.assertEqual([c.kind for c in charged(source)], [ratchet.NON_PROSE])

    def test_an_unreadable_tracked_target_is_a_conservation_failure(self) -> None:
        """K0: a tracked path that cannot be read is never silently dropped."""
        report = ratchet.build_report(root=REPO_ROOT, paths=["IsingModel/DoesNotExist.lean"])
        self.assertFalse(report.sound)
        self.assertTrue(any(failure.startswith("K0") for failure in report.conservation))

    def test_an_undecodable_tracked_target_is_a_conservation_failure(self) -> None:
        """K0 arrives through the finding channel, not as a traceback.

        A tracked file holding a non-UTF-8 byte raised ``UnicodeDecodeError``
        out of the reader.  The run still failed closed, by crashing, but a
        crash reports nothing about the other 1900 targets and is not the
        contract ``K0`` states.
        """
        with tempfile.TemporaryDirectory(prefix="claim-ratchet-bytes-") as tmp:
            root = Path(tmp)
            (root / "IsingModel").mkdir()
            (root / "IsingModel" / "Binary.lean").write_bytes(b"/-!\n# F \xff\n-/\n")
            report = ratchet.build_report(root=root, paths=["IsingModel/Binary.lean"])
        self.assertFalse(report.sound)
        self.assertTrue(
            any(failure.startswith("K0") for failure in report.conservation),
            report.conservation,
        )

    #: The check that makes the sentinel docstring an assertion.
    NO_SENTINEL_CHECK = (
        "        if any(sentinel in text for sentinel in SENTINELS):\n",
        "        if False:\n",
    )

    def sentinel_report(self, module=ratchet):
        """Scan a tracked file that carries a scanner sentinel in its prose."""
        with tempfile.TemporaryDirectory(prefix="claim-ratchet-sentinel-") as tmp:
            root = Path(tmp)
            (root / "IsingModel").mkdir()
            (root / "IsingModel" / "Nul.lean").write_text(
                header(f"Narrow child module for {ratchet.MASK}the 12 foo wrappers."),
                encoding="utf-8",
            )
            return module.build_report(root=root, paths=["IsingModel/Nul.lean"])

    def test_a_source_holding_a_scanner_sentinel_is_a_conservation_failure(self) -> None:
        """K0: the mask sentinel is asserted absent, not assumed absent."""
        report = self.sentinel_report()
        self.assertFalse(report.sound)
        self.assertTrue(
            any(failure.startswith("K0") for failure in report.conservation),
            report.conservation,
        )

    def test_without_that_check_a_sentinel_makes_a_claim_free(self) -> None:
        """Anti-vacuity: absurd as an attack, and it really does buy silence.

        ``Narrow child module for <NUL>the 12 foo wrappers`` reads as a header
        that states no size, because the head clause may not cross a mask -- so
        the record lands in telemetry and the count costs nothing.
        """
        mutant = load_mutant(self.NO_SENTINEL_CHECK)
        report = self.sentinel_report(mutant)
        self.assertTrue(report.sound)
        self.assertEqual([claim.token for claim in report.telemetry], ["-"])
        self.assertEqual(report.charged, Counter())


# --------------------------------------------------------------------------
# The shared Lean lexicon
# --------------------------------------------------------------------------

#: Lean forms in which the three characters ``/-!`` appear *outside* any comment.
#: Both were checked against this repository's pinned toolchain: guillemet
#: identifiers accept every character but ``»``, and a raw string accepts every
#: character up to its closing delimiter.  A lexer that does not know them reads
#: the module as having a docstring, which silently retires the one charge class
#: that exists to stop "delete the header instead of repairing it".
FAKE_MODULE_DOC_FORMS = (
    'def «/-! fake -/» : Nat := 1\n',
    'def s : String := r"/-! fake -/"\n',
    'def s : String := r#"/-! fake -/ "quoted" "#\n',
)

#: Inputs on which a reduced Lean lexer can plausibly disagree with itself.
LEXICALLY_HARD = (
    'def «/-! fake -/» : Nat := 1\n',
    'def «a » b» : Nat := 1\n',
    'def s := r"a /- b"\ndef t := 2\n',
    'def s := r#"a "-/" b"#\ndef t := 2\n',
    '/- outer /- inner -/ still -/\ndef x := 1\n',
    'def s := "escaped \\" quote /- not a comment"\n',
    '-- line /- comment\ndef x := 1\n',
    'def «/-» : Nat := 1\n',
    "def c : Char := '\"'\ndef t := 2\n",
    "def g : Char := '«'\ndef t := 2\n",
    "def q : Char := '\\''\ndef t := 2\n",
    "def b : Char := '\\\\'\ndef t := 2\n",
    "theorem h' (x' : Nat) : True := trivial\n",
    "def s := \"it's not a literal\"\ndef t := 2\n",
    "def r : Char := 'r'\ndef s := \"plain\"\n",
)

#: Lean character literals whose *body* is a delimiter the lexer would otherwise
#: open a span on.  Both compile under this repository's pinned toolchain.
CHAR_LITERAL_FORMS = (
    "def c : Char := '\"'\n",
    "def g : Char := '«'\n",
)


class LexiconTest(unittest.TestCase):
    """The two decomposers must agree, and must agree on the *right* lexicon."""

    def test_a_fake_opener_outside_a_comment_does_not_exonerate_the_module(self) -> None:
        """The evasion `MISSING_MODULE_DOC` exists to stop, one lexical layer down."""
        for body in FAKE_MODULE_DOC_FORMS:
            text = f"import IsingModel.Basic\n\n{body}{TRIVIAL}"
            source = lean_source("M", text)
            self.assertEqual([c.kind for c in charged(source)], [ratchet.MISSING_DOC], body)
            self.assertEqual(ratchet.scan_source(source).conservation, (), body)

    def test_a_real_module_docstring_still_counts(self) -> None:
        """Anti-vacuity: the new lexical classes must not swallow the real opener."""
        source = lean_source("M", header("Provides the foo API.") + 'def «x» := 1\n')
        self.assertEqual(charged(source), [])

    def test_a_claim_inside_a_quoted_identifier_is_not_prose(self) -> None:
        """It is attributable to no header, so it is charged as `NON_PROSE_ANCHOR`."""
        text = '/-!\n# F\n-/\n\ndef «Narrow child module for the 3 foo wrappers» : Nat := 1\n'
        self.assertEqual([c.kind for c in charged(lean_source("M", text))], [ratchet.NON_PROSE])

    def test_an_unterminated_quoted_identifier_is_charged(self) -> None:
        """The file's structure is unknown after it, so it is not a clean parse."""
        text = '/-!\n# F\n-/\n\ndef «never closed : Nat := 1\n'
        self.assertIn(
            ratchet.UNTERMINATED, [claim.kind for claim in charged(lean_source("M", text))]
        )

    def test_the_two_decomposers_agree_on_lexically_hard_input(self) -> None:
        """K3 in fixture form, on the inputs a reduced lexer gets wrong."""
        for text in LEXICALLY_HARD:
            self.assertEqual(ratchet.decompose(text).regions, ratchet.reference_regions(text), text)

    def test_a_character_literal_holding_a_delimiter_is_not_a_false_charge(self) -> None:
        """`'"'` and `'«'` are valid Lean, and they used to turn the gate red.

        Fail-closed rather than a bypass -- the module was charged
        ``UNTERMINATED_COMMENT`` *and* ``MISSING_MODULE_DOC`` -- but on two keys
        no pin holds, so one legitimate ``Char`` literal added anywhere under the
        Lean root would have failed CI with nothing wrong in the prose.
        """
        for body in CHAR_LITERAL_FORMS:
            text = header("Provides the foo API.") + body + TRIVIAL
            source = lean_source("M", text)
            self.assertEqual(charged(source), [], body)
            self.assertEqual(ratchet.scan_source(source).conservation, (), body)
            self.assertTrue(ratchet.decompose(text).terminated, body)

    def test_a_prime_in_an_identifier_does_not_open_a_character_literal(self) -> None:
        """Anti-vacuity for the lookbehind: this corpus is full of `h'` and `x''`."""
        text = header("Provides the foo API.") + "theorem h' (x'' : Nat) : True := trivial\n"
        source = lean_source("M", text)
        self.assertEqual(charged(source), [])
        self.assertEqual(ratchet.scan_source(source).conservation, ())

    def test_a_scanner_blind_to_character_literals_charges_a_clean_module(self) -> None:
        """The bug as measured, and the proof that removing the class restores it."""
        mutant = load_mutant(("|{_CHAR_LITERAL}|«|", "|«|"))
        text = header("Provides the foo API.") + "def c : Char := '\"'\n" + TRIVIAL
        self.assertEqual(charged(lean_source("M", text)), [])
        kinds = [c.kind for c in charged(lean_source("M", text, mutant), mutant)]
        self.assertIn(mutant.UNTERMINATED, kinds)

    def test_the_oracle_would_catch_a_character_literal_lexicon_split(self) -> None:
        """K3 again: mutate the oracle alone and the two decomposers must disagree."""
        mutant = load_mutant(
            ("    literal = _reference_char_literal_end(text, index)\n", "    literal = None\n"),
        )
        text = '/-!\n# F\n-/\ndef c : Char := \'"\'\n-- a line comment\ndef s := "x"\n'
        self.assertEqual(ratchet.scan_source(lean_source("M", text)).conservation, ())
        failures = mutant.scan_source(lean_source("M", text, mutant)).conservation
        self.assertTrue(any(failure.startswith("K3") for failure in failures), failures)

    def test_a_scanner_blind_to_quoted_identifiers_exonerates_the_module(self) -> None:
        """The bug as measured, and the proof that K3 now contradicts it.

        With the guillemet class removed from the scanner alone, ``/-!`` inside
        an identifier opens a comment: the module is exonerated from
        :data:`MISSING_DOC` -- and, because the oracle still knows the class, the
        decomposition disagrees and ``K3`` fires.  Removed from *both*, as it was,
        nothing fires at all.
        """
        mutant = load_mutant(("|{_CHAR_LITERAL}|«|", "|{_CHAR_LITERAL}|"))
        text = f'import IsingModel.Basic\n\ndef «/-! fake -/» : Nat := 1\n{TRIVIAL}'
        self.assertEqual(
            [c.kind for c in charged(lean_source("M", text))], [ratchet.MISSING_DOC]
        )
        scanned = mutant.scan_source(lean_source("M", text, mutant))
        self.assertNotIn(mutant.MISSING_DOC, [claim.kind for claim in scanned.claims])
        self.assertTrue(any(f.startswith("K3") for f in scanned.conservation), scanned.conservation)

    def test_the_oracle_is_what_would_catch_a_lexicon_split(self) -> None:
        """K3 is independent in code, not in lexicon -- so mutate one side alone.

        Nothing asserted that the two decomposers *could* disagree on a hard
        input, which is exactly how the guillemet blind spot survived: it was
        present in both, so K3 stayed green while both were wrong.
        """
        mutant = load_mutant(
            ('    if text[index] == "«":\n', "    if False:\n"),
        )
        text = '/-!\n# F\n-/\ndef «/- fake -/» : Nat := 1\n'
        self.assertEqual(ratchet.scan_source(lean_source("M", text)).conservation, ())
        failures = mutant.scan_source(lean_source("M", text, mutant)).conservation
        self.assertTrue(any(failure.startswith("K3") for failure in failures), failures)


# --------------------------------------------------------------------------
# Conservation
# --------------------------------------------------------------------------


class ConservationTest(unittest.TestCase):
    """K1/K2 hold on healthy input and suppress the report when they do not."""

    def test_a_healthy_source_is_sound(self) -> None:
        """Anti-vacuity for the failing cases below."""
        source = lean_source("M", header("Narrow child module for the 3 foo wrappers."))
        self.assertEqual(ratchet.scan_source(source).conservation, ())

    def unsound_report(self) -> ratchet.Report:
        """Return a report carrying a synthetic conservation failure."""
        source = lean_source("M", header("Narrow child module for the 3 foo wrappers."))
        scanned = ratchet.scan_source(source)
        return ratchet.Report(
            sources=(source,),
            claims=scanned.claims,
            telemetry=scanned.telemetry,
            conservation=("K1 M [NARROW_CHILD]: 2 raw anchor(s) produced 1 record(s)",),
        )

    def test_an_unsound_run_suppresses_the_text_report(self) -> None:
        """No class table, no ratchet verdict: nothing reassuring is printed."""
        buffer = io.StringIO()
        with contextlib.redirect_stdout(buffer):
            ok = ratchet.print_report(self.unsound_report(), Counter(), [])
        output = buffer.getvalue()
        self.assertFalse(ok)
        self.assertNotIn("== Recognized claim classes ==", output)
        self.assertNotIn("== Ratchet ==", output)
        self.assertIn("suppressed", output)

    def test_an_unsound_run_suppresses_every_machine_format(self) -> None:
        """`--baseline` and `--findings` must not emit a population either."""
        original = ratchet.build_report
        ratchet.build_report = lambda *a, **k: self.unsound_report()  # noqa: E731
        try:
            for flag in ("--baseline", "--findings"):
                buffer = io.StringIO()
                with contextlib.redirect_stdout(buffer):
                    code = ratchet.main([flag])
                output = buffer.getvalue()
                self.assertEqual(code, 1, flag)
                self.assertIn("SUPPRESSED", output, flag)
                data = [line for line in output.splitlines() if not line.startswith("#")]
                self.assertEqual(data, [], flag)
        finally:
            ratchet.build_report = original


# --------------------------------------------------------------------------
# The ratchet itself
# --------------------------------------------------------------------------


def population(*pairs: tuple[tuple[str, str, str], int]) -> Counter:
    """Build a charged-claim multiset from ``(key, count)`` pairs."""
    return Counter(dict(pairs))


KEY_A = ("NARROW_CHILD", "IsingModel/A.lean", "12")
KEY_B = ("NARROW_CHILD", "IsingModel/B.lean", "4")


class RatchetTest(unittest.TestCase):
    """Monotone non-increase, per key, with no scalar to offset against."""

    def test_an_unchanged_population_passes(self) -> None:
        base = population((KEY_A, 1), (KEY_B, 1))
        self.assertFalse(ratchet.compare(base, base).regressed)

    def test_a_new_key_fails(self) -> None:
        base = population((KEY_A, 1))
        comparison = ratchet.compare(population((KEY_A, 1), (KEY_B, 1)), base)
        self.assertTrue(comparison.regressed)
        self.assertEqual([key for key, _count in comparison.new], [KEY_B])

    def test_a_grown_count_fails(self) -> None:
        base = population((KEY_A, 1))
        comparison = ratchet.compare(population((KEY_A, 2)), base)
        self.assertTrue(comparison.regressed)
        self.assertEqual([key for key, _now, _was in comparison.grown], [KEY_A])

    def test_a_shrunken_population_passes_and_reports_slack(self) -> None:
        base = population((KEY_A, 2), (KEY_B, 1))
        comparison = ratchet.compare(population((KEY_A, 1)), base)
        self.assertFalse(comparison.regressed)
        self.assertEqual({key for key, _now, _was in comparison.slack}, {KEY_A, KEY_B})

    def test_one_fix_cannot_pay_for_one_regression(self) -> None:
        """The whole reason the key is a multiset and not a scalar."""
        base = population((KEY_A, 1))
        comparison = ratchet.compare(population((KEY_B, 1)), base)
        self.assertTrue(comparison.regressed)

    def test_a_malformed_baseline_line_is_an_error_not_a_dropped_row(self) -> None:
        """A silently dropped baseline row would ratchet the population *up*."""
        _counts, errors = ratchet.parse_baseline("NARROW_CHILD\tIsingModel/A.lean\n")
        self.assertTrue(errors)
        _counts, errors = ratchet.parse_baseline("NARROW_CHILD\tIsingModel/A.lean\t12\tmany\n")
        self.assertTrue(errors)

    def test_the_baseline_round_trips(self) -> None:
        base = population((KEY_A, 3), (KEY_B, 1))
        parsed, errors = ratchet.parse_baseline(ratchet.format_baseline(base))
        self.assertEqual(errors, [])
        self.assertEqual(parsed, base)

    def test_the_report_never_says_the_headers_are_clean(self) -> None:
        """False assurance is the risk the arbitration named as the biggest one."""
        source = lean_source("M", header("Provides the ambient monotonicity API."))
        scanned = ratchet.scan_source(source)
        report = ratchet.Report(
            sources=(source,), claims=scanned.claims, telemetry=scanned.telemetry,
            conservation=(),
        )
        buffer = io.StringIO()
        with contextlib.redirect_stdout(buffer):
            ok = ratchet.print_report(report, Counter(), [])
        output = buffer.getvalue()
        self.assertTrue(ok)
        self.assertIn("A pass never means the headers are clean.", output)
        self.assertIn("says nothing about unrecognized prose", output)

    def test_the_report_says_a_falling_count_is_not_evidence_of_repair(self) -> None:
        """The governance consequence of a finite grammar, printed on every run.

        A claim reworded into an unrecognized shape lowers these totals exactly
        as a repair does, so the number is a prompt to read the findings diff and
        never a substitute for reading it.
        """
        source = lean_source("M", header("Provides the ambient monotonicity API."))
        scanned = ratchet.scan_source(source)
        report = ratchet.Report(
            sources=(source,), claims=scanned.claims, telemetry=scanned.telemetry,
            conservation=(),
        )
        buffer = io.StringIO()
        with contextlib.redirect_stdout(buffer):
            ratchet.print_report(report, Counter(), [])
        output = buffer.getvalue()
        self.assertIn("a FALL in them is not by itself evidence that prose", output)
        self.assertIn("--findings diff", output)


# --------------------------------------------------------------------------
# Mutation canaries
# --------------------------------------------------------------------------


class MutationCanaryTest(unittest.TestCase):
    """Each canary weakens the checker and requires the weakening to show."""

    def corpus(self, module=ratchet):
        """Return sources exercising the article variant and a word number."""
        return (
            lean_source("A", header("Narrow child module for 12 foo wrappers."), module),
            lean_source("B", header("Narrow child module for the four foo wrappers."), module),
        )

    def charged_count(self, module) -> int:
        """Return the number of charged claims the given module finds."""
        return sum(len(charged(source, module)) for source in self.corpus(module))

    def test_weakening_the_anchor_loses_claims(self) -> None:
        """Requiring the article -- Unit 4's exact bug -- must be visible."""
        mutant = load_mutant(
            ('_NARROW_CHILD_ANCHOR = re.compile(r"Narrow child module", re.IGNORECASE)',
             '_NARROW_CHILD_ANCHOR = re.compile(r"Narrow child module for the", re.IGNORECASE)')
        )
        real = self.charged_count(ratchet)
        self.assertEqual(real, 2)
        self.assertLess(self.charged_count(mutant), real)

    def test_skipping_an_unresolved_token_is_caught_by_conservation(self) -> None:
        """The ``_resolve_fragment`` failure mode: a lost record, not a lost verdict."""
        mutant = load_mutant(
            (
                "                token, charged, note = claim_class.extract(raw.text, match)\n",
                "                token, charged, note = claim_class.extract(raw.text, match)\n"
                "                if not charged:\n"
                "                    continue\n",
            )
        )
        text = header("Narrow child module for concrete `latticeGraph` specializations.")
        self.assertEqual(ratchet.scan_source(lean_source("M", text)).conservation, ())
        failures = mutant.scan_source(lean_source("M", text, mutant)).conservation
        self.assertTrue(failures)
        self.assertTrue(any(failure.startswith("K1") for failure in failures))

    def test_dropping_the_conservation_assert_hides_the_lost_record(self) -> None:
        """Proves K1 is load-bearing: without it, the same skip passes silently."""
        mutant = load_mutant(
            (
                "                token, charged, note = claim_class.extract(raw.text, match)\n",
                "                token, charged, note = claim_class.extract(raw.text, match)\n"
                "                if not charged:\n"
                "                    continue\n",
            ),
            ("        if produced != len(raw_matches):", "        if False:"),
        )
        text = header("Narrow child module for concrete `latticeGraph` specializations.")
        scanned = mutant.scan_source(lean_source("M", text, mutant))
        self.assertEqual(scanned.conservation, ())
        self.assertEqual(len(scanned.claims) + len(scanned.telemetry), 0)
        real = ratchet.scan_source(lean_source("M", text))
        self.assertEqual(len(real.claims) + len(real.telemetry), 1)

    #: Claims whose count is a cardinal the shipped lexicon did not know, one
    #: per recognized class.  ``NARROW_CHILD`` reached its extractor and was told
    #: "not a quantity", so it was *accounted* -- zero charge, no mention in the
    #: totals; the other four never matched their anchor at all and produced no
    #: record whatsoever.
    VOCABULARY_FORMS = (
        ("NARROW_CHILD", "Narrow child module for sixty foo wrappers.", "60"),
        ("NARROW_CHILD", "Narrow child module for seventy-two foo wrappers.", "72"),
        ("PAREN_COUNT", "Basic wrappers (sixty theorems):", "60:theorems"),
        ("PREDICATE_COUNT", "Its package contains eighty wrappers.", "80:wrappers"),
        ("POSSESSIVE_COUNT", "Defines `x` and its ninety properties.", "90:properties"),
        ("RELOCATION", "The sixty foo wrappers now live in `X`.", "60->X"),
    )

    #: The same hole reached through a numeric idiom rather than a missing word.
    IDIOM_FORMS = (
        ("NARROW_CHILD", "Narrow child module for ~12 foo wrappers.", "~12"),
        ("NARROW_CHILD", "Narrow child module for about 12 foo wrappers.", "~12"),
        ("NARROW_CHILD", "Narrow child module for 1,024 foo wrappers.", "1024"),
        ("NARROW_CHILD", "Narrow child module for 12+ foo wrappers.", "12+"),
        ("NARROW_CHILD", "Narrow child module for 12-ish foo wrappers.", "?12-ish"),
        ("PAREN_COUNT", "Basic wrappers (about 13 theorems):", "~13:theorems"),
        ("PAREN_COUNT", "Basic wrappers (1,024 theorems):", "1024:theorems"),
        ("PAREN_COUNT", "Basic wrappers (12+ theorems):", "12+:theorems"),
        ("RELOCATION", "The ~12 foo wrappers now live in `X`.", "~12->X"),
    )

    def assert_form_charged_but_not_by(self, forms, mutant) -> None:
        """Require each form's key here, and require ``mutant`` not to produce it.

        Not "the mutant charges nothing": ``RELOCATION`` is charged on its anchor,
        so a mutant that cannot read the *count* still records the sentence --
        under a coarser key (``->X`` rather than ``60->X``).  What the canary
        pins is that the weakening loses the key, which is the fact the ratchet
        is computed from.
        """
        for kind, body, expected in forms:
            source = lean_source("M", header(body))
            self.assertEqual(tokens(source, kind), [expected], body)
            self.assertNotIn(
                expected, tokens(lean_source("M", header(body), mutant), kind, mutant), body
            )

    def test_a_lexicon_that_stops_at_fifty_lets_every_larger_count_through(self) -> None:
        """The bypass as shipped: cardinals above fifty charged nothing.

        Without this canary the extension is untested in the only direction that
        matters.  Every positive fixture in the suite uses a small number,
        because every claim in the corpus does, so narrowing the lexicon again
        would leave the whole suite green.
        """
        mutant = load_mutant(
            ('    "twenty": 20, "thirty": 30, "forty": 40, "fifty": 50, "sixty": 60,\n'
             '    "seventy": 70, "eighty": 80, "ninety": 90,\n',
             '    "twenty": 20, "thirty": 30, "forty": 40, "fifty": 50,\n'),
        )
        self.assert_form_charged_but_not_by(self.VOCABULARY_FORMS, mutant)

    def test_the_pre_fix_quantity_grammar_lets_every_numeric_idiom_through(self) -> None:
        """The same hole one step further out: a hedge, a comma or a `+` was free.

        The mutation restores the shipped grammar exactly -- a bare ``\\d+`` or
        cardinal, and a resolver with no fail-closed branch -- so the canary
        measures the published behaviour rather than a guess at it.
        """
        mutant = load_mutant(
            ('QUANTITY = rf"(?:{_HEDGE})?{_QUANTITY_CORE}\\+?"',
             'QUANTITY = rf"(?:\\d+|{_CARDINAL})"'),
            (
                '    parts = _QUANTITY_PARTS.match(word)\n'
                '    if parts is not None:\n'
                '        core = parts.group("core")\n'
                '        value = core.replace(",", "") if core[0].isdigit() '
                'else _cardinal_token(core)\n'
                '        if value is not None:\n'
                '            if parts.group("hedge"):\n'
                '                value = f"~{value}"\n'
                '            if parts.group("more"):\n'
                '                value = f"{value}+"\n'
                '            return value, True\n'
                '    if _NUMERIC_IDIOM.match(word):\n'
                '        return f"?{word}", True\n'
                '    return word, False\n',
                '    if word.isdigit():\n'
                '        return word, True\n'
                '    if word in WORD_NUMBERS:\n'
                '        return str(WORD_NUMBERS[word]), True\n'
                '    return word, False\n',
            ),
        )
        self.assert_form_charged_but_not_by(self.IDIOM_FORMS, mutant)

    #: The head shapes a single-token capture cannot reach, one per mechanism:
    #: a hedge in front of an unnormalizable count, a range, and a determiner in
    #: front of a bare numeral.
    HEAD_CAPTURE_FORMS = (
        ("NARROW_CHILD", "Narrow child module for about 12ish foo wrappers.", "?about 12ish"),
        ("NARROW_CHILD", "Narrow child module for between 10 and 12 foo wrappers.",
         "?between 10 and 12"),
        ("NARROW_CHILD", "Narrow child module for all 12 foo wrappers.", "12"),
    )

    def test_a_single_token_head_capture_loses_every_multi_word_quantity(self) -> None:
        """The shipped fallback took one word, so the fail-closed rule was unreachable.

        ``resolve_quantity("about 12ish")`` was correct in isolation and never
        saw that string: the head pattern handed it ``about``, which resolves to
        "not a quantity", and the record was filed as free.  The mutation
        restores the one-token capture and the determiner list that went with it.
        """
        mutant = load_mutant(
            (
                "    fragment = quantity_fragment(head)\n"
                "    if fragment:\n"
                "        return fragment\n",
                "",
            ),
            (
                '    rf"\\s*for\\s+{_DETERMINER_PREFIX}(?P<head>{_window(lazy=False)})",\n',
                '    rf"\\s*for\\s+(?:the\\s+)?(?P<head>\\S*)",\n',
            ),
        )
        for kind, body, expected in self.HEAD_CAPTURE_FORMS:
            source = lean_source("M", header(body))
            self.assertEqual(tokens(source, kind), [expected], body)
            self.assertNotEqual(
                tokens(lean_source("M", header(body), mutant), kind, mutant), [expected], body
            )

    def test_charging_a_relocation_only_when_a_count_parses_loses_647_claims(self) -> None:
        """R3.1 as a canary: the anchor is the claim, the count only sharpens it.

        The mutation restores the shipped rule -- no quantified subject, no
        charge -- and with it every ownership sentence whose count sits behind a
        long backticked list goes free again.
        """
        mutant = load_mutant(
            (
                '        return f"->{target}", True, "ownership claim, no quantified subject"',
                '        return "-", False, "no quantified subject"',
            )
        )
        forms = (
            ("RELOCATION", "The basic wrappers now live in `X`.", "->X"),
            ("RELOCATION", "Both wrappers now live in `X`.", "->X"),
            ("RELOCATION", "One wrapper now lives in `X`.", "->X"),
        )
        self.assert_form_charged_but_not_by(forms, mutant)

    #: Read one span and stop, as the destination pattern did.
    SINGLE_SPAN_DESTINATION = (
        "    while (tail := _WRAPPED_TAIL.match(flat, end)) is not None:\n",
        "    while False:\n",
    )

    def test_a_single_span_destination_truncates_a_wrapped_name(self) -> None:
        """The M2 defect, as a canary: the key names a namespace, not a module.

        And the laundering it permits, which the review reproduced: with the
        second half unpinned, rewriting it to name a completely different module
        leaves the pin byte-identical and every gate green.
        """
        mutant = load_mutant(self.SINGLE_SPAN_DESTINATION)
        rewritten = ShapeTest.WRAPPED_DESTINATION.replace(
            "`SusceptibilityPointwiseRegularityAtDifferentiableAt`",
            "`SomewhereCompletelyDifferentEntirely`",
        )
        truncated = "3->IsingModel.AmbientLattice.SpecialCases."
        for body in (ShapeTest.WRAPPED_DESTINATION, rewritten):
            self.assertEqual(
                tokens(lean_source("M", header(body), mutant), "RELOCATION", mutant),
                [truncated],
                "the mutant cannot tell the two destinations apart",
            )
        self.assertNotEqual(
            tokens(lean_source("M", header(ShapeTest.WRAPPED_DESTINATION)), "RELOCATION"),
            tokens(lean_source("M", header(rewritten)), "RELOCATION"),
        )

    #: Read the head clause at position 0 only, as every version before this one
    #: did.  The mutation removes the whole second question, so the canary is
    #: about the rule and not about one of its guards.
    HEAD_POSITION_ONLY = (
        "    governed = clause_quantities(head)\n",
        "    governed = ()\n",
    )

    def test_a_head_position_only_rule_frees_every_modified_count(self) -> None:
        """The R3.1 violation, as a canary: not a coarse key, no key at all.

        With the second question removed, ``for the following 17 wrappers`` is
        telemetry -- reported apart from the ledger, never pinned, never
        compared -- so a reviewer has nothing to look at either.
        """
        mutant = load_mutant(self.HEAD_POSITION_ONLY)
        for body, expected in ShapeTest.MODIFIED_HEADS:
            source = lean_source("M", header(body))
            self.assertEqual(tokens(source, "NARROW_CHILD"), [expected], body)
            mutated = lean_source("M", header(body), mutant)
            self.assertEqual(tokens(mutated, "NARROW_CHILD", mutant), [], body)
            self.assertEqual(
                [claim.token for claim in telemetry(mutated, mutant)], ["-"], body
            )

    #: Read a code span as prose, as a whole-clause scan without `blank_code`
    #: would.  Measured on this tree it charges four Lean expressions as counts.
    CODE_IS_PROSE = (
        "    text = blank_code(clause)\n",
        "    text = clause\n",
    )

    def test_without_blanking_code_a_lean_expression_reads_as_a_count(self) -> None:
        """Anti-vacuity for `blank_code`: the false charges it keeps out are real.

        Both bodies are live headers: `MayerTrivialCases.lean` and
        `MayerRecurrenceHasSum.lean`, in the ambient and the concrete copy each.
        """
        mutant = load_mutant(self.CODE_IS_PROSE)
        for body, expected in (
            ("Narrow child module for the `mayerPartialSum 0 ≤ f` comparison wrappers.", "?0"),
            ("Narrow child module for the `vdPolymerFamilies_sum - 1` tendsto-zero wrapper.",
             "?1"),
        ):
            source = lean_source("M", header(body))
            self.assertEqual(tokens(source, "NARROW_CHILD"), [], body)
            self.assertEqual(
                tokens(lean_source("M", header(body), mutant), "NARROW_CHILD", mutant),
                [expected],
                body,
            )

    #: Flatten a blank line to a space, as every version before this one did.
    PARAGRAPH_BLIND = (
        '            chars.append(PARAGRAPH if run.group(0).count("\\n") > 1 else " ")\n',
        '            chars.append(" ")\n',
    )

    def test_a_flattener_blind_to_paragraphs_borrows_a_count(self) -> None:
        """The two live misattributions, as a canary.

        With a blank line indistinguishable from a line wrap, the relocation of
        *one* wrapper is keyed by the count of the paragraph above it -- a number
        the sentence does not state, baked into the pin, on two real modules.
        """
        mutant = load_mutant(self.PARAGRAPH_BLIND)
        source = lean_source("M", header(ShapeTest.PARAGRAPH_CROSSING))
        self.assertEqual(tokens(source, "RELOCATION"), ["->IsingModel.Other.Susceptibility"])
        self.assertEqual(
            tokens(lean_source("M", header(ShapeTest.PARAGRAPH_CROSSING), mutant),
                   "RELOCATION", mutant),
            ["2->IsingModel.Other.Susceptibility"],
        )

    NESTING_MUTATION = (
        "            if token == \"/-\":\n                depth += 1\n",
        "            if token == \"/-\":\n                pass\n",
    )

    def test_a_non_nesting_comment_scanner_misplaces_a_claim(self) -> None:
        """Nesting decides which side of the mask a claim is on.

        The mutant closes the outer comment at the inner ``-/``, so the claim
        moves out of prose and is charged as ``NON_PROSE`` -- a different key, so
        the gate still fails.  Note what does **not** happen: ``K2`` stays green,
        because both of its sides come from the same (wrong) region set.  ``K3``
        is the law that contradicts this mutation; see the canary below.
        """
        mutant = load_mutant(self.NESTING_MUTATION)
        text = "/-!\n# F\n-/\n/- outer /- inner -/ Narrow child module for the 5 foo wrappers. -/\n"
        self.assertEqual(tokens(lean_source("M", text), "NARROW_CHILD"), ["5"])
        scanned = mutant.scan_source(lean_source("M", text, mutant))
        self.assertIn(mutant.NON_PROSE, [claim.kind for claim in scanned.claims])
        self.assertFalse(
            [failure for failure in scanned.conservation if failure.startswith("K2")],
            "K2 cannot see a decomposition error; claiming it can would be false assurance",
        )

    def test_the_independent_oracle_contradicts_a_nesting_bug(self) -> None:
        """K3's reason to exist: it is the only law that shares no code with the scanner."""
        mutant = load_mutant(self.NESTING_MUTATION)
        text = "/-!\n# F\n-/\n/- outer /- inner -/ Narrow child module for the 5 foo wrappers. -/\n"
        self.assertEqual(ratchet.scan_source(lean_source("M", text)).conservation, ())
        failures = mutant.scan_source(lean_source("M", text, mutant)).conservation
        self.assertTrue(any(failure.startswith("K3") for failure in failures), failures)

    def test_dropping_the_oracle_hides_the_nesting_bug(self) -> None:
        """Proves K3 is load-bearing: without it the same mutant reports a sound run."""
        mutant = load_mutant(
            self.NESTING_MUTATION,
            ("    if source.is_lean and decomposition.regions != reference_regions(text):",
             "    if False:"),
        )
        text = "/-!\n# F\n-/\n/- outer /- inner -/ Narrow child module for the 5 foo wrappers. -/\n"
        self.assertEqual(mutant.scan_source(lean_source("M", text, mutant)).conservation, ())

    def test_a_substring_module_doc_marker_would_exonerate_the_module(self) -> None:
        """The `/-!` charge must come from syntax position, not from a substring.

        ``def marker : String := "/-!"`` and ``-- /-!`` both contain the three
        characters and neither is a module docstring, so a substring test lets a
        module delete its header and keep the exemption -- in the one class that
        exists to stop exactly that evasion.
        """
        mutant = load_mutant(
            ("    if source.is_lean and not decomposition.module_doc:",
             "    if source.is_lean and _MODULE_DOC not in text:"),
        )
        for body in ('def marker : String := "/-!"\n', "-- /-!\n"):
            text = f"import IsingModel.Basic\n\n{body}{TRIVIAL}"
            self.assertEqual(
                [c.kind for c in charged(lean_source("M", text))], [ratchet.MISSING_DOC], body
            )
            self.assertEqual(charged(lean_source("M", text, mutant), mutant), [], body)

    def test_a_scalar_ratchet_lets_one_fix_pay_for_one_regression(self) -> None:
        """The offsetting the multiset key forbids, demonstrated on a mutant."""
        mutant = load_mutant(
            (
                "    new = tuple(sorted((key, count) for key, count in live.items()",
                "    if sum(live.values()) <= sum(baseline.values()):\n"
                "        return Comparison(new=(), grown=(), slack=())\n"
                "    new = tuple(sorted((key, count) for key, count in live.items()",
            )
        )
        base = population((KEY_A, 1))
        live = population((KEY_B, 1))
        self.assertTrue(ratchet.compare(live, base).regressed)
        self.assertFalse(mutant.compare(live, base).regressed)

    def test_dropping_the_missing_header_charge_hides_an_uninspectable_module(self) -> None:
        """"Charged, not skipped" is a rule, so removing it has to be visible."""
        mutant = load_mutant(
            ("    if source.is_lean and not decomposition.module_doc:", "    if False:"),
        )
        text = "import IsingModel.Basic\n\ntheorem f : True := trivial\n"
        self.assertEqual(len(charged(lean_source("M", text))), 1)
        self.assertEqual(len(charged(lean_source("M", text, mutant), mutant)), 0)

    def test_narrowing_the_scan_scope_drops_live_claims(self) -> None:
        """The boundary is a decision, so shrinking it back has to be visible.

        ``IsingModel.lean`` and four ``docs/`` pages were outside the scan while
        one of them, ``docs/architecture-import-layers.md``, was already carrying
        a claim of a charged class.
        """
        mutant = load_mutant(
            ('SCAN_ROOTS: tuple[str, ...] = ("IsingModel.lean", "IsingModel", "README.md", '
             '"docs", "tex")',
             'SCAN_ROOTS: tuple[str, ...] = ("IsingModel",)'),
        )
        wide = set(ratchet.tracked_paths(REPO_ROOT))
        narrow = set(mutant.tracked_paths(REPO_ROOT))
        self.assertLess(narrow, wide)
        self.assertIn("IsingModel.lean", wide - narrow)
        self.assertIn("docs/architecture-import-layers.md", wide - narrow)

    def test_a_filesystem_walk_would_read_untracked_files(self) -> None:
        """The tracked set is the source of truth; a walk is not an equivalent.

        Written against a throwaway repository rather than against ``IsingModel/``
        so it states a property of the *query*, not of today's working tree.
        """
        with tempfile.TemporaryDirectory(prefix="claim-ratchet-") as tmp:
            root = Path(tmp)
            (root / "IsingModel").mkdir()
            (root / "IsingModel" / "Tracked.lean").write_text(
                header("Narrow child module for the 3 foo wrappers."), encoding="utf-8"
            )
            subprocess.run(["git", "-C", tmp, "init", "-q"], check=True)
            subprocess.run(["git", "-C", tmp, "add", "IsingModel/Tracked.lean"], check=True)
            (root / "IsingModel" / "Untracked.lean").write_text(
                header("Narrow child module for the 99 foo wrappers."), encoding="utf-8"
            )
            self.assertEqual(ratchet.tracked_paths(root), ("IsingModel/Tracked.lean",))
            walked = sorted(str(p.relative_to(root)) for p in root.rglob("*.lean"))
            self.assertEqual(len(walked), 2)


# --------------------------------------------------------------------------
# End-to-end, on a throwaway repository
# --------------------------------------------------------------------------


class ScratchRepoTest(unittest.TestCase):
    """Inject a claim into a scratch copy and require the ratchet to name it."""

    def setUp(self) -> None:
        self.tmp = tempfile.mkdtemp(prefix="claim-ratchet-repo-")
        self.addCleanup(shutil.rmtree, self.tmp, True)
        self.root = Path(self.tmp)
        (self.root / "IsingModel").mkdir()
        self.write("IsingModel/One.lean", header("Narrow child module for the 12 foo wrappers."))
        self.write("IsingModel/Two.lean", header("Provides the ambient monotonicity API."))
        subprocess.run(["git", "-C", self.tmp, "init", "-q"], check=True)
        subprocess.run(["git", "-C", self.tmp, "add", "-A"], check=True)
        self.baseline = self.root / "baseline.tsv"

    def write(self, relative: str, text: str) -> None:
        """Write ``text`` at ``relative`` inside the scratch repository."""
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    def pin(self) -> Counter:
        """Pin the current population as the scratch repository's baseline."""
        report = ratchet.build_report(root=self.root)
        self.baseline.write_text(ratchet.format_baseline(report.charged), encoding="utf-8")
        parsed, errors = ratchet.read_baseline(self.baseline)
        self.assertEqual(errors, [])
        return parsed

    def verdict(self, baseline: Counter) -> tuple[bool, str]:
        """Return ``(passes, printed report)`` for the scratch repository."""
        report = ratchet.build_report(root=self.root)
        buffer = io.StringIO()
        with contextlib.redirect_stdout(buffer):
            ok = ratchet.print_report(report, baseline, [])
        return ok, buffer.getvalue()

    def test_nothing_injected_passes_against_its_own_baseline(self) -> None:
        """The control arm: a pinned tree is green, and says so honestly."""
        baseline = self.pin()
        self.assertEqual(sum(baseline.values()), 1)
        ok, output = self.verdict(baseline)
        self.assertTrue(ok, output)
        self.assertIn("PASS: no recognized inventory claim was added", output)

    def test_an_injected_claim_is_named(self) -> None:
        """The canary arm: a new claim in a previously clean module fails the gate."""
        baseline = self.pin()
        self.write("IsingModel/Two.lean", header("Narrow child module for the 7 bar wrappers."))
        ok, output = self.verdict(baseline)
        self.assertFalse(ok, output)
        self.assertIn("NARROW_CHILD IsingModel/Two.lean 7", output)

    def test_an_injected_duplicate_of_a_baselined_claim_is_named(self) -> None:
        """Growth of an existing key fails too, so a key cannot absorb a second claim."""
        baseline = self.pin()
        self.write(
            "IsingModel/One.lean",
            header("Narrow child module for the 12 foo wrappers.\n\n"
                   "Narrow child module for the 12 baz wrappers."),
        )
        ok, output = self.verdict(baseline)
        self.assertFalse(ok, output)
        self.assertIn("claim count grew 1 -> 2", output)

    def test_repairing_a_claim_passes_without_a_baseline_edit(self) -> None:
        """The direction the campaign moves in must never need a test or pin change."""
        baseline = self.pin()
        self.write("IsingModel/One.lean", header("Provides the foo API."))
        ok, output = self.verdict(baseline)
        self.assertTrue(ok, output)
        self.assertIn("below their pin", output)

    def test_deleting_the_whole_header_does_not_pay_for_the_claim(self) -> None:
        """The cheapest evasion -- delete the docstring -- is itself charged."""
        baseline = self.pin()
        self.write("IsingModel/One.lean", f"import IsingModel.Basic\n\n{TRIVIAL}")
        ok, output = self.verdict(baseline)
        self.assertFalse(ok, output)
        self.assertIn(ratchet.MISSING_DOC, output)


# --------------------------------------------------------------------------
# K4: the ledger key identifies exactly one file
# --------------------------------------------------------------------------

#: The keying as it was before ``K4``: a dotted module name derived from the
#: path.  Written as a mutation of the shipped detector, so the collision below
#: is demonstrated on the real code rather than on a stand-in.
DOTTED_TARGET = (
    "            Source(target=path, path=path, text=text, is_lean=path.endswith(\".lean\"))\n",
    "            Source(target=display_name(path), path=path, text=text,\n"
    "                   is_lean=path.endswith(\".lean\"))\n",
)

#: The review's collision, verbatim: two distinct tracked paths whose dotted
#: module names are the same string.  Lean accepts both -- a file name may carry
#: a dot -- so this is a property of the *keying*, not of today's corpus, and no
#: assertion over ``IsingModel/`` could ever have caught it.
COLLIDING: tuple[str, ...] = (
    "IsingModel/AmbientLattice/Analyticity.lean",
    "IsingModel/AmbientLattice.Analyticity.lean",
)


class KeyIdentityTest(unittest.TestCase):
    """``K4``, on inputs constructed for it rather than on the live tree.

    ``K0``-``K3`` prove that a record exists for every input.  None of them
    proves that its *key* is unique, and the difference was a working laundering
    channel: reword the pinned claim in one of the two files above into a shape
    the grammar does not recognize, write the same sentence into the other, and
    the pin comes out byte-identical with ``--check`` and the drift check both
    green.  One file's vacated capacity paid for the other's new claim.
    """

    CLAIM = "The 4 boundary wrappers now live in `IsingModel.Other`."

    def setUp(self) -> None:
        self.tmp = tempfile.mkdtemp(prefix="claim-ratchet-key-")
        self.addCleanup(shutil.rmtree, self.tmp, True)
        self.root = Path(self.tmp)
        for path in COLLIDING:
            full = self.root / path
            full.parent.mkdir(parents=True, exist_ok=True)
            full.write_text(header(self.CLAIM), encoding="utf-8")

    def population(self, module=ratchet) -> tuple[Counter, tuple[str, ...]]:
        """Return ``(charged population, K-failures)`` for the colliding pair."""
        report = module.build_report(root=self.root, paths=COLLIDING)
        return report.charged, report.conservation

    def test_two_files_that_share_a_dotted_name_are_two_ledger_rows(self) -> None:
        """The fix: the key is the path, so the two claims cost two charges."""
        charged, failures = self.population()
        self.assertEqual(failures, ())
        self.assertEqual(sorted(key[1] for key in charged), sorted(COLLIDING))
        self.assertEqual(sum(charged.values()), 2)

    def test_the_dotted_keying_collapses_them_and_k4_says_so(self) -> None:
        """Anti-vacuity: with the old keying the exploit is back, and ``K4`` fires."""
        mutant = load_mutant(DOTTED_TARGET)
        charged, failures = self.population(mutant)
        self.assertEqual(len(charged), 1, "the pin cannot tell the two files apart")
        self.assertEqual(sum(charged.values()), 2, "two claims, one key")
        self.assertTrue(any(failure.startswith("K4") for failure in failures), failures)
        self.assertTrue(any("share one ledger key" in failure for failure in failures), failures)
        self.assertTrue(any("does not invert" in failure for failure in failures), failures)

    def test_a_key_that_does_not_name_its_file_is_a_k4_failure(self) -> None:
        """The other half of the law, stated on one constructed source."""
        lossy = ratchet.Source(
            target="IsingModel.A", path="IsingModel/A.lean", text="", is_lean=True
        )
        self.assertTrue(
            any("does not invert" in failure for failure in ratchet.key_failures([lossy]))
        )
        self.assertEqual(ratchet.key_failures([lean_source("IsingModel.A", "")]), [])

    def test_the_display_name_is_still_available_beside_the_key(self) -> None:
        """A dotted name a Lean reader can read, as a column and never as an identity."""
        self.assertEqual(
            ratchet.display_name("IsingModel/AmbientLattice/Analyticity.lean"),
            "IsingModel.AmbientLattice.Analyticity",
        )
        self.assertEqual(ratchet.display_name("docs/index.md"), "docs/index.md")
        report = ratchet.build_report(root=self.root, paths=COLLIDING)
        findings = ratchet.format_findings(report)
        self.assertIn("class\ttarget\tmodule\ttoken\tline\tnote", findings)
        for path in COLLIDING:
            self.assertIn(f"{path}\tIsingModel.AmbientLattice.Analyticity\t", findings)


# --------------------------------------------------------------------------
# Anti-vacuity, on fixtures rather than on the tree
# --------------------------------------------------------------------------

#: One fixture per charge class, charged.  These are what prove the detector is
#: alive, and they keep proving it after the last real claim is repaired -- which
#: is why the anti-vacuity assertions live here and not on ``IsingModel/``.
FIXTURES: tuple[tuple[str, str], ...] = (
    ("NARROW_CHILD", header("Narrow child module for the 12 foo wrappers.")),
    ("PAREN_COUNT", header("Basic wrappers (13 theorems):")),
    ("POSSESSIVE_COUNT", header("Defines `x` and its 4 properties.")),
    ("PREDICATE_COUNT", header("Its entry-point package contains ten wrappers.")),
    ("RELOCATION", header("The 13 bridge wrappers now live in `IsingModel.Other`.")),
    (ratchet.MISSING_DOC, f"import IsingModel.Basic\n\n{TRIVIAL}"),
    (ratchet.UNTERMINATED, "/-! # F\n\nNarrow child module for the 3 foo wrappers.\n"),
    (
        ratchet.NON_PROSE,
        '/-!\n# F\n-/\n\ndef s : String := "Narrow child module for the 3 foo wrappers"\n',
    ),
)


class DetectorAliveTest(unittest.TestCase):
    """Every charge class fires on a fixture, whatever the live tree looks like."""

    def test_every_charge_class_is_exercised(self) -> None:
        for kind, text in FIXTURES:
            self.assertIn(
                kind, [claim.kind for claim in charged(lean_source("M", text))], kind
            )

    def test_the_fixture_set_covers_every_class_the_checker_defines(self) -> None:
        """So that adding a class without a fixture cannot pass unnoticed."""
        self.assertEqual(
            {kind for kind, _text in FIXTURES},
            {claim_class.name for claim_class in ratchet.CLAIM_CLASSES}
            | {ratchet.MISSING_DOC, ratchet.UNTERMINATED, ratchet.NON_PROSE},
        )

    def test_an_unterminated_string_literal_is_charged(self) -> None:
        """The scan cannot know the file's structure after an unclosed quote."""
        text = '/-!\n# F\n-/\n\ndef s : String := "never closed\n'
        self.assertIn(
            ratchet.UNTERMINATED, [claim.kind for claim in charged(lean_source("M", text))]
        )


# --------------------------------------------------------------------------
# Baseline drift against the base branch
# --------------------------------------------------------------------------


#: The detector as it was before ``NARROW_CHILD``'s anchor gained
#: ``re.IGNORECASE`` -- the one real detector migration on this project's record,
#: and the shape the escape hatch exists for.  A scratch repository whose base
#: commit carries *this* detector and whose head carries the shipped one
#: reproduces that migration end to end, so the hatch is tested against a real
#: recount rather than against a stand-in file that was edited.
NARROWED_ANCHOR = (
    '_NARROW_CHILD_ANCHOR = re.compile(r"Narrow child module", re.IGNORECASE)',
    '_NARROW_CHILD_ANCHOR = re.compile(r"Narrow child module")',
)


def narrowed_detector() -> str:
    """Return the checker's source with the case-insensitive anchor removed."""
    text = source_text()
    if NARROWED_ANCHOR[0] not in text:
        raise AssertionError("mutation target absent, the migration fixture would be vacuous")
    return text.replace(*NARROWED_ANCHOR, 1)


def load_source(text: str) -> types.ModuleType:
    """Return ``text`` executed as a module (used for the base-commit detector)."""
    module = types.ModuleType("header_inventory_claim_ratchet_fixture")
    module.__file__ = str(SCRIPT_FILE)
    exec(compile(text, str(SCRIPT_FILE), "exec"), module.__dict__)  # noqa: S102
    return module


class DriftTest(unittest.TestCase):
    """B1/B2/B3, on a throwaway repository with a real base commit.

    Hermetic by construction: the scratch repository has its own ``main``, so the
    test states a property of the comparison rather than of today's fork point.
    It carries a real copy of the detector rather than a stand-in file, because
    the migration hatch now asks what the detector's *logic* does and re-runs the
    base commit's copy of it.
    """

    def setUp(self) -> None:
        self.tmp = tempfile.mkdtemp(prefix="claim-ratchet-drift-")
        self.addCleanup(shutil.rmtree, self.tmp, True)
        self.root = Path(self.tmp)
        (self.root / "IsingModel").mkdir()
        (self.root / "scripts" / "audit").mkdir(parents=True)
        self.write("IsingModel/One.lean", header("Narrow child module for the 12 foo wrappers."))
        self.write("IsingModel/Two.lean", header("Narrow child module for the 7 bar wrappers."))
        self.write(ratchet.DETECTOR_REPO_PATH, source_text())
        self.git("init", "-q", "-b", "main")
        self.git("config", "user.email", "t@example.com")
        self.git("config", "user.name", "t")
        # Tracked first: the pin is computed from `git ls-files`, so a scratch
        # repository pinned before its first `add` records an empty population
        # and every assertion below would be vacuous.
        self.git("add", "-A")
        self.repin()
        self.git("add", "-A")
        self.git("commit", "-q", "-m", "base")

    def git(self, *args: str) -> None:
        """Run ``git`` in the scratch repository."""
        subprocess.run(["git", "-C", self.tmp, *args], check=True, capture_output=True)

    def write(self, relative: str, text: str) -> None:
        """Write ``text`` at ``relative`` inside the scratch repository."""
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    def repin(self, module=ratchet) -> None:
        """Regenerate the scratch repository's baseline from its own tree."""
        report = module.build_report(root=self.root)
        self.write(ratchet.BASELINE_REPO_PATH, module.format_baseline(report.charged))

    def declare_migration(self, reason: str = "anchor widened, recounted") -> None:
        """Add the migration trailer to the head checkout's pin."""
        path = self.root / ratchet.BASELINE_REPO_PATH
        path.write_text(
            f"{ratchet.MIGRATION_MARKER} {reason}\n" + path.read_text(encoding="utf-8"),
            encoding="utf-8",
        )

    def drift(self) -> ratchet.Drift | None:
        """Return the drift verdict of the scratch repository against its own main."""
        return ratchet.check_drift(root=self.root, base_ref="main")

    def test_an_untouched_checkout_has_no_drift(self) -> None:
        """The control arm."""
        drift = self.drift()
        self.assertTrue(drift.ok, drift)
        self.assertTrue(drift.had_baseline)

    def test_a_real_repair_that_is_re_pinned_passes(self) -> None:
        """The direction the campaign moves in: prose edited, pin regenerated."""
        self.write("IsingModel/One.lean", header("Provides the foo API."))
        self.repin()
        drift = self.drift()
        self.assertTrue(drift.ok, drift)

    def test_a_net_zero_swap_fails(self) -> None:
        """B1, and the whole reason this check exists.

        Repair one claim, write another, regenerate the pin: the total is
        unchanged, the live tree agrees with its own baseline, and every
        same-checkout check passes.  Only the base branch's file knows.
        """
        self.write("IsingModel/One.lean", header("Narrow child module for the 99 foo wrappers."))
        self.repin()
        drift = self.drift()
        self.assertFalse(drift.ok, drift)
        self.assertEqual([key for key, _now, _was in drift.added],
                         [("NARROW_CHILD", "IsingModel/One.lean", "99")])

    def drop_a_baseline_row(self) -> tuple[str, str, str]:
        """Delete one row from the pin without repairing the claim it records."""
        key = ("NARROW_CHILD", "IsingModel/Two.lean", "7")
        baseline, _errors = ratchet.read_baseline(self.root / ratchet.BASELINE_REPO_PATH)
        del baseline[key]
        self.write(ratchet.BASELINE_REPO_PATH, ratchet.format_baseline(baseline))
        return key

    def test_deleting_a_baseline_row_without_touching_its_source_fails(self) -> None:
        """B2: the pin is not a text file that may be edited downward for free."""
        key = self.drop_a_baseline_row()
        drift = self.drift()
        self.assertFalse(drift.ok, drift)
        self.assertEqual([k for k, _now, _was in drift.unexplained], [key])

    def test_touching_the_file_does_not_buy_a_deleted_baseline_row(self) -> None:
        """B2 attributes per file, and B3 is why that is enough.

        Adding a blank line to the module would satisfy the "this diff edits the
        source" test on its own.  It does not help: the claim is still written,
        so the pin is no longer an exact function of the tree and B3 rejects it.
        """
        key = self.drop_a_baseline_row()
        self.write(
            "IsingModel/Two.lean",
            header("Narrow child module for the 7 bar wrappers.") + "\n-- unrelated\n",
        )
        drift = self.drift()
        self.assertEqual(drift.unexplained, (), "the file edit does satisfy B2")
        self.assertEqual(drift.untight, (key,))
        self.assertFalse(drift.ok, drift)

    def test_slack_in_the_pin_fails(self) -> None:
        """B3: an un-pinned repair leaves room for a later claim to be written into."""
        self.write("IsingModel/One.lean", header("Provides the foo API."))
        drift = self.drift()
        self.assertFalse(drift.ok, drift)
        self.assertEqual(drift.untight, (("NARROW_CHILD", "IsingModel/One.lean", "12"),))

    def test_a_declaration_plus_a_comment_only_detector_edit_buys_nothing(self) -> None:
        """The measured exploit, as a permanent arm.

        Write two new claims, re-pin, append one comment line to the detector,
        add the marker: the hatch as first written waived every ``B1``/``B2``
        failure in the run and printed ``PASS``.  A comment is not logic, so
        there is no allowance and the two new keys are still rises.
        """
        self.write("IsingModel/One.lean", header("Narrow child module for the 99 foo wrappers."))
        self.write("IsingModel/Two.lean", header("Narrow child module for the 42 bar wrappers."))
        self.repin()
        self.declare_migration("recount under the corrected detector")
        self.write(ratchet.DETECTOR_REPO_PATH, source_text() + "\n# cosmetic\n")
        drift = self.drift()
        self.assertFalse(drift.ok, drift)
        self.assertEqual(
            [key for key, _now, _was in drift.added],
            [("NARROW_CHILD", "IsingModel/One.lean", "99"),
             ("NARROW_CHILD", "IsingModel/Two.lean", "42")],
        )
        self.assertTrue(
            any("logic is unchanged" in note for note in drift.migration), drift.migration
        )

    def test_a_declaration_alone_buys_nothing(self) -> None:
        """No detector edit at all: the marker is a sentence, not a permission."""
        self.write("IsingModel/One.lean", header("Narrow child module for the 99 foo wrappers."))
        self.repin()
        self.declare_migration()
        self.assertFalse(self.drift().ok)

    def test_a_repair_that_renames_its_module_is_not_rejected(self) -> None:
        """B2 must see the old path of a ``git mv``, or it rejects real repairs.

        ``git diff --name-only`` prints a rename as its destination alone, so the
        deleted claim looked like a baseline row dropped with no edit to the file
        that owned it -- in a repository whose dominant workflow is exactly module
        splits and renames.
        """
        self.git("mv", "IsingModel/One.lean", "IsingModel/OneCore.lean")
        self.write("IsingModel/OneCore.lean", header("Provides the foo API."))
        self.repin()
        drift = self.drift()
        self.assertEqual(drift.unexplained, (), drift)
        self.assertTrue(drift.ok, drift)

    def test_a_rename_that_carries_its_claim_still_fails(self) -> None:
        """The other half of the rename story, and it is not a defect.

        A count keyed to a module name is a claim about *that* module, so moving
        it to a new name is writing it there.  The repair is to drop the count
        while moving the file, which is what the campaign is for.
        """
        self.git("mv", "IsingModel/One.lean", "IsingModel/OneCore.lean")
        self.repin()
        drift = self.drift()
        self.assertFalse(drift.ok, drift)
        self.assertEqual([key for key, _now, _was in drift.added],
                         [("NARROW_CHILD", "IsingModel/OneCore.lean", "12")])

    def test_a_broken_run_suppresses_the_comparison(self) -> None:
        """The drift mode used to report ``PASS`` on a tree ``--check`` was failing.

        Its conservation laws are the same laws, and a mode that ignores them is
        a fail-open path guarded only by the order of the CI steps.
        """
        original = ratchet.build_report
        ratchet.build_report = lambda *a, **k: ratchet.Report(
            sources=(), claims=(), telemetry=(),
            conservation=("K3 IsingModel.One: synthetic",),
        )
        try:
            drift = self.drift()
        finally:
            ratchet.build_report = original
        self.assertFalse(drift.ok, drift)
        self.assertEqual(drift.unsound, ("K3 IsingModel.One: synthetic",))
        buffer = io.StringIO()
        with contextlib.redirect_stdout(buffer):
            ok = ratchet.print_drift(drift, "main")
        self.assertFalse(ok)
        self.assertIn("suppressed", buffer.getvalue())
        self.assertNotIn("PASS", buffer.getvalue())

    def test_a_malformed_pin_suppresses_the_comparison(self) -> None:
        """A pin that cannot be parsed is not a pin the comparison may believe."""
        path = self.root / ratchet.BASELINE_REPO_PATH
        path.write_text(path.read_text(encoding="utf-8") + "NARROW_CHILD\tIsingModel/One.lean\n",
                        encoding="utf-8")
        drift = self.drift()
        self.assertFalse(drift.ok, drift)
        self.assertTrue(drift.baseline_errors, drift)

    def test_an_unresolvable_base_ref_fails_closed(self) -> None:
        """A drift check that cannot find its base must never report a pass."""
        self.assertIsNone(ratchet.check_drift(root=self.root, base_ref="origin/nope"))
        buffer = io.StringIO()
        with contextlib.redirect_stdout(buffer):
            ok = ratchet.print_drift(None, "origin/nope")
        self.assertFalse(ok)
        self.assertIn("does not resolve", buffer.getvalue())


class MigrationHatchTest(unittest.TestCase):
    """The one legitimate movement no prose edit explains, and its exact bounds.

    The scratch repository's base commit carries the detector as it was *before*
    ``NARROW_CHILD``'s anchor gained ``re.IGNORECASE``, and its tree carries a
    lowercase claim that only the widened detector can see -- this project's one
    real migration (713 -> 740), reproduced end to end.  What the hatch grants is
    then measured against a recount rather than against the declaration.
    """

    def setUp(self) -> None:
        self.tmp = tempfile.mkdtemp(prefix="claim-ratchet-migration-")
        self.addCleanup(shutil.rmtree, self.tmp, True)
        self.root = Path(self.tmp)
        (self.root / "IsingModel").mkdir()
        (self.root / "scripts" / "audit").mkdir(parents=True)
        self.write("IsingModel/One.lean", header("Narrow child module for the 12 foo wrappers."))
        # Lowercase: invisible to the base commit's detector, visible to this one.
        self.write("IsingModel/Two.lean", header("narrow child module for the 5 bar wrappers."))
        self.write(ratchet.DETECTOR_REPO_PATH, narrowed_detector())
        self.git("init", "-q", "-b", "main")
        self.git("config", "user.email", "t@example.com")
        self.git("config", "user.name", "t")
        self.git("add", "-A")
        narrowed = load_source(narrowed_detector())
        pin = narrowed.build_report(root=self.root).charged
        self.assertEqual(sum(pin.values()), 1, "the narrowed detector must miss the lowercase one")
        self.write(ratchet.BASELINE_REPO_PATH, narrowed.format_baseline(pin))
        self.git("add", "-A")
        self.git("commit", "-q", "-m", "base")

    def git(self, *args: str) -> None:
        """Run ``git`` in the scratch repository."""
        subprocess.run(["git", "-C", self.tmp, *args], check=True, capture_output=True)

    def write(self, relative: str, text: str) -> None:
        """Write ``text`` at ``relative`` inside the scratch repository."""
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    def migrate(self) -> None:
        """Land the widened detector and re-pin under it."""
        self.write(ratchet.DETECTOR_REPO_PATH, source_text())
        report = ratchet.build_report(root=self.root)
        self.write(ratchet.BASELINE_REPO_PATH, ratchet.format_baseline(report.charged))

    def declare(self, line: str) -> None:
        """Prepend ``line`` to the head checkout's pin."""
        path = self.root / ratchet.BASELINE_REPO_PATH
        path.write_text(line + "\n" + path.read_text(encoding="utf-8"), encoding="utf-8")

    def drift(self) -> ratchet.Drift | None:
        """Return the drift verdict of the scratch repository against its own main."""
        return ratchet.check_drift(root=self.root, base_ref="main")

    def test_a_recount_the_detector_change_explains_is_allowed(self) -> None:
        """The 713 -> 740 shape: prose untouched, the pin rises, and that is honest."""
        self.migrate()
        self.assertFalse(self.drift().ok, "a recount still has to be declared")
        self.declare(f"{ratchet.MIGRATION_MARKER} anchor widened to ignore case, recounted")
        drift = self.drift()
        self.assertTrue(drift.ok, drift)
        self.assertTrue(any("allowance" in note for note in drift.migration), drift.migration)

    def test_a_new_claim_written_alongside_a_real_migration_still_fails(self) -> None:
        """The allowance is per key and is measured on the base commit's own tree.

        A claim this diff writes is not in that tree, so it earns nothing and is
        a ``B1`` failure however loudly the migration is declared -- which is the
        property neither the total waiver nor the head-tree recount had.
        """
        self.write("IsingModel/One.lean", header("Narrow child module for the 99 foo wrappers."))
        self.migrate()
        self.declare(f"{ratchet.MIGRATION_MARKER} anchor widened to ignore case, recounted")
        drift = self.drift()
        self.assertFalse(drift.ok, drift)
        self.assertEqual([key for key, _now, _was in drift.added],
                         [("NARROW_CHILD", "IsingModel/One.lean", "99")])
        self.assertTrue(any("allowance" in note for note in drift.migration), drift.migration)

    def test_the_declaration_must_be_a_whole_line_of_its_own(self) -> None:
        """Near misses, one of which -- the embedded marker -- used to be enough."""
        self.migrate()
        path = self.root / ratchet.BASELINE_REPO_PATH
        pinned = path.read_text(encoding="utf-8")
        for line in (
            f"  {ratchet.MIGRATION_MARKER} indented, so not a trailer of its own",
            f"# see {ratchet.MIGRATION_MARKER} elsewhere for why",
            ratchet.MIGRATION_MARKER,
            f"{ratchet.MIGRATION_MARKER} ",
            f"{ratchet.MIGRATION_MARKER}no space, no reason",
        ):
            self.declare(line)
            self.assertEqual(ratchet.migration_declarations(self.root, "main"), (), line)
            self.assertFalse(self.drift().ok, line)
            path.write_text(pinned, encoding="utf-8")
        self.declare(f"{ratchet.MIGRATION_MARKER} anchor widened to ignore case, recounted")
        self.assertEqual(
            ratchet.migration_declarations(self.root, "main"),
            ("anchor widened to ignore case, recounted",),
            "anti-vacuity: the well-formed trailer is recognized",
        )

    def test_a_marker_already_on_the_base_branch_is_not_a_declaration(self) -> None:
        """The hatch lives in the diff, so it can never become a standing permission."""
        declaration = f"{ratchet.MIGRATION_MARKER} anchor widened to ignore case, recounted"
        self.declare(declaration)
        self.git("add", "-A")
        self.git("commit", "-q", "-m", "declare on the base branch")
        self.migrate()
        self.declare(declaration)
        self.assertEqual(ratchet.migration_declarations(self.root, "main"), ())
        self.assertFalse(self.drift().ok)

    def test_a_migration_never_waives_b2_or_b3(self) -> None:
        """Only B1 is relaxed: a detector edit may not delete a row or leave slack."""
        self.migrate()
        self.declare(f"{ratchet.MIGRATION_MARKER} anchor widened to ignore case, recounted")
        pin = self.root / ratchet.BASELINE_REPO_PATH
        tight = pin.read_text(encoding="utf-8")
        pin.write_text(
            "\n".join(
                line for line in tight.splitlines()
                if not line.startswith("NARROW_CHILD\tIsingModel/One.lean")
            ) + "\n",
            encoding="utf-8",
        )
        drift = self.drift()
        self.assertFalse(drift.ok, drift)
        self.assertEqual([key for key, _now, _was in drift.unexplained],
                         [("NARROW_CHILD", "IsingModel/One.lean", "12")])
        self.assertEqual(drift.untight, (("NARROW_CHILD", "IsingModel/One.lean", "12"),))

    def test_the_recount_is_both_detectors_on_the_base_commit_s_tree(self) -> None:
        """Anti-vacuity for the allowance: the two detectors really do disagree here."""
        self.migrate()
        with ratchet.base_worktree(self.root, "main") as tree:
            self.assertIsNotNone(tree)
            before = ratchet.detector_charges(self.root, "main", tree)
            after = ratchet.own_charges(tree)
        self.assertEqual(sum(before.values()), 1)
        self.assertEqual(sum(after.values()), 2)
        self.assertTrue(ratchet.detector_logic_changed(self.root, "main"))

    def test_the_base_worktree_is_removed_again(self) -> None:
        """A checkout left behind would accumulate one registration per CI run."""
        with ratchet.base_worktree(self.root, "main") as tree:
            self.assertTrue((tree / "IsingModel" / "One.lean").exists())
            path = tree
        self.assertFalse(path.exists())
        listed = subprocess.run(
            ["git", "-C", self.tmp, "worktree", "list"],
            capture_output=True, text=True, check=True,
        )
        self.assertNotIn(str(path), listed.stdout)


#: A grammar widening: one new keyword in the predicate anchor.  Written as a
#: mutation of the shipped detector so that the "base" side of the exploit below
#: is the real thing rather than a stand-in.
WIDENED_PREDICATE = (
    r'rf"\b(?:cover(?:s|ing)?|contains?|holds?|collects?|groups?|bundles?|comprises?)"',
    r'rf"\b(?:cover(?:s|ing)?|contains?|holds?|collects?|groups?|bundles?|comprises?'
    r'|aggregates?)"',
)


def widened_detector() -> str:
    """Return the checker's source with ``aggregates`` added to the predicate anchor."""
    text = source_text()
    if WIDENED_PREDICATE[0] not in text:
        raise AssertionError("mutation target absent, the exploit fixture would be vacuous")
    return text.replace(*WIDENED_PREDICATE, 1)


class SmuggledGrammarTest(unittest.TestCase):
    """The exploit the head-tree recount permitted, and its legitimate twin.

    Both arms land the *same* detector change -- ``aggregates`` added to the
    predicate anchor -- declare the *same* migration, and re-pin.  The only
    difference is whether the prose the new keyword recognizes was already in
    the base commit's tree or was written by the diff.  A mechanism that cannot
    tell those apart lets a diff widen the grammar and bank claims under cover
    of the widening, which is precisely what the round-3 review reproduced:

        base detector charges 740 on this tree and this one charges 741;
        1 charge(s) ... attributable to the detector change
        PASS: the pin moved only where this diff explains it

    The allowance is now taken on the base commit's checkout, where prose the
    diff writes does not exist.
    """

    CLAIM = "This module aggregates seventeen lemmas."

    def setUp(self) -> None:
        self.tmp = tempfile.mkdtemp(prefix="claim-ratchet-smuggle-")
        self.addCleanup(shutil.rmtree, self.tmp, True)
        self.root = Path(self.tmp)
        (self.root / "IsingModel").mkdir()
        (self.root / "scripts" / "audit").mkdir(parents=True)
        self.write("IsingModel/One.lean", header("Narrow child module for the 12 foo wrappers."))
        self.write("IsingModel/Two.lean", header("Provides the bar API."))
        self.write(ratchet.DETECTOR_REPO_PATH, source_text())

    def start(self) -> None:
        """Commit the scratch repository's base, pinned by the shipped detector."""
        self.git("init", "-q", "-b", "main")
        self.git("config", "user.email", "t@example.com")
        self.git("config", "user.name", "t")
        self.git("add", "-A")
        self.write(
            ratchet.BASELINE_REPO_PATH,
            ratchet.format_baseline(ratchet.build_report(root=self.root).charged),
        )
        self.git("add", "-A")
        self.git("commit", "-q", "-m", "base")

    def git(self, *args: str) -> None:
        """Run ``git`` in the scratch repository."""
        subprocess.run(["git", "-C", self.tmp, *args], check=True, capture_output=True)

    def write(self, relative: str, text: str) -> None:
        """Write ``text`` at ``relative`` inside the scratch repository."""
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    def widen_and_declare(self, *mutations: tuple[str, str]) -> ratchet.Drift:
        """Land the widened detector, re-pin under it, declare, and measure.

        ``mutations`` weaken the *head* detector further, so that a canary can
        put back one half of the H1 fix at a time and watch the exploit come
        back to life.
        """
        text = widened_detector()
        for old, new in mutations:
            if old not in text:
                raise AssertionError(f"mutation target absent, canary would be vacuous: {old!r}")
            text = text.replace(old, new, 1)
        widened = load_source(text)
        self.write(ratchet.DETECTOR_REPO_PATH, text)
        pin = widened.build_report(root=self.root).charged
        path = self.root / ratchet.BASELINE_REPO_PATH
        path.write_text(
            f"{ratchet.MIGRATION_MARKER} PREDICATE_COUNT now recognizes `aggregates`\n"
            + widened.format_baseline(pin),
            encoding="utf-8",
        )
        return widened.check_drift(root=self.root, base_ref="main")

    #: Measure the allowance on the HEAD tree, as the round-3 version did.
    HEAD_TREE_RECOUNT = (
        "    with base_worktree(root, commit) as tree:\n",
        "    with contextlib.nullcontext(root) as tree:\n",
    )

    #: Grant an allowance even for a key whose file this diff edits.
    NO_EDITED_FILTER = (
        "        {key: count for key, count in gained.items() "
        "if target_path(key[1]) not in edited}\n",
        "        dict(gained)\n",
    )

    def test_prose_the_diff_writes_is_not_paid_for_by_the_widening(self) -> None:
        """The exploit: new keyword and new prose that matches it, in one diff."""
        self.start()
        self.write("IsingModel/Two.lean", header(self.CLAIM))
        drift = self.widen_and_declare()
        self.assertFalse(drift.ok, drift)
        self.assertEqual(
            [key for key, _now, _was in drift.added],
            [("PREDICATE_COUNT", "IsingModel/Two.lean", "17:lemmas")],
        )

    def test_prose_that_predates_the_diff_is_paid_for_by_the_widening(self) -> None:
        """Anti-vacuity: the same widening, the same declaration, a legitimate recount.

        Without this arm the fix above would be indistinguishable from disabling
        the hatch, and a mechanism that refuses every migration teaches people to
        route around it.
        """
        self.write("IsingModel/Two.lean", header(self.CLAIM))
        self.start()
        drift = self.widen_and_declare()
        self.assertTrue(drift.ok, drift)
        self.assertTrue(any("allowance" in note for note in drift.migration), drift.migration)

    def test_editing_the_file_forfeits_its_allowance(self) -> None:
        """Belt and braces: a key whose source this diff touches earns nothing.

        The prose predates the diff, so the base-tree measurement would grant
        the allowance -- and the diff edits the file it lives in, which is the
        shape "widen the grammar while rewriting the headers" takes.
        """
        self.write("IsingModel/Two.lean", header(self.CLAIM))
        self.start()
        self.write("IsingModel/Two.lean", header(self.CLAIM) + "\n-- an unrelated edit\n")
        drift = self.widen_and_declare()
        self.assertFalse(drift.ok, drift)
        self.assertEqual(
            [key for key, _now, _was in drift.added],
            [("PREDICATE_COUNT", "IsingModel/Two.lean", "17:lemmas")],
        )

    def test_either_half_of_the_fix_closes_the_exploit_alone(self) -> None:
        """Each rule is sufficient on its own, so neither is decoration."""
        self.start()
        self.write("IsingModel/Two.lean", header(self.CLAIM))
        self.assertFalse(self.widen_and_declare(self.NO_EDITED_FILTER).ok,
                         "the base-tree measurement alone must reject it")
        self.assertFalse(self.widen_and_declare(self.HEAD_TREE_RECOUNT).ok,
                         "the edited-file filter alone must reject it")

    def test_the_round_three_defect_is_reproduced_when_both_are_removed(self) -> None:
        """Anti-vacuity for the two canaries above: this is the reviewed bypass.

        Head-tree recount, no edited-file filter: the new prose is invisible to
        the base detector *and* to the new one on the base side, so it shows up
        as pure detector delta and pays for itself.  ``PASS: the pin moved only
        where this diff explains it``, on a diff that wrote a claim.
        """
        self.start()
        self.write("IsingModel/Two.lean", header(self.CLAIM))
        drift = self.widen_and_declare(self.HEAD_TREE_RECOUNT, self.NO_EDITED_FILTER)
        self.assertTrue(drift.ok, drift)
        self.assertTrue(any("allowance" in note for note in drift.migration), drift.migration)


#: A pure recall improvement: two more inventory nouns, recognizing prose that
#: was always there.  It is the *other* kind of detector change from
#: :data:`WIDENED_PREDICATE`, and the kind this design nearly made impossible:
#: ``RELOCATION``'s token carries the count as well as the destination, so a
#: subject the grammar newly understands does not add a row -- it *replaces*
#: ``->X`` with ``11->X``.  Round 4 measured both stagings of that and both
#: failed, which would have frozen the token grammar the moment the pin landed.
WIDENED_NOUN = (
    r'r"|modules?|files?|variants?)"',
    r'r"|modules?|files?|variants?|capstones?|bundles?)"',
)


def noun_widened_detector() -> str:
    """Return the checker's source with two nouns added to :data:`INVENTORY_NOUN`."""
    text = source_text()
    if WIDENED_NOUN[0] not in text:
        raise AssertionError("mutation target absent, the recall fixture would be vacuous")
    return text.replace(*WIDENED_NOUN, 1)


class MigrationDeltaTest(unittest.TestCase):
    """The arithmetic of the two budgets, without a repository around it."""

    KEY = ("RELOCATION", "IsingModel/One.lean", "->IsingModel.Other")
    REKEYED = ("RELOCATION", "IsingModel/One.lean", "11->IsingModel.Other")
    OTHER = ("RELOCATION", "IsingModel/One.lean", "->IsingModel.Third")

    def delta(self, before: dict, after: dict, edited=frozenset()):
        """Return ``(allowance, relief)`` for one measured detector delta."""
        return ratchet.migration_delta(Counter(before), Counter(after), edited)

    def test_a_rekeying_is_both_allowed_and_relieved(self) -> None:
        """The modal recall fix: one row replaces another, nobody edited prose."""
        allowance, relief = self.delta({self.KEY: 1}, {self.REKEYED: 1})
        self.assertEqual(allowance, Counter({self.REKEYED: 1}))
        self.assertEqual(relief, Counter({self.KEY: 1}))

    def test_a_net_reduction_earns_no_relief(self) -> None:
        """The laundering direction: narrow the detector, drop rows, declare."""
        allowance, relief = self.delta({self.KEY: 1, self.OTHER: 1}, {})
        self.assertEqual(allowance, Counter())
        self.assertEqual(relief, Counter())

    def test_one_rekeying_does_not_pay_for_a_second_removal(self) -> None:
        """The guard is per group and in aggregate, so a re-key cannot cover a drop."""
        allowance, relief = self.delta(
            {self.KEY: 1, self.OTHER: 1}, {self.REKEYED: 1}
        )
        self.assertEqual(allowance, Counter({self.REKEYED: 1}))
        self.assertEqual(relief, Counter(), "1 gain may not relieve 2 losses in one group")

    def test_a_gain_in_another_group_does_not_pay_for_a_loss(self) -> None:
        """Groups are ``(class, target)``: another file's gain is not this file's."""
        elsewhere = ("RELOCATION", "IsingModel/Two.lean", "4->IsingModel.Other")
        allowance, relief = self.delta({self.KEY: 1}, {elsewhere: 1})
        self.assertEqual(allowance, Counter({elsewhere: 1}))
        self.assertEqual(relief, Counter())

    def test_an_edited_file_earns_neither_budget(self) -> None:
        """The same rule guards both directions: a touched file is paid for by nobody."""
        allowance, relief = self.delta(
            {self.KEY: 1}, {self.REKEYED: 1}, frozenset({"IsingModel/One.lean"})
        )
        self.assertEqual(allowance, Counter())
        self.assertEqual(relief, Counter())


class RecallMigrationTest(unittest.TestCase):
    """A recall improvement that re-keys existing prose must be landable.

    Round 4's H2: adding an inventory noun made six pinned ``RELOCATION`` rows
    become sharper keys, which is one addition and one removal per sentence, on
    prose the diff does not touch.  ``B1`` covered the additions only while the
    files stayed untouched and ``B2`` demanded those very files be touched, so
    the two rules were mutually exclusive and the improvement had no staging at
    all.  Both arms below land the *same* widening; what differs is whether the
    prose it recognizes predates the diff.
    """

    CLAIM = "The 11 along-exhaustion capstones now live in `IsingModel.Other`."
    OLD_KEY = ("RELOCATION", "IsingModel/One.lean", "->IsingModel.Other")
    NEW_KEY = ("RELOCATION", "IsingModel/One.lean", "11->IsingModel.Other")

    def setUp(self) -> None:
        self.tmp = tempfile.mkdtemp(prefix="claim-ratchet-recall-")
        self.addCleanup(shutil.rmtree, self.tmp, True)
        self.root = Path(self.tmp)
        (self.root / "IsingModel").mkdir()
        (self.root / "scripts" / "audit").mkdir(parents=True)
        self.write("IsingModel/One.lean", header(self.CLAIM))
        self.write("IsingModel/Two.lean", header("Provides the bar API."))
        # Lowercase, so the narrowing arm below has a row to lose.
        self.write("IsingModel/Three.lean", header("narrow child module for the 5 bar wrappers."))
        self.write(ratchet.DETECTOR_REPO_PATH, source_text())

    def start(self) -> None:
        """Commit the base: the shipped detector, and its own pin of this tree."""
        self.git("init", "-q", "-b", "main")
        self.git("config", "user.email", "t@example.com")
        self.git("config", "user.name", "t")
        self.git("add", "-A")
        pin = ratchet.build_report(root=self.root).charged
        self.assertEqual(pin[self.OLD_KEY], 1, "the base detector must miss the count")
        self.write(ratchet.BASELINE_REPO_PATH, ratchet.format_baseline(pin))
        self.git("add", "-A")
        self.git("commit", "-q", "-m", "base")

    def git(self, *args: str) -> None:
        """Run ``git`` in the scratch repository."""
        subprocess.run(["git", "-C", self.tmp, *args], check=True, capture_output=True)

    def write(self, relative: str, text: str) -> None:
        """Write ``text`` at ``relative`` inside the scratch repository."""
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    def land(self, text: str, reason: str) -> tuple[ratchet.Drift, Counter]:
        """Land detector ``text``, re-pin under it, declare, and measure."""
        detector = load_source(text)
        self.write(ratchet.DETECTOR_REPO_PATH, text)
        pin = detector.build_report(root=self.root).charged
        path = self.root / ratchet.BASELINE_REPO_PATH
        path.write_text(
            f"{ratchet.MIGRATION_MARKER} {reason}\n" + detector.format_baseline(pin),
            encoding="utf-8",
        )
        return detector.check_drift(root=self.root, base_ref="main"), pin

    def test_a_pure_recall_improvement_lands(self) -> None:
        """The positive case round 4 proved impossible, with no prose edited."""
        self.start()
        drift, pin = self.land(noun_widened_detector(), "INVENTORY_NOUN gained `capstones`")
        self.assertEqual(pin[self.NEW_KEY], 1, "the widened detector resolves the count")
        self.assertEqual(pin[self.OLD_KEY], 0, "and the coarse key is gone")
        self.assertTrue(drift.ok, drift)
        self.assertTrue(any("relief: 1 charge" in note for note in drift.migration),
                        drift.migration)

    def test_the_recall_improvement_may_not_carry_new_prose(self) -> None:
        """H1's exploit, in the recall staging: a claim the diff writes still fails."""
        self.start()
        self.write(
            "IsingModel/Two.lean",
            header("The 7 smuggled capstones now live in `IsingModel.Elsewhere`."),
        )
        drift, _pin = self.land(noun_widened_detector(), "INVENTORY_NOUN gained `capstones`")
        self.assertFalse(drift.ok, drift)
        self.assertEqual(
            [key for key, _now, _was in drift.added],
            [("RELOCATION", "IsingModel/Two.lean", "7->IsingModel.Elsewhere")],
        )

    def test_editing_the_recalled_file_forfeits_both_budgets(self) -> None:
        """The relief is zeroed by the same rule the allowance is.

        Widening the grammar *and* editing the file it newly understands is the
        shape "widen while rewriting the headers" takes.  Both budgets go to
        zero, so the re-keyed row is a plain ``B1`` rise; the removal it replaces
        is explained by the edit itself, which is ``B2``'s ordinary rule and not
        the relief.
        """
        self.start()
        self.write("IsingModel/One.lean", header(self.CLAIM) + "\n-- an unrelated edit\n")
        drift, _pin = self.land(noun_widened_detector(), "INVENTORY_NOUN gained `capstones`")
        self.assertFalse(drift.ok, drift)
        self.assertEqual([key for key, _now, _was in drift.added], [self.NEW_KEY])
        self.assertTrue(any("relief: 0 charge(s) over 0 key(s)" in note
                            for note in drift.migration), drift.migration)
        self.assertTrue(any("0 charge(s) over 0 key(s) in files this diff does not touch" in note
                            for note in drift.migration), drift.migration)

    def test_a_narrowing_that_only_drops_rows_is_still_a_b2_failure(self) -> None:
        """The guard: relief may never become "blind the detector, drop the row".

        The narrowed detector stops seeing the lowercase ``NARROW_CHILD`` claim
        entirely -- a group that loses without gaining -- so the row it removes
        from the pin is unexplained however loudly the migration is declared.
        """
        self.start()
        drift, pin = self.land(narrowed_detector(), "anchor narrowed")
        self.assertEqual(pin[("NARROW_CHILD", "IsingModel/Three.lean", "5")], 0)
        self.assertFalse(drift.ok, drift)
        self.assertEqual(
            [key for key, _now, _was in drift.unexplained],
            [("NARROW_CHILD", "IsingModel/Three.lean", "5")],
        )


# --------------------------------------------------------------------------
# The real tree
# --------------------------------------------------------------------------

_REAL: ratchet.Report | None = None


def real_report() -> ratchet.Report:
    """Return the (cached) verdict of one full scan of this repository."""
    global _REAL  # noqa: PLW0603
    if _REAL is None:
        _REAL = ratchet.build_report()
    return _REAL


class RealTreeTest(unittest.TestCase):
    """The delivered verdict, pinned."""

    def test_the_scan_sees_the_whole_tracked_set(self) -> None:
        report = real_report()
        self.assertGreater(len(report.sources), TARGET_FLOOR)
        paths = {source.path for source in report.sources}
        self.assertIn("IsingModel.lean", paths, "the top-level umbrella is in scope")
        self.assertIn("README.md", paths)
        self.assertIn("docs/index.md", paths)
        self.assertIn("tex/proof-guide.tex", paths)
        self.assertIn("docs/architecture-import-layers.md", paths)

    def test_the_documented_exclusions_are_really_excluded(self) -> None:
        """`test/`, `.github/` and `scripts/` are out of scope on purpose.

        Stated as an assertion and not only as a docstring: ``scripts/`` holds
        this suite, every fixture in which is a deliberate inventory claim, so a
        scan that reached it would grow its own pin with each new canary.
        """
        for path in ratchet.tracked_paths():
            self.assertFalse(
                path.startswith(ratchet.EXCLUDED_ROOTS), f"{path} is inside an excluded root"
            )
            self.assertTrue(path.endswith(ratchet.SCAN_SUFFIXES), path)
        self.assertTrue((REPO_ROOT / "scripts" / "audit").is_dir(), "anti-vacuity")

    def test_every_target_name_inverts_to_its_path(self) -> None:
        """`target_path` inverts on the delivered tree.

        A property of the corpus, kept as a smoke check only.  The property of
        the *keying* -- which is what H0 broke -- is
        :class:`KeyIdentityTest`, on constructed inputs.
        """
        for source in real_report().sources:
            self.assertEqual(ratchet.target_path(source.target), source.path)

    def test_the_real_run_is_sound(self) -> None:
        """K0/K1/K2/K3/K4 hold on the tree as delivered."""
        report = real_report()
        self.assertTrue(report.sound, "\n".join(report.conservation))

    def test_every_documented_reference_names_something_real(self) -> None:
        """A docstring that names a symbol which does not exist is this PR's own bug.

        Four review rounds have turned on a docstring stating a property the code
        does not have; the cheapest half of that class is a docstring naming a
        function the code does not have, and a rename is all it takes.  Two live
        ones were found this way (`_GOVERNED_QUANTITY` after a rename here,
        `detector_recount` which has never existed).  Attributes resolve against
        the module's own classes, since a class docstring names its fields
        without qualifying them.
        """
        text = SCRIPT_FILE.read_text(encoding="utf-8")
        scopes = [ratchet] + [
            value for value in vars(ratchet).values()
            if isinstance(value, type) and value.__module__ == ratchet.__name__
        ]
        dangling = []
        for role, name in re.findall(r":(data|func|class|attr|meth):`([^`]+)`", text):
            head, *rest = name.split(".")
            found = False
            for scope in scopes:
                target = getattr(scope, head, None)
                for part in rest:
                    target = getattr(target, part, None)
                found = found or target is not None
            if not found:
                dangling.append(f":{role}:`{name}`")
        self.assertEqual(sorted(set(dangling)), [], "anti-vacuity: the roles are found")
        self.assertGreater(len(re.findall(r":func:`", text)), 20, "anti-vacuity")

    def test_the_tree_is_not_regressed_against_the_committed_baseline(self) -> None:
        baseline, errors = ratchet.read_baseline()
        self.assertEqual(errors, [])
        comparison = ratchet.compare(real_report().charged, baseline)
        self.assertFalse(
            comparison.regressed,
            f"new={comparison.new[:5]} grown={comparison.grown[:5]}",
        )

    def test_the_baseline_may_only_ever_shrink(self) -> None:
        """A ratchet on the ratchet: raising the pin has to be a deliberate edit."""
        baseline, _errors = ratchet.read_baseline()
        self.assertLessEqual(sum(baseline.values()), BASELINE_CEILING)

    def test_the_live_population_is_well_formed(self) -> None:
        """Shape, never size: this assertion has to survive the campaign succeeding.

        It used to require more than a hundred live charges and three named
        classes still present on the tree.  That reads as anti-vacuity but is a
        floor under the defect count: driving it down is the entire point of the
        ratchet, so the suite would have turned red exactly when the campaign
        worked, and the cheapest repair would have been to loosen the test inside
        the PR that did the repairing -- the self-certification shape this design
        exists to refuse.  Anti-vacuity belongs on fixtures
        (:class:`DetectorAliveTest`), which stay true at zero live claims; what
        the live tree owes is only that every key it produces is well formed.
        """
        report = real_report()
        known = {claim_class.name for claim_class in ratchet.CLAIM_CLASSES} | {
            ratchet.NON_PROSE, ratchet.MISSING_DOC, ratchet.UNTERMINATED
        }
        targets = {source.target for source in report.sources}
        for (kind, target, token), count in report.charged.items():
            self.assertIn(kind, known)
            self.assertIn(target, targets)
            self.assertTrue(token)
            self.assertGreater(count, 0)

    def test_the_scan_is_deterministic(self) -> None:
        """Same tree, same population: no set iteration leaking into the output."""
        again = ratchet.build_report()
        self.assertEqual(again.charged, real_report().charged)


class CIWiringTest(unittest.TestCase):
    """A gate nobody runs is not a gate.

    The wiring is read out of the workflow rather than assumed: a substring
    search would be satisfied by a commented-out step, so only the scalar of a
    ``run:`` key counts here.
    """

    @classmethod
    def setUpClass(cls) -> None:
        cls.commands = cls.run_commands()

    @staticmethod
    def run_commands() -> list[str]:
        """Every single-line ``run:`` scalar of the workflow, in file order."""
        commands: list[str] = []
        for line in WORKFLOW_FILE.read_text(encoding="utf-8").splitlines():
            stripped = line.strip()
            if stripped.startswith("#") or not stripped.startswith("run:"):
                continue
            command = stripped[len("run:"):].strip()
            if command:
                commands.append(command)
        return commands

    @staticmethod
    def job_block() -> str:
        """The workflow text of the ratchet job, up to the next top-level job."""
        text = WORKFLOW_FILE.read_text(encoding="utf-8")
        start = text.index(f"\n  {CI_JOB}:\n") + 1
        rest = text[start + 1:]
        offsets = [
            match for match in (rest.find(f"\n  {name}") for name in ("build:", "import-dag"))
            if match >= 0
        ]
        end = min(offsets) if offsets else len(rest)
        return rest[:end]

    def test_ci_runs_the_gate(self) -> None:
        self.assertIn(GATE_COMMAND, self.commands, f"run commands seen = {self.commands}")

    def test_ci_runs_the_checkers_own_tests(self) -> None:
        self.assertIn(SUITE_COMMAND, self.commands, f"run commands seen = {self.commands}")

    def test_ci_runs_the_baseline_drift_check(self) -> None:
        """Without it the pin is only ever compared against itself."""
        self.assertIn(DRIFT_COMMAND, self.commands, f"run commands seen = {self.commands}")

    def test_the_self_tests_run_before_the_gate(self) -> None:
        """`--check` stays green when a rule is weakened; the suite is what fails."""
        self.assertLess(self.commands.index(SUITE_COMMAND), self.commands.index(GATE_COMMAND))

    def test_the_drift_job_checks_out_enough_history(self) -> None:
        """`fetch-depth: 0`, or `origin/main` is absent and the drift step fails closed."""
        self.assertIn("fetch-depth: 0", self.job_block())


def run_suite() -> int:
    """Run every test. Return ``0`` on success, ``1`` otherwise."""
    loader = unittest.TestLoader()
    suite = loader.loadTestsFromModule(sys.modules[__name__])
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    return 0 if result.wasSuccessful() else 1


if __name__ == "__main__":
    sys.exit(run_suite())

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
editing ``IsingModel/``.  Two suites do read the repository: :class:`RealTreeTest`,
which pins the delivered verdict and the ceiling on the baseline, and
:class:`ScratchRepoTest`, which builds a throwaway ``git`` repository so the
tracked-set discipline (``git ls-files``, never a filesystem walk) is exercised
end to end rather than assumed.
"""

from __future__ import annotations

import contextlib
import io
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

#: Ceiling on the pinned baseline, first measured at 713 charges on the commit
#: that introduced it (main ``fd1cdd8a``) and corrected to 740 when
#: ``NARROW_CHILD``'s anchor gained ``re.IGNORECASE``: 27 lowercase occurrences
#: that had always been in the tree became visible to the detector, so the 713
#: was an undercount of the tree, not a smaller population.  A ceiling, not an
#: equality: the campaign this ratchet exists to serve drives the number down,
#: and re-pinning after a repair must not need a test edit -- but *raising* it
#: has to, which is why this correction had to be made here in the open.
BASELINE_CEILING = 740

#: A minimal declaration, so a fixture module is never accidentally an umbrella.
TRIVIAL = "theorem f : True := trivial\n"

#: The command lines CI must run, in this order.
SUITE_COMMAND = "python3 scripts/test_header_inventory_claim_ratchet.py"
GATE_COMMAND = "python3 scripts/header_inventory_claim_ratchet.py --check"


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


def lean_source(target: str, text: str, module=ratchet):
    """Return a synthetic Lean :class:`Source` named ``target``."""
    return module.Source(target=target, path=f"{target}.lean", text=text, is_lean=True)


def doc_source(target: str, text: str, module=ratchet):
    """Return a synthetic document :class:`Source` named ``target``."""
    return module.Source(target=target, path=target, text=text, is_lean=False)


def charged(source, module=ratchet) -> list:
    """Return the charged claims of one source."""
    return [claim for claim in module.scan_source(source).claims if claim.charged]


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

    def test_an_unquantified_narrow_child_header_is_accounted_not_charged(self) -> None:
        """`for concrete latticeGraph specializations` states no size."""
        source = lean_source(
            "M", header("Narrow child module for concrete `latticeGraph` specializations of X.")
        )
        claims = ratchet.scan_source(source).claims
        self.assertEqual([claim.charged for claim in claims], [False])
        self.assertEqual(claims[0].kind, "NARROW_CHILD")

    def test_an_unquantified_relocation_is_accounted_not_charged(self) -> None:
        """Ownership prose without a size is reported, but this tool does not size it."""
        source = lean_source("M", header("The basic wrappers now live in `IsingModel.Other`."))
        claims = [c for c in ratchet.scan_source(source).claims if c.kind == "RELOCATION"]
        self.assertEqual([claim.charged for claim in claims], [False])

    def test_a_pr_reference_is_not_mistaken_for_a_quantity(self) -> None:
        """`Step 241 interior wrappers now live in X` must not charge 241."""
        source = lean_source(
            "M",
            header("The regularity wrappers (Step 241 interior `ContinuousAt` wrappers) "
                   "now live in `IsingModel.Other`."),
        )
        self.assertEqual(tokens(source, "RELOCATION"), [])

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


KEY_A = ("NARROW_CHILD", "IsingModel.A", "12")
KEY_B = ("NARROW_CHILD", "IsingModel.B", "4")


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
        _counts, errors = ratchet.parse_baseline("NARROW_CHILD\tIsingModel.A\n")
        self.assertTrue(errors)
        _counts, errors = ratchet.parse_baseline("NARROW_CHILD\tIsingModel.A\t12\tmany\n")
        self.assertTrue(errors)

    def test_the_baseline_round_trips(self) -> None:
        base = population((KEY_A, 3), (KEY_B, 1))
        parsed, errors = ratchet.parse_baseline(ratchet.format_baseline(base))
        self.assertEqual(errors, [])
        self.assertEqual(parsed, base)

    def test_the_report_never_says_the_headers_are_clean(self) -> None:
        """False assurance is the risk the arbitration named as the biggest one."""
        source = lean_source("M", header("Provides the ambient monotonicity API."))
        report = ratchet.Report(
            sources=(source,), claims=ratchet.scan_source(source).claims, conservation=()
        )
        buffer = io.StringIO()
        with contextlib.redirect_stdout(buffer):
            ok = ratchet.print_report(report, Counter(), [])
        output = buffer.getvalue()
        self.assertTrue(ok)
        self.assertIn("A pass never means the headers are clean.", output)
        self.assertIn("says nothing about unrecognized prose", output)


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
        self.assertEqual(len(scanned.claims), 0)
        self.assertEqual(len(ratchet.scan_source(lean_source("M", text)).claims), 1)

    def test_a_non_nesting_comment_scanner_misplaces_a_claim(self) -> None:
        """K2's reason to exist: nesting decides which side of the mask a claim is on."""
        mutant = load_mutant(
            ("            if token == \"/-\":\n                depth += 1\n",
             "            if token == \"/-\":\n                pass\n"),
        )
        text = "/-!\n# F\n-/\n/- outer /- inner -/ Narrow child module for the 5 foo wrappers. -/\n"
        self.assertEqual(tokens(lean_source("M", text), "NARROW_CHILD"), ["5"])
        mutated = [claim.kind for claim in charged(lean_source("M", text, mutant), mutant)]
        self.assertIn(mutant.NON_PROSE, mutated)

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
            ("    if source.is_lean and _MODULE_DOC not in text:", "    if False:"),
        )
        text = "import IsingModel.Basic\n\ntheorem f : True := trivial\n"
        self.assertEqual(len(charged(lean_source("M", text))), 1)
        self.assertEqual(len(charged(lean_source("M", text, mutant), mutant)), 0)

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
        self.assertIn("NARROW_CHILD IsingModel.Two 7", output)

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
        self.assertEqual(
            {source.path for source in report.sources if not source.is_lean},
            set(ratchet.DOC_TARGETS),
        )

    def test_the_real_run_is_sound(self) -> None:
        """K0/K1/K2 hold on the tree as delivered."""
        report = real_report()
        self.assertTrue(report.sound, "\n".join(report.conservation))

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

    def test_the_population_is_not_degenerate(self) -> None:
        """A collapsed extractor would make every assertion above vacuously true."""
        live = real_report().charged
        kinds = {key[0] for key in live}
        self.assertGreater(sum(live.values()), 100)
        for name in ("NARROW_CHILD", "PAREN_COUNT", "RELOCATION"):
            self.assertIn(name, kinds)

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

    def test_ci_runs_the_gate(self) -> None:
        self.assertIn(GATE_COMMAND, self.commands, f"run commands seen = {self.commands}")

    def test_ci_runs_the_checkers_own_tests(self) -> None:
        self.assertIn(SUITE_COMMAND, self.commands, f"run commands seen = {self.commands}")

    def test_the_self_tests_run_before_the_gate(self) -> None:
        """`--check` stays green when a rule is weakened; the suite is what fails."""
        self.assertLess(self.commands.index(SUITE_COMMAND), self.commands.index(GATE_COMMAND))


def run_suite() -> int:
    """Run every test. Return ``0`` on success, ``1`` otherwise."""
    loader = unittest.TestLoader()
    suite = loader.loadTestsFromModule(sys.modules[__name__])
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    return 0 if result.wasSuccessful() else 1


if __name__ == "__main__":
    sys.exit(run_suite())

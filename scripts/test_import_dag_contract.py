#!/usr/bin/env python3
"""Tests for the import-DAG layer contract (``scripts/import_dag_contract.py``).

The contract is worth exactly as much as the proof that it can fail.  The suite
is therefore built around canaries: :class:`CanaryTest` mutates a synthetic tree
once per enforced rule and requires the checker to name that exact edge, and
:meth:`RuleTableTest.test_every_enforced_rule_has_a_canary` requires a canary to
exist for every rule in :data:`import_dag_contract.RULES`, so a rule that is
silently dropped from -- or quietly added to -- the table cannot stay green.

Every structural fixture is synthetic (``scripts/testdata/import_dag_contract/``),
so no test can be repaired by editing ``IsingModel/``.  The two assertions that
do read the real tree are :class:`RealTreeTest`, which pins the delivered
verdict, and the anti-scope checks that read this checker's own source.
"""

from __future__ import annotations

import contextlib
import io
import shutil
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
FIXTURE_DIR = SCRIPT_DIR / "testdata" / "import_dag_contract"
sys.path.insert(0, str(SCRIPT_DIR))

import import_dag_contract as contract  # noqa: E402

#: Ceiling on the unranked ``L2_THEORY -> L4_LATTICE/L5_CHAIN`` edge count of the
#: real tree, measured at 28 on the delivering commit.  A ceiling rather than an
#: equality: unrelated module additions must not turn the suite red, but growing
#: the unranked set has to be a deliberate, reviewed edit.  It is NOT a quota --
#: nothing in the checker reads it and the contract's exit status ignores INFO
#: entirely (:meth:`AntiScopeTest.test_info_edges_cannot_change_the_verdict`).
INFO_CEILING = 28

#: Floor on the number of modules the real scan sees, so a collapse of the graph
#: builder cannot make every assertion below vacuously true.
REAL_MODULE_FLOOR = 1500


def load_manifest(name: str) -> dict[str, str]:
    """Parse a fixture manifest into ``{repo-relative path: file text}``."""
    text = (FIXTURE_DIR / name).read_text(encoding="utf-8")
    files: dict[str, str] = {}
    current: str | None = None
    lines: list[str] = []
    for raw in text.splitlines():
        if raw.startswith("--- "):
            if current is not None:
                files[current] = "\n".join(lines).strip("\n") + "\n"
            current = raw[4:].strip()
            lines = []
        elif current is not None:
            lines.append(raw)
    if current is not None:
        files[current] = "\n".join(lines).strip("\n") + "\n"
    return files


def materialize(files: dict[str, str], root: Path) -> Path:
    """Write ``files`` under ``root`` and return ``root``."""
    for relative, text in files.items():
        path = root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")
    return root


class TreeHarness(unittest.TestCase):
    """Base class materialising a fixture manifest into a temporary tree."""

    MANIFEST = "tree_clean.txt"

    def setUp(self) -> None:
        self.tmp = tempfile.mkdtemp(prefix="import-dag-contract-")
        self.addCleanup(shutil.rmtree, self.tmp, True)
        self.root = Path(self.tmp)
        self.files = load_manifest(self.MANIFEST)

    def tree(self, mutations: dict[str, str] | None = None) -> Path:
        """Materialise the fixture, appending each mutation's import line.

        ``mutations`` maps a fixture path to an extra ``import`` line, which is
        prepended to that file exactly the way a contributor would add one.
        """
        files = dict(self.files)
        for relative, extra in (mutations or {}).items():
            self.assertIn(relative, files, "mutation targets a file the fixture lacks")
            files[relative] = extra + "\n" + files[relative]
        root = self.root / f"tree{len(list(self.root.iterdir()))}"
        root.mkdir()
        return materialize(files, root)

    def report(self, root: Path, baseline: str | None = None) -> contract.Report:
        """Return the contract's verdict for ``root`` under an optional baseline."""
        baseline_path = root / "baseline.txt"
        baseline_path.write_text(baseline or "", encoding="utf-8")
        return contract.build_report(root=root, baseline_path=baseline_path)

    def verdict(self, root: Path, baseline: str | None = None) -> tuple[bool, str]:
        """Return ``(passes, printed report)`` for ``root``."""
        report = self.report(root, baseline)
        entries, _ = contract.parse_baseline(baseline or "")
        buffer = io.StringIO()
        with contextlib.redirect_stdout(buffer):
            ok = contract.print_report(report, entries)
        return ok, buffer.getvalue()

    def violation_keys(self, report: contract.Report) -> set[str]:
        """Return the ``importer -> target`` keys of every reported violation."""
        return {edge.key for edges in report.violations.values() for edge in edges}


# --------------------------------------------------------------------------
# T4 -- layer tagging
# --------------------------------------------------------------------------


class LayerTagTest(unittest.TestCase):
    """Prefix matching must consume whole dotted components, never characters."""

    def test_the_exact_model_core_list_is_l1(self) -> None:
        """``L1_MODEL`` is an enumerated set, not "lives at the root"."""
        for module in contract.L1_MODEL_MODULES:
            self.assertEqual(contract.layer_of(module), contract.L1_MODEL, module)

    def test_other_root_modules_are_not_model_core(self) -> None:
        """Root files split three ways; the leftovers default to theory."""
        self.assertEqual(contract.layer_of("IsingModel.SumModel"), contract.L2_THEORY)
        self.assertEqual(contract.layer_of("IsingModel.Asano"), contract.L2_THEORY)
        self.assertEqual(contract.layer_of("IsingModel.Lattice"), contract.L4_LATTICE)

    def test_sibling_prefixes_are_not_confused(self) -> None:
        """The live trap: ``Lattice`` must not swallow ``LatticeExpSum``.

        Both names exist in the tree and both belong to ``L4_LATTICE``, but for
        *different* reasons; a bare ``startswith`` would make the second rule
        dead code and would equally capture any future ``LatticeFoo``.
        """
        self.assertEqual(contract.layer_of("IsingModel.LatticeExpSum"), contract.L4_LATTICE)
        self.assertEqual(contract.layer_of("IsingModel.Lattice.Sub"), contract.L4_LATTICE)
        self.assertEqual(contract.layer_of("IsingModel.LatticeFoo"), contract.L2_THEORY)

    def test_no_prefix_rule_captures_a_longer_sibling_name(self) -> None:
        """Every prefix rule, checked against a hypothetical ``<prefix>Foo``."""
        for prefix, layer in contract.LAYER_PREFIXES:
            sibling = prefix + "Foo"
            if any(sibling == other or sibling.startswith(other + ".")
                   for other, _ in contract.LAYER_PREFIXES):
                continue
            self.assertEqual(contract.layer_of(sibling), contract.L2_THEORY,
                             f"{prefix!r} captured {sibling!r} by bare startswith")
            self.assertEqual(contract.layer_of(prefix), layer, prefix)

    def test_longest_prefix_wins(self) -> None:
        """Overlapping rules resolve to the most specific one."""
        self.assertEqual(
            contract.layer_of("IsingModel.AmbientLattice.Monotonicity.PlusScreening"),
            contract.L3_AMBIENT,
        )
        self.assertEqual(contract.layer_of("IsingModel.AmbientLatticeSum.Foo"), contract.L3_AMBIENT)

    def test_the_default_layer_is_theory(self) -> None:
        """An unmatched module is unranked, never silently promoted."""
        self.assertEqual(contract.layer_of("IsingModel.SomethingBrandNew"), contract.L2_THEORY)


# --------------------------------------------------------------------------
# T3 -- aggregator classification
# --------------------------------------------------------------------------


class AggregatorTest(TreeHarness):
    """The classifier must not let a real module pass as a re-export index."""

    MANIFEST = "tree_aggregator.txt"

    def test_the_fixture_names_encode_the_expectation(self) -> None:
        """Every ``Agg*`` file is an aggregator and every ``Real*`` file is not."""
        root = self.tree()
        graph = contract.load_graph(root)
        self.assertTrue(graph.modules, "the aggregator fixture materialised no module")
        for module in sorted(graph.modules):
            final = module.rsplit(".", 1)[-1]
            expected = final.startswith("Agg")
            self.assertEqual(module in graph.aggregators, expected, module)

    def test_both_classes_are_populated(self) -> None:
        """Anti-vacuity: a classifier that answers a constant fails here."""
        root = self.tree()
        graph = contract.load_graph(root)
        self.assertGreaterEqual(len(graph.aggregators), 3)
        self.assertGreaterEqual(len(graph.modules - graph.aggregators), 5)

    def test_a_missing_file_is_not_an_aggregator(self) -> None:
        """An unresolvable target must not silently gain pass-through semantics."""
        self.assertFalse(contract.is_aggregator("IsingModel.NoSuchModule", self.root))


#: Declaration forms whose *only* common feature is that they are content.  The
#: classifier must keep every one of them checkable; the list exists because a
#: keyword denylist fails open, and ``unsafe def`` was exactly the form that
#: escaped one.  A form nobody anticipated must behave like these, not like an
#: umbrella -- which is what the allowlist buys and what the sweep below pins.
DECLARATION_FORMS = (
    "theorem d : True := trivial",
    "@[simp] theorem d : True := trivial",
    "private noncomputable def d : Nat := 0",
    "unsafe def d : Nat := 0",
    "partial def d : Nat := 0",
    "nonrec def d : Nat := 0",
    "protected unsafe partial def d : Nat := 0",
    "abbrev d : Nat := 0",
    "instance d : Inhabited Nat := ⟨0⟩",
    "structure D where\n  field : Nat",
    "inductive D | a | b",
    "class D where\n  field : Nat",
    "alias d := other",
    "macro_rules | `(x) => `(y)",
    "notation:max \"d\" => 0",
    "attribute [simp] other",
    "deriving instance Repr for Nat",
    "open Nat in theorem d : True := trivial",
    "set_option maxHeartbeats 400000 in\ntheorem d : True := trivial",
    "initialize d : Nat ← pure 0",
    "example : True := trivial",
    # Lean's grammar is whitespace-insensitive at the command level: the next
    # two lines each hold several commands and each compiles.  A classifier that
    # inspected only the start of a line would call both harmless.
    "namespace Foo theorem d : True := trivial end Foo",
    "section open Nat theorem d : True := trivial end",
    # Scaffolding around nothing.  Not content, but not recognised as an
    # umbrella either, because the line above cannot be told apart from it
    # without parsing Lean.  Under-recognition is the safe direction.
    "namespace Foo\nopen Nat\nvariable {V : Type*}\nend Foo",
)


class DeclarationFormTest(unittest.TestCase):
    """No non-import content may make a module invisible to the enforced rules.

    This is the regression test for two false negatives an independent review
    found.  With a denylist of declaration *keywords*, a module whose only
    content was ``unsafe def`` classified as an umbrella, so its forbidden
    ``L3_AMBIENT -> L4_LATTICE`` import was not reported at all; with an
    allowlist matched at the *start of a line*, ``namespace Foo theorem d :
    True := trivial end Foo`` did the same.  Each case is asserted twice -- the
    classification *and* the direction verdict it feeds -- because the
    classification alone is not the property that matters.
    """

    def setUp(self) -> None:
        self.tmp = tempfile.mkdtemp(prefix="import-dag-forms-")
        self.addCleanup(shutil.rmtree, self.tmp, True)

    def tree_with(self, body: str, index: int) -> Path:
        """Return a two-module tree: an ``L3`` module with ``body``, an ``L4`` sink."""
        root = Path(self.tmp) / f"case{index}"
        return materialize(
            {
                "IsingModel/AmbientLattice/Ambient.lean": (
                    "import IsingModel.Concrete.Sink\n\n" + body + "\n"
                ),
                "IsingModel/Concrete/Sink.lean": "theorem concreteSink : True := trivial\n",
            },
            root,
        )

    def test_every_declaration_form_stays_a_violation_source(self) -> None:
        """Content in any spelling keeps the module checkable, and R3 fires."""
        for index, body in enumerate(DECLARATION_FORMS):
            with self.subTest(form=body.splitlines()[0]):
                root = self.tree_with(body, index)
                graph = contract.load_graph(root)
                self.assertNotIn("IsingModel.AmbientLattice.Ambient", graph.aggregators)
                report = contract.build_report(root=root, baseline_path=root / "none.txt")
                self.assertEqual(
                    [edge.key for edge in report.violations["R3"]],
                    ["IsingModel.AmbientLattice.Ambient -> IsingModel.Concrete.Sink"],
                )

    def test_a_genuine_umbrella_in_the_same_position_is_not_a_source(self) -> None:
        """Anti-vacuity: the sweep above must not be flagging every module."""
        root = self.tree_with("/-! A pure re-export index. -/", len(DECLARATION_FORMS))
        graph = contract.load_graph(root)
        self.assertIn("IsingModel.AmbientLattice.Ambient", graph.aggregators)
        report = contract.build_report(root=root, baseline_path=root / "none.txt")
        self.assertEqual(report.violations["R3"], [])


class ReadableImportTest(unittest.TestCase):
    """A line the import scanner cannot fully read is a hard failure.

    ``leaf_audit.build_import_graph`` reads one ``import`` per physical line, and
    Lean accepts more than one.  An independent review showed that
    ``import IsingModel.Inequalities.Safe import IsingModel.Concrete.Sink`` in an
    ``L3_AMBIENT`` module therefore hid the second edge from every rule.  The
    contract now refuses to certify such a file instead of reporting it clean.
    """

    def setUp(self) -> None:
        self.tmp = tempfile.mkdtemp(prefix="import-dag-readable-")
        self.addCleanup(shutil.rmtree, self.tmp, True)

    def tree_with(self, header: str, name: str) -> Path:
        """Return a tree whose ``L3`` module has ``header`` as its import block."""
        return materialize(
            {
                "IsingModel/AmbientLattice/Ambient.lean": header + "\ntheorem a : True := trivial\n",
                "IsingModel/Inequalities/Safe.lean": "theorem s : True := trivial\n",
                "IsingModel/Concrete/Sink.lean": "theorem c : True := trivial\n",
            },
            Path(self.tmp) / name,
        )

    def verdict(self, root: Path) -> tuple[bool, str]:
        """Return ``(passes, printed report)`` for ``root`` with no baseline."""
        baseline = root / "baseline.txt"
        baseline.write_text("", encoding="utf-8")
        report = contract.build_report(root=root, baseline_path=baseline)
        buffer = io.StringIO()
        with contextlib.redirect_stdout(buffer):
            ok = contract.print_report(report, {})
        return ok, buffer.getvalue()

    def test_two_imports_on_one_line_fail(self) -> None:
        """The exact shape that hid an ``L3 -> L4`` edge from the graph."""
        root = self.tree_with(
            "import IsingModel.Inequalities.Safe import IsingModel.Concrete.Sink", "two"
        )
        graph = contract.load_graph(root)
        self.assertNotIn(
            "IsingModel.Concrete.Sink", graph.imports["IsingModel.AmbientLattice.Ambient"],
            "the scanner unexpectedly saw the second import; this test is now vacuous",
        )
        ok, text = self.verdict(root)
        self.assertFalse(ok, text)
        self.assertIn("more than one `import`", text)

    def test_a_non_ising_import_cannot_shadow_an_ising_one(self) -> None:
        """The scanner's regex anchors on ``import IsingModel``, so this hides too."""
        root = self.tree_with("import Mathlib.Order.Basic import IsingModel.Concrete.Sink", "mixed")
        ok, text = self.verdict(root)
        self.assertFalse(ok, text)

    def test_one_import_per_line_passes(self) -> None:
        """Anti-vacuity: the ordinary shape is not flagged."""
        root = self.tree_with(
            "import IsingModel.Inequalities.Safe\nimport IsingModel.Concrete.Sink", "ok"
        )
        _ok, text = self.verdict(root)
        self.assertIn("every `import` sits alone on its physical line", text)

    def test_a_commented_import_is_not_counted(self) -> None:
        """Comments are blanked before the count, so prose cannot trip the guard."""
        root = self.tree_with(
            "import IsingModel.Inequalities.Safe -- import IsingModel.Concrete.Sink", "comment"
        )
        _ok, text = self.verdict(root)
        self.assertIn("every `import` sits alone on its physical line", text)


# --------------------------------------------------------------------------
# The clean fixture, and T1/T1b -- the canaries
# --------------------------------------------------------------------------


class CleanTreeTest(TreeHarness):
    """The unmutated fixture must pass; otherwise every canary is meaningless."""

    def test_the_unmutated_tree_passes(self) -> None:
        """A checker that always fails is caught here."""
        ok, text = self.verdict(self.tree())
        self.assertTrue(ok, text)
        self.assertIn("PASS: import-DAG contract satisfied", text)

    def test_the_unmutated_tree_has_no_enforced_violation(self) -> None:
        """Each enforced rule is clean on the fixture."""
        report = self.report(self.tree())
        self.assertEqual({rule_id: len(edges) for rule_id, edges in report.violations.items()},
                         {rule.rule_id: 0 for rule in contract.RULES})

    def test_every_layer_is_populated(self) -> None:
        """The fixture exercises all six zones, not a convenient subset."""
        report = self.report(self.tree())
        for layer in contract.LAYERS:
            self.assertGreater(report.layer_sizes[layer], 0, layer)

    def test_the_unranked_edge_is_reported_and_harmless(self) -> None:
        """The one ``L2 -> L4`` edge is INFO: reported, never a failure."""
        root = self.tree()
        report = self.report(root)
        self.assertEqual(
            report.info,
            [("IsingModel.Inequalities.Capstone", "IsingModel.Concrete.Sink")],
        )
        ok, text = self.verdict(root)
        self.assertTrue(ok)
        self.assertIn("IsingModel.Inequalities.Capstone -> IsingModel.Concrete.Sink", text)


#: One mutation per enforced rule: ``rule id -> (file, extra import, edge key)``.
#: Each target is a sink, so no mutation introduces an import cycle, and each
#: source sits in the rule's own layer.
CANARY_MUTATIONS: dict[str, tuple[str, str, str]] = {
    "R1": (
        "IsingModel/Analysis/Helper.lean",
        "import IsingModel.Concrete.Sink",
        "IsingModel.Analysis.Helper -> IsingModel.Concrete.Sink",
    ),
    "R2": (
        "IsingModel/Hamiltonian.lean",
        "import IsingModel.Inequalities.Sink",
        "IsingModel.Hamiltonian -> IsingModel.Inequalities.Sink",
    ),
    "R3": (
        "IsingModel/AmbientLattice/Ambient.lean",
        "import IsingModel.Concrete.Sink",
        "IsingModel.AmbientLattice.Ambient -> IsingModel.Concrete.Sink",
    ),
    "R6": (
        "IsingModel/Concrete/Lattice.lean",
        "import IsingModel.TransferMatrix.Sink",
        "IsingModel.Concrete.Lattice -> IsingModel.TransferMatrix.Sink",
    ),
}


class CanaryTest(TreeHarness):
    """T1/T1b: a forbidden reverse edge must fail, and be named."""

    def test_each_enforced_rule_fails_on_its_own_mutation(self) -> None:
        """One deliberately inserted reverse import per rule, each caught."""
        for rule_id, (path, extra, key) in CANARY_MUTATIONS.items():
            with self.subTest(rule=rule_id):
                root = self.tree({path: extra})
                report = self.report(root)
                self.assertEqual(
                    [edge.key for edge in report.violations[rule_id]], [key],
                    f"{rule_id} did not flag its canary edge",
                )
                ok, text = self.verdict(root)
                self.assertFalse(ok, text)
                self.assertIn(f"{rule_id} FAIL", text)
                self.assertIn("FAIL: import-DAG contract violated", text)

    def test_a_mutation_does_not_disturb_the_other_rules(self) -> None:
        """The report attributes each edge to one rule, not to all of them."""
        for rule_id, (path, extra, _key) in CANARY_MUTATIONS.items():
            with self.subTest(rule=rule_id):
                report = self.report(self.tree({path: extra}))
                for other in contract.RULES:
                    if other.rule_id != rule_id:
                        self.assertEqual(report.violations[other.rule_id], [], other.rule_id)

    def test_the_reverse_of_a_forbidden_edge_stays_legal(self) -> None:
        """Direction, not adjacency: the mirror import of the R3 canary passes.

        Without this, a checker that flagged *every* edge between ``L3_AMBIENT``
        and ``L4_LATTICE`` would satisfy every other assertion in this class.
        """
        root = self.tree({"IsingModel/Concrete/Sink.lean": "import IsingModel.AmbientLattice.Sink"})
        ok, text = self.verdict(root)
        self.assertTrue(ok, text)


class RuleTableTest(unittest.TestCase):
    """The rule table itself, pinned so that a dropped rule cannot hide."""

    def test_the_enforced_rule_set_is_pinned(self) -> None:
        """Adding or removing an enforced rule is an explicit, reviewed edit."""
        self.assertEqual([rule.rule_id for rule in contract.RULES], ["R1", "R2", "R3", "R6"])

    def test_every_enforced_rule_has_a_canary(self) -> None:
        """A new rule without a mutation proving it can fail is not enforced."""
        self.assertEqual(
            sorted(CANARY_MUTATIONS), sorted(rule.rule_id for rule in contract.RULES)
        )

    def test_each_rule_forbids_exactly_the_complement_of_its_allowed_set(self) -> None:
        """The rules and the allowed-direction table cannot drift apart."""
        for rule in contract.RULES:
            self.assertEqual(
                rule.forbidden, frozenset(contract.LAYERS) - contract.ALLOWED[rule.source]
            )
            self.assertTrue(rule.forbidden, f"{rule.rule_id} forbids nothing")

    def test_the_unranked_zone_forbids_nothing(self) -> None:
        """``L2_THEORY`` is deliberately unranked, and no rule enforces it."""
        self.assertEqual(contract.ALLOWED[contract.L2_THEORY], frozenset(contract.LAYERS))
        self.assertNotIn(contract.L2_THEORY, [rule.source for rule in contract.RULES])
        self.assertEqual(contract.INFO_SOURCE, contract.L2_THEORY)


# --------------------------------------------------------------------------
# T2 -- umbrella pass-through
# --------------------------------------------------------------------------


class PassThroughTest(TreeHarness):
    """Umbrellas stay importable, but cannot launder a forbidden edge."""

    UMBRELLA = "IsingModel/Inequalities/Umbrella.lean"

    def test_an_umbrella_re_exporting_only_theory_is_legal(self) -> None:
        """The supported case: ``L3_AMBIENT`` imports an ``L2_THEORY`` umbrella."""
        root = self.tree()
        graph = contract.load_graph(root)
        self.assertIn("IsingModel.Inequalities.Umbrella", graph.aggregators)
        self.assertIn(
            "IsingModel.Inequalities.Umbrella",
            graph.imports["IsingModel.AmbientLattice.Ambient"],
        )
        ok, text = self.verdict(root)
        self.assertTrue(ok, text)

    def test_an_umbrella_cannot_launder_a_forbidden_edge(self) -> None:
        """The same import is flagged once the umbrella re-exports ``L4_LATTICE``."""
        root = self.tree({self.UMBRELLA: "import IsingModel.Concrete.Sink"})
        report = self.report(root)
        self.assertEqual(
            [edge.key for edge in report.violations["R3"]],
            ["IsingModel.AmbientLattice.Ambient -> IsingModel.Concrete.Sink"],
        )
        ok, text = self.verdict(root)
        self.assertFalse(ok, text)
        self.assertIn("(via IsingModel.Inequalities.Umbrella)", text)

    def test_an_aggregator_is_never_a_violation_source(self) -> None:
        """The umbrella itself is an index, so it is not blamed for the edge."""
        root = self.tree({self.UMBRELLA: "import IsingModel.Concrete.Sink"})
        report = self.report(root)
        for key in self.violation_keys(report):
            self.assertFalse(key.startswith("IsingModel.Inequalities.Umbrella "), key)

    def test_an_aggregator_is_never_an_info_source(self) -> None:
        """An umbrella's own downward re-export is an index entry, not a signal."""
        report = self.report(self.tree({self.UMBRELLA: "import IsingModel.Concrete.Sink"}))
        self.assertNotIn(
            ("IsingModel.Inequalities.Umbrella", "IsingModel.Concrete.Sink"), report.info
        )

    def test_expansion_reaches_through_a_chain_of_umbrellas(self) -> None:
        """Two umbrellas in a row hide the target no better than one."""
        root = self.tree(
            {
                self.UMBRELLA: "import IsingModel.AmbientLattice",
                "IsingModel/AmbientLattice.lean": "import IsingModel.Concrete.Lattice",
            }
        )
        report = self.report(root)
        self.assertIn(
            "IsingModel.AmbientLattice.Ambient -> IsingModel.Concrete.Lattice",
            [edge.key for edge in report.violations["R3"]],
        )

    def test_expansion_terminates_on_a_cycle(self) -> None:
        """Cheap insurance: a malformed fixture must not hang the suite."""
        root = self.tree(
            {
                self.UMBRELLA: "import IsingModel.AmbientLattice",
                "IsingModel/AmbientLattice.lean": "import IsingModel.Inequalities.Umbrella",
            }
        )
        graph = contract.load_graph(root)
        self.assertEqual(contract.resolve_target(graph, "IsingModel.Inequalities.Umbrella"),
                         {"IsingModel.Inequalities.Theory", "IsingModel.AmbientLattice.Ambient"})


# --------------------------------------------------------------------------
# T5 -- the baseline cannot rot
# --------------------------------------------------------------------------


class BaselineTest(TreeHarness):
    """The one structural risk: an allowlist that outlives its cause."""

    R3 = CANARY_MUTATIONS["R3"]
    ANNOTATED = f"{R3[2]}  # owner: someone  # issue: #4833\n"

    def test_a_violation_absent_from_the_baseline_fails(self) -> None:
        """(b) The default: an unlisted inversion is a failure."""
        ok, _text = self.verdict(self.tree({self.R3[0]: self.R3[1]}))
        self.assertFalse(ok)

    def test_an_annotated_baseline_entry_suppresses_its_own_edge(self) -> None:
        """The mechanism works at all -- otherwise (a) and (c) are vacuous."""
        ok, text = self.verdict(self.tree({self.R3[0]: self.R3[1]}), self.ANNOTATED)
        self.assertTrue(ok, text)
        self.assertIn("[baselined]", text)
        self.assertIn("(1 baselined)", text)

    def test_a_baseline_entry_for_a_vanished_edge_fails(self) -> None:
        """(a) The stale-entry check: the allowlist cannot outlive its cause."""
        ok, text = self.verdict(self.tree(), self.ANNOTATED)
        self.assertFalse(ok, text)
        self.assertIn("stale baseline entry", text)

    def test_a_baseline_entry_without_an_owner_fails(self) -> None:
        """(c) An unowned entry is a silencer, not an exception."""
        ok, text = self.verdict(
            self.tree({self.R3[0]: self.R3[1]}), f"{self.R3[2]}  # issue: #4833\n"
        )
        self.assertFalse(ok, text)
        self.assertIn("missing `# owner:", text)

    def test_a_baseline_entry_without_an_issue_fails(self) -> None:
        """An exception with no tracker is an exception nobody will remove."""
        ok, text = self.verdict(
            self.tree({self.R3[0]: self.R3[1]}), f"{self.R3[2]}  # owner: someone\n"
        )
        self.assertFalse(ok, text)
        self.assertIn("missing `# issue:", text)

    def test_annotation_look_alikes_do_not_count(self) -> None:
        """The fields are matched structurally, not by substring presence.

        An independent review found that ``# notowner: x  # noissue: 1`` and an
        empty ``# owner:`` both satisfied a substring test, so an edge could be
        silenced with no owner and no tracker at all.
        """
        cases = {
            "look-alike labels": "# notowner: someone  # noissue: 4833",
            "empty owner": "# owner:  # issue: #4833",
            "empty issue": "# owner: someone  # issue:",
            "non-numeric issue": "# owner: someone  # issue: TODO",
            "issue without a number sign": "# owner: someone  # issue: 4833",
            "placeholder owner": "# owner: TODO  # issue: #4833",
            "placeholder owner plus a word": "# owner: TODO x  # issue: #4833",
            "punctuation for an owner": "# owner: @  # issue: #4833",
            "issue zero": "# owner: someone  # issue: #0",
            "issue with leading zeros": "# owner: someone  # issue: #007",
            "no annotation at all": "",
        }
        for label, annotation in cases.items():
            with self.subTest(case=label):
                ok, text = self.verdict(
                    self.tree({self.R3[0]: self.R3[1]}), f"{self.R3[2]}  {annotation}\n"
                )
                self.assertFalse(ok, f"{label} was accepted:\n{text}")

    def test_a_fully_annotated_entry_still_works(self) -> None:
        """Anti-vacuity for the case above: real annotations are accepted."""
        for annotation in ("# owner: someone  # issue: #4833", "# owner: @phasetr  # issue: #1"):
            with self.subTest(annotation=annotation):
                _entries, errors = contract.parse_baseline(f"{self.R3[2]}  {annotation}\n")
                self.assertEqual(errors, [])

    def test_a_baseline_entry_suppresses_only_its_own_edge(self) -> None:
        """An allowlisted edge does not amnesty the rest of its rule."""
        root = self.tree({self.R3[0]: self.R3[1], "IsingModel/Analysis/Helper.lean":
                          CANARY_MUTATIONS["R1"][1]})
        ok, text = self.verdict(root, self.ANNOTATED)
        self.assertFalse(ok, text)
        self.assertIn("R1 FAIL", text)
        self.assertIn("R3 PASS", text)

    def test_comments_and_blank_lines_are_ignored(self) -> None:
        """The shipped file is all comments; it must parse as an empty baseline."""
        entries, errors = contract.parse_baseline(contract.BASELINE_FILE.read_text("utf-8"))
        self.assertEqual((entries, errors), ({}, []))

    def test_a_malformed_line_fails(self) -> None:
        """A typo must be loud, not silently dropped."""
        _entries, errors = contract.parse_baseline("IsingModel.A  # owner: x  # issue: #1\n")
        self.assertEqual(len(errors), 1)
        self.assertIn("not an `importer -> imported` pair", errors[0])

    def test_a_duplicate_entry_fails(self) -> None:
        """Two owners for one edge means nobody owns it."""
        line = self.ANNOTATED
        _entries, errors = contract.parse_baseline(line + line)
        self.assertTrue(any("duplicate" in message for message in errors), errors)

    def test_the_emitted_baseline_names_the_right_edges(self) -> None:
        """``--baseline`` derives the edge set deterministically from the tree."""
        report = self.report(self.tree({self.R3[0]: self.R3[1]}))
        entries, _errors = contract.parse_baseline(contract.format_baseline(report.violations))
        self.assertEqual(sorted(entries), [self.R3[2]])

    def test_the_emitted_baseline_does_not_validate_as_written(self) -> None:
        """The skeleton carries placeholders, so it cannot be committed as-is.

        ``--baseline`` derives the *edges*; assigning an owner and a tracker is a
        human decision, and an emitted file that passed unchanged would make the
        annotation requirement ceremonial.
        """
        report = self.report(self.tree({self.R3[0]: self.R3[1]}))
        _entries, errors = contract.parse_baseline(contract.format_baseline(report.violations))
        self.assertTrue(errors, "the emitted skeleton validated without being filled in")


# --------------------------------------------------------------------------
# T6 -- anti-scope
# --------------------------------------------------------------------------


class AntiScopeTest(TreeHarness):
    """The checker must stay a direction checker, and nothing else."""

    #: Words whose appearance in the report would mean the tool started
    #: answering a question the issue explicitly rules out.
    BANNED_REPORT_WORDS = (
        "quota", "budget", "seconds", "elapsed", "critical path", "build time",
        "path depth", "too many", "redundant", "unnecessary", "unused import",
        "delete", "remove ", "shake",
    )

    def test_the_report_contains_no_out_of_scope_field(self) -> None:
        """No file-count, path-depth, build-time, deletion or shake verdict."""
        _ok, text = self.verdict(self.tree())
        lowered = text.lower()
        for word in self.BANNED_REPORT_WORDS:
            self.assertNotIn(word, lowered, f"out-of-scope report field: {word!r}")

    def test_a_failing_report_contains_no_out_of_scope_field(self) -> None:
        """The failure path is where a "fix it by deleting" hint would appear."""
        path, extra, _key = CANARY_MUTATIONS["R3"]
        _ok, text = self.verdict(self.tree({path: extra}))
        lowered = text.lower()
        for word in self.BANNED_REPORT_WORDS:
            self.assertNotIn(word, lowered, f"out-of-scope report field: {word!r}")

    def test_info_edges_cannot_change_the_verdict(self) -> None:
        """Unranked edges are a signal; adding many of them changes nothing."""
        base_ok, _text = self.verdict(self.tree())
        extra = "\n".join(f"import IsingModel.Concrete.Sink{i}" for i in range(20))
        files = dict(self.files)
        files["IsingModel/Inequalities/Capstone.lean"] = (
            extra + "\n" + files["IsingModel/Inequalities/Capstone.lean"]
        )
        for i in range(20):
            files[f"IsingModel/Concrete/Sink{i}.lean"] = f"theorem sink{i} : True := trivial\n"
        root = materialize(files, self.root / "info")
        report = self.report(root)
        self.assertEqual(len(report.info), 21)
        ok, _text = self.verdict(root)
        self.assertEqual(ok, base_ok)

    def test_module_count_cannot_change_the_verdict(self) -> None:
        """No file-count or path-depth quota: growth alone is never a failure."""
        files = dict(self.files)
        for i in range(50):
            deep = "/".join(f"Deep{j}" for j in range(6))
            files[f"IsingModel/Inequalities/{deep}/Padding{i}.lean"] = (
                f"theorem padding{i} : True := trivial\n"
            )
        ok, _text = self.verdict(materialize(files, self.root / "padding"))
        self.assertTrue(ok)

    def test_the_checker_measures_no_time_and_runs_no_tool(self) -> None:
        """Anti-scope pinned at the source level, not only in the output."""
        source = (SCRIPT_DIR / "import_dag_contract.py").read_text(encoding="utf-8")
        for banned in ("import time", "import subprocess", "perf_counter", "noshake"):
            self.assertNotIn(banned, source, banned)


# --------------------------------------------------------------------------
# T7 -- the real tree
# --------------------------------------------------------------------------


class RealTreeTest(unittest.TestCase):
    """The delivered verdict on ``IsingModel/``, and the ratchet around it."""

    @classmethod
    def setUpClass(cls) -> None:
        cls.report = contract.build_report()
        cls.baseline, cls.baseline_errors = contract.read_baseline()

    def test_the_scan_is_not_vacuous(self) -> None:
        """A collapsed graph builder would make every assertion below trivial."""
        self.assertGreater(len(self.report.graph.modules), REAL_MODULE_FLOOR)
        self.assertGreater(len(self.report.graph.aggregators), 0)
        self.assertEqual(
            sum(self.report.layer_sizes.values()), len(self.report.graph.modules)
        )

    def test_the_contract_passes_on_the_current_tree(self) -> None:
        """The delivered state: every enforced rule clean, baseline empty."""
        self.assertEqual(self.baseline_errors, [])
        self.assertEqual(self.report.unmatched_baseline, [])
        self.assertEqual(self.report.enforced_count, len(self.baseline))
        self.assertEqual(len(self.baseline), 0)

    def test_every_import_in_the_library_is_readable(self) -> None:
        """No physical line in ``IsingModel/`` hides a second ``import``."""
        self.assertEqual(self.report.malformed_imports, [])

    def test_the_cli_exits_zero(self) -> None:
        """End to end, through ``main`` and the shipped baseline file."""
        buffer = io.StringIO()
        with contextlib.redirect_stdout(buffer):
            code = contract.main([])
        self.assertEqual(code, 0, buffer.getvalue())

    def test_the_unranked_edge_count_stays_under_its_ceiling(self) -> None:
        """A ratchet, not a quota: INFO never affects the exit status.

        Measured at :data:`INFO_CEILING` on the delivering commit.  Raising the
        number must be a reviewed edit, but unrelated module additions must not
        turn the suite red, hence a ceiling rather than an equality.
        """
        self.assertLessEqual(len(self.report.info), INFO_CEILING)
        self.assertGreater(len(self.report.info), 0, "the INFO channel went silent")

    def test_every_layer_is_populated_on_the_real_tree(self) -> None:
        """A layer that empties out means a tagging rule stopped matching."""
        for layer in contract.LAYERS:
            self.assertGreater(self.report.layer_sizes[layer], 0, layer)

    def test_the_relocated_bridge_lemma_is_where_the_contract_needs_it(self) -> None:
        """``boltzmannWeightJ_uniform_eq`` is what R3 was failing on before.

        Pinned here because the checker cannot see declarations: if the lemma
        moves back into a cubic-box file, R3 regresses and this test says why.
        """
        home = contract.REPO_ROOT / "IsingModel" / "Inequalities" / "FKGInhomogeneous.lean"
        self.assertIn("theorem boltzmannWeightJ_uniform_eq", home.read_text(encoding="utf-8"))


def run_suite() -> int:
    """Run every test. Return ``0`` on success, ``1`` otherwise."""
    loader = unittest.TestLoader()
    suite = loader.loadTestsFromModule(sys.modules[__name__])
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    return 0 if result.wasSuccessful() else 1


if __name__ == "__main__":
    sys.exit(run_suite())

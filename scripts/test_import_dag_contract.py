#!/usr/bin/env python3
"""Tests for the import-DAG layer contract (``scripts/import_dag_contract.py``).

The contract is worth exactly as much as the proof that it can fail.  The suite
is therefore built around canaries: :class:`CanaryTest` mutates a synthetic tree
once per enforced rule and requires the checker to name that exact edge, and
:meth:`RuleTableTest.test_every_enforced_rule_has_a_canary` requires a canary to
exist for every rule in :data:`import_dag_contract.RULES`, so a rule that is
silently dropped from -- or quietly added to -- the table cannot stay green.

Every structural fixture is synthetic (``scripts/testdata/import_dag_contract/``),
so no test can be repaired by editing ``IsingModel/``.  The assertions that do
read the real repository are :class:`RealTreeTest`, which pins the delivered
verdict, the anti-scope checks that read this checker's own source, and
:class:`CIWiringTest`, which pins the fact that CI actually runs the contract.
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
    # Declarations spelled with no punctuation at all, so every one of their
    # words satisfies the scaffolding argument class.  These are the shapes that
    # can ride along on a multi-argument `open` or `universe` line.
    "universe u inductive Hidden",
    "open Nat structure Hidden",
    "open Nat class Hidden",
    "open Nat deriving instance Repr for Nat",
    "inductive Hidden",
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

    #: Bodies that declare nothing.  They must be recognised as umbrellas, both
    #: as anti-vacuity for the sweep above and because an unrecognised umbrella
    #: hides an inversion of its own (see :class:`AggregatorOracleTest`).
    UMBRELLA_FORMS = (
        "/-! A pure re-export index. -/",
        "namespace Foo\nopen Nat\nvariable {V : Type*}\nend Foo",
        "namespace Foo\nsection\nopen scoped Bar\nuniverse u\nend\nend Foo",
    )

    def test_a_genuine_umbrella_in_the_same_position_is_not_a_source(self) -> None:
        """Anti-vacuity: the sweep above must not be flagging every module."""
        for index, body in enumerate(self.UMBRELLA_FORMS):
            with self.subTest(form=body.splitlines()[0]):
                root = self.tree_with(body, len(DECLARATION_FORMS) + index)
                graph = contract.load_graph(root)
                self.assertIn("IsingModel.AmbientLattice.Ambient", graph.aggregators)
                report = contract.build_report(root=root, baseline_path=root / "none.txt")
                self.assertEqual(report.violations["R3"], [])


class CommentLexerTest(unittest.TestCase):
    """Comment stripping decides what the classifier sees, so it is pinned here.

    Lean's block comments nest.  A non-greedy ``/-.*?-/`` closes at the first
    ``-/`` and leaves the remainder of a nested comment behind as apparent code,
    which demotes a genuine umbrella and hides an ``L3 -> umbrella -> L4``
    inversion -- the failure an independent review reproduced.
    """

    def code(self, text: str) -> str:
        """Return the comment-stripped text with whitespace collapsed."""
        return " ".join(contract.strip_comments(text).split())

    def test_nested_block_comments_are_consumed_whole(self) -> None:
        """The residue of the inner comment must not survive as code."""
        self.assertEqual(self.code("/- a /- b -/ c -/"), "")
        self.assertEqual(self.code("/- /- /- deep -/ -/ -/"), "")
        self.assertEqual(self.code("/- /- x -/ -/ theorem d"), "theorem d")

    def test_a_line_comment_inside_a_block_comment_is_inert(self) -> None:
        """``--`` must not start a line comment while inside ``/- ... -/``."""
        self.assertEqual(self.code("/- -- not a line comment\n-/ theorem d"), "theorem d")

    def test_a_block_opener_inside_a_line_comment_is_inert(self) -> None:
        """``/-`` after ``--`` must not swallow the rest of the file."""
        self.assertEqual(self.code("-- /- not a block\ntheorem d"), "theorem d")

    def test_a_block_opener_inside_a_string_is_inert(self) -> None:
        """A string literal is not a comment, escapes included."""
        self.assertEqual(self.code('def s := "/- not a comment"\ntheorem d'), 'def s := "/- not a comment" theorem d')
        self.assertEqual(self.code('def s := "a \\" /- b"\ntheorem d'), 'def s := "a \\" /- b" theorem d')

    def test_the_line_count_is_preserved(self) -> None:
        """The readability guard reads raw lines by index, so lines must align."""
        for text in (
            "import A\n/- one\ntwo\nthree -/\ntheorem d\n",
            "/- a /- b\nc -/ d -/\ntheorem e\n",
            "-- x\n-- y\ntheorem z\n",
        ):
            with self.subTest(text=text.splitlines()[0]):
                self.assertEqual(
                    len(contract.strip_comments(text).splitlines()), len(text.splitlines())
                )


class AggregatorOracleTest(unittest.TestCase):
    """The umbrella set, re-derived on the real tree by an independent parser.

    The classification has to be right, not merely conservative: calling a real
    module an umbrella exempts it as a violation source, and calling an umbrella
    a real module hides an ``L3 -> U -> L4`` inversion behind an allowed
    ``L3 -> L2`` edge and an unranked ``L2 -> L4`` one.  Two independent reviews
    broke earlier one-sided arguments, so the property is measured instead of
    argued: ``dead_candidate_scan`` is a separately written declaration parser in
    this repository, and the two must agree about which of the ~1900 modules
    declare nothing.
    """

    @classmethod
    def setUpClass(cls) -> None:
        import dead_candidate_scan as dcs  # noqa: PLC0415  (slow import, real tree)

        cls.declaring = {
            contract.REPO_ROOT.joinpath(decl.file).with_suffix("").relative_to(
                contract.REPO_ROOT
            ).as_posix().replace("/", ".")
            for decl in dcs.load_tree().decls
        }
        cls.graph = contract.load_graph()

    def test_the_two_parsers_agree_on_which_modules_declare_nothing(self) -> None:
        """No aggregator declares anything, per the other parser."""
        declaring_aggregators = sorted(self.graph.aggregators & self.declaring)
        self.assertEqual(declaring_aggregators, [], "umbrella holding a declaration")

    def test_no_declaration_free_importer_is_left_out(self) -> None:
        """Conversely, every declaration-free module with imports is an umbrella."""
        missed = sorted(
            module
            for module in self.graph.modules
            if module not in self.declaring
            and module not in self.graph.aggregators
            and self.graph.imports.get(module)
        )
        self.assertEqual(missed, [], "declaration-free module not recognised as an umbrella")

    def test_the_oracle_is_not_vacuous(self) -> None:
        """Both sides have to be populated for the agreement to mean anything."""
        self.assertGreater(len(self.graph.aggregators), 50)
        self.assertGreater(len(self.declaring), 1000)

    def test_no_umbrella_mentions_a_declaration_command_anywhere(self) -> None:
        """The coarse sieve, applied to the real tree rather than to fixtures.

        The oracle above and the line classifier share one weakness -- both read
        the *leading* command -- so an independent review found
        ``universe u inductive Hidden`` slipping past both.  This assertion has a
        different shape again: no umbrella's file may contain a declaration or
        modifier keyword as a standalone token at all, wherever it sits.
        """
        offenders = sorted(
            module
            for module in self.graph.aggregators
            if contract._HIDDEN_COMMAND_RE.search(
                contract.strip_comments(contract.module_source(module, contract.REPO_ROOT) or "")
            )
        )
        self.assertEqual(offenders, [], "umbrella mentioning a declaration command")

    def test_the_hidden_command_list_is_not_empty(self) -> None:
        """Emptying the sieve's pattern is the cheapest way to silence it."""
        for keyword in ("inductive", "structure", "class", "deriving", "theorem", "def"):
            self.assertTrue(
                contract._HIDDEN_COMMAND_RE.search(f"universe u {keyword} Hidden"), keyword
            )
        self.assertIsNone(contract._HIDDEN_COMMAND_RE.search("open Finset Real"))
        self.assertIsNone(contract._HIDDEN_COMMAND_RE.search("import IsingModel.ClassicalSpin"))


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

    #: ``(raw line, readable)``.  The unreadable half is the accumulated list of
    #: shapes successive reviews produced, each legal Lean and each invisible to
    #: ``leaf_audit``; the readable half is the anti-vacuity floor.
    IMPORT_LINE_CASES = (
        ("import IsingModel.Foo", True),
        ("import IsingModel", True),
        ("import Mathlib.Order.Basic", True),
        ("import IsingModel.Foo -- trailing line comment", True),
        ("import IsingModel.Foo /- trailing block comment -/", True),
        ("import", False),
        ("  import IsingModel.Foo", False),
        ("\timport IsingModel.Foo", False),
        ("import IsingModel.A import IsingModel.B", False),
        ("import Mathlib.Order.Basic import IsingModel.B", False),
        ("import/- sep -/ IsingModel.Foo", False),
        ("import /-x-/IsingModel.Foo", False),
        ("import /- a -/ /- b -/ IsingModel.Foo", False),
        # Guillemet-escaped identifiers: legal Lean, and doubly dangerous --
        # either the scanner captures nothing, or it captures a spelling that
        # matches no real module and so lands in the default layer.
        ("import «IsingModel».Concrete.Foo", False),
        ("import IsingModel.«Concrete».Foo", False),
        ("import «IsingModel.Concrete.Foo»", False),
    )

    def test_readability_is_an_equivalence_with_the_scanner(self) -> None:
        """Each accumulated shape, checked directly against the two views.

        Enumerating bad shapes was a losing game -- five reviews produced five
        more -- so the guard compares what Lean sees on the stripped line with
        what ``leaf_audit``'s own regex extracts from the raw one.  These cases
        pin that comparison; the unreadable ones all compile under
        ``lake env lean``.
        """
        for raw, readable in self.IMPORT_LINE_CASES:
            with self.subTest(line=raw):
                self.assertEqual(
                    contract.line_is_readable(raw, contract.strip_comments(raw)), readable
                )

    def test_an_escaped_module_name_fails(self) -> None:
        """``import «IsingModel».Concrete.Foo`` compiles and hides its edge."""
        root = self.tree_with("import «IsingModel».Concrete.Sink", "escaped")
        graph = contract.load_graph(root)
        self.assertEqual(
            graph.imports.get("IsingModel.AmbientLattice.Ambient", set()), set(),
            "the scanner unexpectedly saw the import; this test is now vacuous",
        )
        ok, text = self.verdict(root)
        self.assertFalse(ok, text)

    def test_every_real_import_argument_is_canonical(self) -> None:
        """Anti-vacuity for the canonical-spelling rule on the real library.

        A rule that rejected ordinary module names would show up as a wall of
        failures rather than as silence, but only if something reads the real
        tree; this is that something.
        """
        graph = contract.load_graph()
        self.assertGreater(len(graph.modules), REAL_MODULE_FLOOR)
        for module in graph.modules:
            self.assertRegex(module, contract._CANONICAL_MODULE_RE)

    def test_a_comment_inside_the_import_command_fails(self) -> None:
        """``import /-x-/Foo``: the scanner's capture must start at the module."""
        root = self.tree_with("import /-x-/IsingModel.Concrete.Sink", "inline")
        graph = contract.load_graph(root)
        self.assertEqual(
            graph.imports.get("IsingModel.AmbientLattice.Ambient", set()), set(),
            "the scanner unexpectedly saw the import; this test is now vacuous",
        )
        ok, text = self.verdict(root)
        self.assertFalse(ok, text)

    def test_a_comment_between_import_and_module_fails(self) -> None:
        """``import/- c -/ Foo`` is legal Lean and unreadable to the scanner.

        The guard has to judge the *raw* line: normalising the comment away
        first turns this into a canonical import that validates, while the
        scanner -- which sees the raw text and needs whitespace after the
        keyword -- still records nothing.
        """
        root = self.tree_with("import/- separator -/ IsingModel.Concrete.Sink", "commented")
        graph = contract.load_graph(root)
        self.assertEqual(
            graph.imports.get("IsingModel.AmbientLattice.Ambient", set()), set(),
            "the scanner unexpectedly saw the import; this test is now vacuous",
        )
        ok, text = self.verdict(root)
        self.assertFalse(ok, text)

    def test_a_multiline_import_fails(self) -> None:
        """Lean lets the module name sit on the line after ``import``.

        The bare ``import`` line carries a single token with nothing after it, so
        the guard's trailing boundary has to be ``\\b`` rather than whitespace.
        """
        root = self.tree_with("import\n IsingModel.Concrete.Sink", "multiline")
        graph = contract.load_graph(root)
        self.assertEqual(
            graph.imports.get("IsingModel.AmbientLattice.Ambient", set()), set(),
            "the scanner unexpectedly saw the split import; this test is now vacuous",
        )
        ok, text = self.verdict(root)
        self.assertFalse(ok, text)

    def test_an_indented_import_fails(self) -> None:
        """Lean accepts a leading space; the scanner's ``^import`` anchor does not.

        This case carries only *one* ``import`` token, so a guard that merely
        counted duplicates would wave it through -- which is what it did until
        this test was added.
        """
        root = self.tree_with("  import IsingModel.Concrete.Sink", "indented")
        graph = contract.load_graph(root)
        self.assertEqual(
            graph.imports.get("IsingModel.AmbientLattice.Ambient", set()), set(),
            "the scanner unexpectedly saw the indented import; this test is now vacuous",
        )
        ok, text = self.verdict(root)
        self.assertFalse(ok, text)
        self.assertIn("import IsingModel.Concrete.Sink", text)

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


# --------------------------------------------------------------------------
# T8 -- CI wiring
# --------------------------------------------------------------------------

#: Workflow expected to run the contract on every pull request (Issue #4833).
WORKFLOW_FILE = contract.REPO_ROOT / ".github" / "workflows" / "lean_action_ci.yml"

#: Job of that workflow which must do it.
WORKFLOW_JOB = "import-dag-contract"

#: Command word and script of the checker itself, as CI spells them.
CONTRACT_COMMAND = ("python3", "scripts/import_dag_contract.py")

#: The same, for this suite run standalone.
SUITE_COMMAND = ("python3", "scripts/test_import_dag_contract.py")

#: The gate's exact invocation.  ``--baseline`` exits ``0`` by construction and
#: ``--help`` checks nothing, so neither can report an inversion; ``--self-test``
#: runs this suite, which is the *other* step.  Matching the whole argument list
#: rather than a prefix is also what rejects a trailing ``|| true``.
GATE_INVOCATION = (*CONTRACT_COMMAND, "--check")

#: Keys that would leave the pinned steps looking wired while changing what they
#: mean: ``if`` (GitHub reports a *skipped* job as successful),
#: ``continue-on-error`` (the exit status is discarded), ``shell`` (a custom
#: template decides what the exit status even is), ``with`` (``ref:`` would aim
#: checkout at another tree, so the gate would grade the wrong commit), ``env``
#: (a nested ``run`` key is an environment variable, not a command), and the
#: job-shape keys ``needs`` / ``strategy`` / ``defaults`` / ``<<``.
FORBIDDEN_KEYS = (
    "if", "continue-on-error", "shell", "with", "env", "needs", "strategy",
    "defaults", "container", "services", "<<",
)

#: The workflow, pinned in its entirety.
#:
#: Five review rounds broke every *partial* pin, each time from the part the
#: pin had argued was irrelevant: command prefixes lost to ``|| true`` and
#: ``--help``; job scope lost to a ``run`` key under ``env:`` and to
#: ``if : false`` respaced; a structural reader lost to a merge-key alias and
#: to ``with: ref:``; the job pinned verbatim lost to ``jobs: |`` and to a
#: duplicate header; the frame plus a coverage audit lost to a quoted scalar
#: opened in the *sibling* job, which swallows this one.
#:
#: The whole file is the one region needing no relevance argument, so that is
#: what is pinned.  **What this buys is one thing: every edit to CI shows up as
#: a diff in this file.**  It is a review tripwire, deliberately not more --
#: see :class:`CIWiringTest` for what it does not do.
PINNED_WORKFLOW = """\
name: Lean Action CI

on:
  push:
    branches: [main]
  pull_request:
  workflow_dispatch:

# Sets permissions of the GITHUB_TOKEN to allow deployment to GitHub Pages
permissions:
  contents: read # Read access to repository contents
  pages: write # Write access to GitHub Pages
  id-token: write # Write access to ID tokens

jobs:
  build:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v5
      - uses: leanprover/lean-action@v1
      - name: Completion-claim gate self-tests
        run: python3 scripts/test_completion_claim_gate.py
      - name: Live completion-claim adapter self-tests
        run: python3 scripts/test_completion_claim_live.py
      - name: Run GKS numerical tests
        run: lake exe GKSTest
      - name: Build sentinel property suite (Issue #888 Step P3)
        run: lake build test.IsingModel.SentinelProps
      # The gate's own tests run *before* the gate: `--full` only says whether
      # the current tree passes, which stays true when a check is weakened, so
      # the self tests are what actually defend V1-V4. Both suites are pure
      # Python (no lake, no network) and cost about 20 s and 80 s respectively.
      - name: Audit gate self-tests (test the gate, not just the tree)
        run: python3 scripts/audit_gate.py --self-test
      - name: Dead-candidate scanner self-tests
        run: python3 scripts/dead_candidate_scan.py --self-test
      - name: Audit gate (V1-V4 axiom/sorry/capstone/no-Japanese checks)
        run: python3 scripts/audit_gate.py --full

  # Architecture gate for Issue #4833: the import-DAG layer contract. It is a
  # separate job rather than another step of `build` because it needs no Lean
  # toolchain, so it reports an inversion in about a minute instead of behind
  # the Lean build -- and, more importantly, a red or cancelled Lean build can
  # then never mask an architecture violation. It is not (yet) a required
  # check; making it blocking is a separate governance decision.
  import-dag-contract:
    runs-on: ubuntu-latest
    timeout-minutes: 10
    permissions:
      contents: read
    steps:
      - uses: actions/checkout@v5
      # Same order as the audit gate above, for the same reason: `--check` only
      # says whether the current tree passes, which stays true when a rule is
      # weakened or dropped, so the suite's mutation canaries are what actually
      # defend R1/R2/R3/R6 (and its `CIWiringTest` defends these two steps).
      # Both commands are pure Python -- no lake, no network -- and cost about
      # 20 s and 5 s on a runner. NOTE: `CIWiringTest` pins THIS WHOLE FILE
      # byte for byte, so any edit here -- to either job -- must be mirrored
      # into `PINNED_WORKFLOW` in scripts/test_import_dag_contract.py.
      - name: Import-DAG contract self-tests (test the checker, not just the tree)
        run: python3 scripts/test_import_dag_contract.py
      - name: Import-DAG layer contract (R1/R2/R3/R6 direction rules)
        run: python3 scripts/import_dag_contract.py --check

  # NOTE: docs generation via `leanprover-community/docgen-action` has been
  # temporarily disabled because every main-push run takes ~1 hour and
  # CI queues backed up. Re-enable once the docgen step is accelerated
  # (e.g. by caching or by running on a schedule instead of every push).
  # See README / docs/index.md for user-facing notice.
  #
  # docs:
  #   if: github.event_name == 'push' && github.ref == 'refs/heads/main'
  #   needs: build
  #   runs-on: ubuntu-latest
  #   steps:
  #     - uses: actions/checkout@v5
  #     - uses: leanprover/lean-action@v1
  #     - uses: leanprover-community/docgen-action@main
  #       with:
  #         use-github-cache: false
"""


def yaml_indent(line: str) -> int:
    """Indentation width of ``line``."""
    return len(line) - len(line.lstrip())


def yaml_key(text: str) -> str | None:
    """Mapping key of already-stripped ``text``, or ``None`` if it has none."""
    if not text or text.startswith("#") or ":" not in text:
        return None
    key = text.split(":", 1)[0].strip().strip("\"'")
    return key or None


def content_lines(lines: list[str]) -> list[int]:
    """Indices of the lines that are neither blank nor a whole-line comment."""
    return [
        i for i, line in enumerate(lines)
        if line.strip() and not line.strip().startswith("#")
    ]


def block_indices(lines: list[str], header: int) -> list[int]:
    """Indices of ``header`` and everything nested under it."""
    indent = yaml_indent(lines[header])
    block = [header]
    for i in content_lines(lines):
        if i <= header:
            continue
        if yaml_indent(lines[i]) <= indent:
            break
        block.append(i)
    return block


class CIWiringTest(unittest.TestCase):
    """A gate nobody runs is not a gate.

    The workflow is pinned byte for byte, so removing, disabling or retargeting
    the CI job cannot happen without editing this file too.  The remaining
    assertions re-derive the wiring from the pinned copy -- the job is unique,
    its steps are this suite and then the tree gate in that order, no key
    changes what they mean, the trigger is an unfiltered ``pull_request:`` --
    which catches the coarse ways of gutting the gate while updating the pin to
    match.

    **Two things this deliberately does not claim.**  The derivation is not
    exhaustive and cannot be: whether a job really enforces anything depends on
    GitHub's semantics, not on the text, and an editor willing to change the
    workflow *and* this pin together can still find a dimension it does not
    model (``runs-on:`` a label no runner answers, dropping the checkout step,
    renaming the job).  That case is a review question, not a test question.
    Nor does this suite protect its own execution: it runs from the very job it
    pins, so it is a tripwire for edits, and only a required-status-check
    decision -- taken outside this repository -- makes the gate blocking.

    Deliberately brittle: touching the workflow at all turns this red until
    :data:`PINNED_WORKFLOW` is updated to match, which is the diff a reviewer
    sees.
    """

    @classmethod
    def setUpClass(cls) -> None:
        cls.actual = WORKFLOW_FILE.read_bytes()
        cls.lines = PINNED_WORKFLOW.splitlines()
        headers = [
            i for i in content_lines(cls.lines)
            if yaml_indent(cls.lines[i]) == 2
            and yaml_key(cls.lines[i].strip()) == WORKFLOW_JOB
        ]
        cls.job = [cls.lines[i] for i in block_indices(cls.lines, headers[0])] if headers else []
        cls.job_count = len(headers)

    def test_the_workflow_is_pinned_byte_for_byte(self) -> None:
        """Any edit to CI, anywhere in the file, has to be mirrored here.

        Compared as *bytes*: reading as text would normalise CRLF and let a
        re-encoded file compare equal to this pin while differing on disk.
        """
        self.assertEqual(self.actual.decode("utf-8"), PINNED_WORKFLOW)
        self.assertEqual(self.actual, PINNED_WORKFLOW.encode("utf-8"))

    def test_the_pinned_workflow_runs_the_gate_after_its_tests(self) -> None:
        """Updating the pin to match a gutted job must not be free.

        A smoke test over the coarse moves, not a proof of enforcement (see the
        class docstring): the job has to exist exactly once -- YAML keeps the
        last of two identical keys, so a duplicate header would be the one
        GitHub runs -- and its steps have to be this suite followed by the tree
        gate, with no key that changes what either one means.
        """
        self.assertEqual(self.job_count, 1, f"job {WORKFLOW_JOB!r} is not unique")
        commands = [
            tuple(line.strip()[len("run:") :].split())
            for line in self.job
            if yaml_key(line.strip()) == "run"
        ]
        self.assertEqual(commands, [SUITE_COMMAND, GATE_INVOCATION])
        keys = {yaml_key(line.strip().removeprefix("- ")) for line in self.job}
        for forbidden in FORBIDDEN_KEYS:
            self.assertNotIn(forbidden, keys, f"pinned job carries {forbidden!r}")

    def test_the_pinned_workflow_runs_on_every_pull_request(self) -> None:
        """A gate no pull request triggers enforces nothing.

        The trigger must be an unfiltered ``pull_request:``; a branch, path or
        event filter under it would silently exempt some pull requests.
        """
        on = [
            i for i in content_lines(self.lines)
            if yaml_indent(self.lines[i]) == 0 and self.lines[i] == "on:"
        ]
        self.assertEqual(len(on), 1, "no unique top-level `on:` key")
        triggers = block_indices(self.lines, on[0])
        pull_request = [
            i for i in triggers
            if yaml_indent(self.lines[i]) == 2
            and yaml_key(self.lines[i].strip()) == "pull_request"
        ]
        self.assertEqual(len(pull_request), 1, "no unique `pull_request:` trigger")
        self.assertEqual(
            block_indices(self.lines, pull_request[0]),
            [pull_request[0]],
            "`pull_request:` carries a filter",
        )


def run_suite() -> int:
    """Run every test. Return ``0`` on success, ``1`` otherwise."""
    loader = unittest.TestLoader()
    suite = loader.loadTestsFromModule(sys.modules[__name__])
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    return 0 if result.wasSuccessful() else 1


if __name__ == "__main__":
    sys.exit(run_suite())

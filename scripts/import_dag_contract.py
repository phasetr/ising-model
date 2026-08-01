#!/usr/bin/env python3
"""Import-DAG layer contract for the IsingModel Lean library (Issue #4833).

The library is a single Lake target whose 1900+ modules form one big import
DAG.  Nothing in the build system records *which direction* a dependency is
allowed to run in, so an inversion -- a general result reaching down into a
specialization -- costs nothing to introduce and is invisible afterwards.  This
script makes the intended direction executable.

What it is not
--------------
It is **not** a total order over directories.  A naive strict order over the 25
top-level directories reports ~40 violations, most of which are tagging
artifacts rather than inversions (``IsingModel/PhaseTransition/`` is entirely
``SimpleGraph``-generic despite its concrete-sounding name; ``SumModel.lean``
sits at the root but consumes ``FreeEnergy/SubgraphBounds.lean``).  The contract
therefore ranks only the zones whose direction is both semantically
load-bearing and empirically clean, and declares the rest explicitly unranked.

Layers
------
Six zones, assigned by longest-prefix match on the dotted module name (see
:data:`LAYER_PREFIXES` and :data:`L1_MODEL_MODULES`); the documented map is
``docs/architecture-import-layers.md``.

===============  ===========================================================
``L0_MATH``      mathlib-adjacent helpers with no Ising content
``L1_MODEL``     finite-volume model definitions over an arbitrary graph
``L2_THEORY``    graph-generic theory -- the default, deliberately unranked
``L3_AMBIENT``   the ambient/exhaustion *generality* layer
``L4_LATTICE``   the concrete Z^d lattice specialization
``L5_CHAIN``     the 1D chain / transfer-matrix vertical
===============  ===========================================================

Enforced rules
--------------
Only four directions are enforced (see :data:`RULES`):

====  =========================================================
R1    ``L0_MATH`` imports nothing outside ``L0_MATH``
R2    ``L1_MODEL`` imports only ``L0_MATH`` / ``L1_MODEL``
R3    ``L3_AMBIENT`` imports no ``L4_LATTICE`` / ``L5_CHAIN``
R6    ``L4_LATTICE`` does not import ``L5_CHAIN``
====  =========================================================

R3 is the invariant the issue is about: *generality must not depend on
specialization*.  The identifiers ``R4`` / ``R5`` are deliberately absent -- they
name the two ``L2_THEORY -> L4_LATTICE`` / ``L2_THEORY -> L5_CHAIN`` directions
that are reported as ``INFO`` and never enforced.  Enforcing them would
manufacture a 28-entry baseline and would implicitly demand a file-relocation
campaign, which is exactly the mechanical rewrite the issue forbids: many of
those edges are honest concrete capstones that merely live under a topic
directory, so the *file* is misfiled while the *edge* is correctly directed.

Aggregators
-----------
A module that declares nothing is an **aggregator** (a re-export umbrella): after
comment stripping, every line is ``import`` or namespace/section scaffolding.
The test is an allowlist of harmless commands rather than a list of declaration
keywords, because that direction fails closed -- a construct nobody thought of
leaves the module a real one.  The set is computed, never hand-listed, so new
umbrellas need no maintenance.  Aggregators are never violation *sources* --
they are indices, not generality code -- and as *targets* they are expanded
transitively to the first non-aggregator modules behind them.  Expansion rather
than exemption is what keeps a compatibility umbrella a fully supported public
import without letting it launder a reverse edge.

Baseline
--------
``scripts/import_dag_baseline.txt`` is an owner-annotated allowlist of edges
that are real inversions not yet fixed.  Every entry needs a real
``# owner: <name>`` and ``# issue: #<number>`` -- matched structurally, so a
look-alike or an empty value is a failure -- and an entry whose edge no longer
exists is itself a failure, so the allowlist cannot outlive its cause.  The
skeleton ``--baseline`` prints deliberately does *not* validate: the edges are
machine-derived but the ownership is a human decision.  A **tagging bug is fixed in the tagging
rules, never in the baseline**: a baseline entry means "genuine inversion,
scheduled"; using one to silence a mislabelled endpoint destroys that meaning.

Anti-scope (pinned by ``scripts/test_import_dag_contract.py``)
--------------------------------------------------------------
No file-count quota, no path-depth quota, no build-time or critical-path
measurement, no redundant-import verdict and no deletion suggestion.  The only
input to a verdict is the layer tag of the two endpoints of an edge.
``lake exe shake`` answers a different question ("is this import needed?") and
its output is never read here.

Usage
-----
    python3 scripts/import_dag_contract.py             # --check (default)
    python3 scripts/import_dag_contract.py --baseline  # emit baseline format
    python3 scripts/import_dag_contract.py --self-test # run the test suite

Exit code 0 iff every enforced rule is clean modulo the baseline and the
baseline itself is fresh; 1 otherwise.  ``INFO`` never affects the exit code.
"""

from __future__ import annotations

import argparse
import contextlib
import os
import re
import sys
from pathlib import Path
from typing import Iterator, NamedTuple

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent
BASELINE_FILE = SCRIPT_DIR / "import_dag_baseline.txt"

sys.path.insert(0, str(SCRIPT_DIR))

from leaf_audit import build_import_graph  # noqa: E402

# --------------------------------------------------------------------------
# Layer map
# --------------------------------------------------------------------------

L0_MATH = "L0_MATH"
L1_MODEL = "L1_MODEL"
L2_THEORY = "L2_THEORY"
L3_AMBIENT = "L3_AMBIENT"
L4_LATTICE = "L4_LATTICE"
L5_CHAIN = "L5_CHAIN"

LAYERS = (L0_MATH, L1_MODEL, L2_THEORY, L3_AMBIENT, L4_LATTICE, L5_CHAIN)

#: ``L1_MODEL`` is an exact list, not a prefix: the root directory holds three
#: different kinds of file (model core, concrete lattice, generic theory), so
#: "is at the root" is not a layer.
L1_MODEL_MODULES = frozenset(
    {
        "IsingModel.Basic",
        "IsingModel.Hamiltonian",
        "IsingModel.GibbsMeasure",
        "IsingModel.PartitionFunctionIso",
        "IsingModel.SumGraph",
        "IsingModel.RealTanhAux",
    }
)

#: Dotted prefixes, matched as ``m == p or m.startswith(p + ".")`` and resolved
#: longest-first.  Bare ``str.startswith`` is wrong here and the tree contains
#: live traps for it: ``IsingModel.LatticeExpSum`` would be captured by the
#: ``IsingModel.Lattice`` rule, and ``IsingModel.AmbientLatticeSumLogZ`` by the
#: ``IsingModel.AmbientLattice`` one.  Every prefix that needs to cover such a
#: sibling is therefore listed on its own line.
LAYER_PREFIXES: tuple[tuple[str, str], ...] = (
    ("IsingModel.Analysis", L0_MATH),
    ("IsingModel.Combinatorics", L0_MATH),
    ("IsingModel.AmbientLattice", L3_AMBIENT),
    ("IsingModel.AmbientLatticeSum", L3_AMBIENT),
    ("IsingModel.AmbientComplexAnalyticity", L3_AMBIENT),
    ("IsingModel.AmbientFKG", L3_AMBIENT),
    ("IsingModel.InfiniteVolume", L3_AMBIENT),
    ("IsingModel.Concrete", L4_LATTICE),
    ("IsingModel.Peierls", L4_LATTICE),
    ("IsingModel.PeierlsInfinite", L4_LATTICE),
    ("IsingModel.Lattice", L4_LATTICE),
    ("IsingModel.LatticeExpSum", L4_LATTICE),
    ("IsingModel.PolyDecay", L4_LATTICE),
    ("IsingModel.TransferMatrix", L5_CHAIN),
)

#: ``ALLOWED[importer]`` is the set of layers ``importer`` may import from.
#: ``L2_THEORY`` allows everything: it is the unranked default zone, and its
#: downward edges are surfaced as ``INFO`` instead.
ALLOWED: dict[str, frozenset[str]] = {
    L0_MATH: frozenset({L0_MATH}),
    L1_MODEL: frozenset({L0_MATH, L1_MODEL}),
    L2_THEORY: frozenset(LAYERS),
    L3_AMBIENT: frozenset({L0_MATH, L1_MODEL, L2_THEORY, L3_AMBIENT}),
    L4_LATTICE: frozenset({L0_MATH, L1_MODEL, L2_THEORY, L3_AMBIENT, L4_LATTICE}),
    L5_CHAIN: frozenset(LAYERS),
}


class Rule(NamedTuple):
    """An enforced rule: one importer layer and the layers it must not reach."""

    rule_id: str
    source: str
    forbidden: frozenset[str]
    summary: str


RULES: tuple[Rule, ...] = (
    Rule("R1", L0_MATH, frozenset(LAYERS) - ALLOWED[L0_MATH],
         "mathlib-adjacent helpers carry no Ising content"),
    Rule("R2", L1_MODEL, frozenset(LAYERS) - ALLOWED[L1_MODEL],
         "the model core is defined before any theory about it"),
    Rule("R3", L3_AMBIENT, frozenset(LAYERS) - ALLOWED[L3_AMBIENT],
         "generality must not depend on specialization"),
    Rule("R6", L4_LATTICE, frozenset(LAYERS) - ALLOWED[L4_LATTICE],
         "the lattice layer does not depend on the 1D chain vertical"),
)

#: The unranked directions, reported but never enforced.  Kept as data so the
#: report and the documentation cannot drift apart.
INFO_SOURCE = L2_THEORY
INFO_TARGETS = frozenset({L4_LATTICE, L5_CHAIN})


def layer_of(module: str) -> str:
    """Return the layer tag of ``module``; ``L2_THEORY`` when no rule matches.

    Prefix rules are resolved longest-first, and a prefix matches only a whole
    dotted component (``m == p`` or ``m.startswith(p + ".")``).
    """
    if module in L1_MODEL_MODULES:
        return L1_MODEL
    best_prefix = ""
    best_layer = L2_THEORY
    for prefix, layer in LAYER_PREFIXES:
        if module == prefix or module.startswith(prefix + "."):
            if len(prefix) > len(best_prefix):
                best_prefix, best_layer = prefix, layer
    return best_layer


# --------------------------------------------------------------------------
# Aggregator (re-export umbrella) classification
# --------------------------------------------------------------------------

_BLOCK_COMMENT_RE = re.compile(r"/-.*?-/", re.DOTALL)
_LINE_COMMENT_RE = re.compile(r"--.*$", re.MULTILINE)

#: The commands an umbrella may contain besides ``import``: namespace/section
#: scaffolding that declares nothing.  The test is an **allowlist**, never a
#: list of declaration keywords, because that direction fails closed: an
#: unrecognised construct (``unsafe def``, ``partial def``, ``alias``,
#: ``macro_rules``, a future keyword) leaves the module a real one and therefore
#: still a violation source.  A denylist of declaration openers fails *open* --
#: one keyword missing from it silently exempts the module.
_SCAFFOLDING_RE = re.compile(
    r"^\s*(?:import|namespace|end|section|open|universe|variable)\b"
)

#: ``open Foo in <decl>`` and ``set_option x in <decl>`` are command *wrappers*:
#: the line starts with allowlisted scaffolding but carries a declaration on the
#: same line.  Any scaffolding line containing the ``in`` combinator is
#: therefore rejected.
_IN_COMBINATOR_RE = re.compile(r"(?:^|\s)in(?:\s|$)")


def module_source(module: str, root: Path) -> str | None:
    """Return the source text of ``module`` under ``root``, or ``None``."""
    path = root / (module.replace(".", os.sep) + ".lean")
    try:
        return path.read_text(encoding="utf-8", errors="replace")
    except FileNotFoundError:
        return None


def is_aggregator(module: str, root: Path) -> bool:
    """Return whether ``module`` is a re-export umbrella (declares nothing).

    Comments are stripped first, so a ``/-! ... theorem foo ... -/`` module
    header cannot make an umbrella look declarative.  Every remaining non-blank
    line must then be allowlisted scaffolding (:data:`_SCAFFOLDING_RE`).

    A module whose file is missing is not an aggregator: an unresolvable target
    must not silently gain pass-through semantics.
    """
    text = module_source(module, root)
    if text is None:
        return False
    stripped = _LINE_COMMENT_RE.sub("", _BLOCK_COMMENT_RE.sub("", text))
    for line in stripped.splitlines():
        if not line.strip():
            continue
        if not _SCAFFOLDING_RE.match(line) or _IN_COMBINATOR_RE.search(line):
            return False
    return True


# --------------------------------------------------------------------------
# Graph construction
# --------------------------------------------------------------------------


@contextlib.contextmanager
def _chdir(target: Path) -> Iterator[None]:
    """Temporarily change the working directory (``leaf_audit`` scans ``.``)."""
    previous = Path.cwd()
    os.chdir(target)
    try:
        yield
    finally:
        os.chdir(previous)


class Graph(NamedTuple):
    """The tagged import graph of one source tree."""

    root: Path
    imports: dict[str, set[str]]
    modules: set[str]
    aggregators: frozenset[str]


def load_graph(root: Path = REPO_ROOT) -> Graph:
    """Build the tagged import graph of the tree rooted at ``root``.

    Import parsing is delegated to :func:`leaf_audit.build_import_graph`, the
    repository's single ``^import\\s+(IsingModel\\S*)`` scanner, so the contract
    can never disagree with the leaf audit about what the edges are.
    """
    with _chdir(root):
        imports, modules = build_import_graph()
    aggregators = frozenset(m for m in modules if is_aggregator(m, root))
    return Graph(root=root, imports=dict(imports), modules=modules, aggregators=aggregators)


def resolve_target(graph: Graph, target: str) -> set[str]:
    """Expand an aggregator ``target`` to the non-aggregator modules behind it.

    A non-aggregator resolves to itself.  Expansion is cycle-guarded even though
    Lean forbids import cycles, so a malformed fixture cannot hang the suite.
    """
    resolved: set[str] = set()
    seen: set[str] = set()
    stack = [target]
    while stack:
        node = stack.pop()
        if node in seen:
            continue
        seen.add(node)
        if node in graph.aggregators:
            stack.extend(child for child in graph.imports.get(node, ()) if child not in seen)
        else:
            resolved.add(node)
    return resolved


# --------------------------------------------------------------------------
# Violations
# --------------------------------------------------------------------------


class Edge(NamedTuple):
    """A checked edge: ``importer`` -> ``target``, reached via ``direct``."""

    rule_id: str
    importer: str
    importer_layer: str
    direct: str
    target: str
    target_layer: str

    @property
    def key(self) -> str:
        """The baseline key: the importer and the module actually reached."""
        return f"{self.importer} -> {self.target}"

    def describe(self) -> str:
        """Return the one-line report form, naming the umbrella when used."""
        via = "" if self.direct == self.target else f" (via {self.direct})"
        return f"{self.importer} [{self.importer_layer}] -> {self.target} [{self.target_layer}]{via}"


class Report(NamedTuple):
    """The full verdict of one contract run."""

    graph: Graph
    violations: dict[str, list[Edge]]
    info: list[tuple[str, str]]
    layer_sizes: dict[str, int]
    unmatched_baseline: list[str]
    baseline_errors: list[str]

    @property
    def enforced_count(self) -> int:
        """Total number of enforced-rule violating edges, baseline included."""
        return sum(len(edges) for edges in self.violations.values())


def find_violations(graph: Graph) -> dict[str, list[Edge]]:
    """Return the enforced-rule violations of ``graph``, keyed by rule id."""
    rule_by_source = {rule.source: rule for rule in RULES}
    found: dict[str, list[Edge]] = {rule.rule_id: [] for rule in RULES}
    for importer in sorted(graph.modules):
        if importer in graph.aggregators:
            continue
        importer_layer = layer_of(importer)
        rule = rule_by_source.get(importer_layer)
        if rule is None:
            continue
        for direct in sorted(graph.imports.get(importer, ())):
            for target in sorted(resolve_target(graph, direct)):
                target_layer = layer_of(target)
                if target_layer not in rule.forbidden:
                    continue
                found[rule.rule_id].append(
                    Edge(rule.rule_id, importer, importer_layer, direct, target, target_layer)
                )
    return found


def find_info_edges(graph: Graph) -> list[tuple[str, str]]:
    """Return the unranked ``L2_THEORY -> L4_LATTICE/L5_CHAIN`` edges.

    These are the *literal* import edges of non-aggregator modules: the signal
    is "this generic-looking file names a concrete module", a statement about
    the file, so aggregator pass-through (which is about laundering a forbidden
    edge) does not apply.
    """
    edges: set[tuple[str, str]] = set()
    for importer in graph.modules:
        if importer in graph.aggregators or layer_of(importer) != INFO_SOURCE:
            continue
        for target in graph.imports.get(importer, ()):
            if layer_of(target) in INFO_TARGETS:
                edges.add((importer, target))
    return sorted(edges)


# --------------------------------------------------------------------------
# Baseline
# --------------------------------------------------------------------------


#: ``# owner: <name>``.  The leading ``#`` is part of the pattern, so a
#: look-alike such as ``# notowner: x`` does not satisfy it, and the value class
#: excludes ``#`` so that an empty ``# owner:`` cannot borrow the next field's
#: marker as its value.
_OWNER_RE = re.compile(r"#\s*owner:\s*([^\s#][^#]*?)\s*(?=#|$)")

#: ``# issue: #<number>``.  A tracker reference has to be a number, so a word
#: cannot stand in for one.
_ISSUE_RE = re.compile(r"#\s*issue:\s*#(\d+)(?:\s|$)")

#: Values that name no owner.  Without this the skeleton emitted by
#: ``--baseline`` would satisfy :data:`_OWNER_RE` and could be committed as-is.
_PLACEHOLDER_OWNERS = frozenset({"todo", "tbd", "fixme", "unassigned", "none", "n/a", "-", "?"})


def parse_baseline(text: str) -> tuple[dict[str, str], list[str]]:
    """Parse baseline text into ``({key: annotation}, errors)``.

    Every entry must carry a real ``# owner: <name>`` and a real
    ``# issue: #<number>``.  The fields are matched structurally, not by
    substring presence: ``# notowner: x`` is not an owner, ``# owner:`` with no
    value is not an owner, and ``# issue: TODO`` is not a tracker.  Otherwise a
    baseline line would be a bare silencer wearing an annotation.
    """
    entries: dict[str, str] = {}
    errors: list[str] = []
    for lineno, raw in enumerate(text.splitlines(), start=1):
        if not raw.strip() or raw.lstrip().startswith("#"):
            continue
        marker = raw.find("#")
        edge = " ".join((raw if marker < 0 else raw[:marker]).split())
        annotation = "" if marker < 0 else raw[marker:].strip()
        if " -> " not in edge:
            errors.append(f"line {lineno}: not an `importer -> imported` pair: {raw.strip()!r}")
            continue
        owner = _OWNER_RE.search(annotation)
        if owner is None:
            errors.append(f"line {lineno}: missing `# owner: <name>` annotation for {edge!r}")
        elif owner.group(1).strip().lower() in _PLACEHOLDER_OWNERS:
            errors.append(
                f"line {lineno}: placeholder owner {owner.group(1).strip()!r} for {edge!r}"
            )
        if _ISSUE_RE.search(annotation) is None:
            errors.append(f"line {lineno}: missing `# issue: #<number>` annotation for {edge!r}")
        if edge in entries:
            errors.append(f"line {lineno}: duplicate baseline entry {edge!r}")
        entries[edge] = annotation
    return entries, errors


def read_baseline(path: Path = BASELINE_FILE) -> tuple[dict[str, str], list[str]]:
    """Read and parse the baseline file (an absent file means an empty one)."""
    if not path.exists():
        return {}, []
    return parse_baseline(path.read_text(encoding="utf-8"))


BASELINE_HEADER = """\
# Import-DAG contract exception baseline (scripts/import_dag_contract.py).
#
# One `importer -> imported` pair per line, each with a mandatory
# `# owner: <name>  # issue: #<number>` annotation.  Both fields are matched
# structurally: a look-alike label, an empty value or a non-numeric issue is a
# failure, and so is an entry whose edge no longer exists -- the allowlist
# cannot outlive its cause.  The `TODO` values below are placeholders that the
# contract rejects on purpose: `--baseline` derives the edges, a human assigns
# the ownership.
#
# A baseline entry means "genuine inversion, scheduled".  A tagging bug is
# fixed in the tagging rules of the checker, never here.
"""


def format_baseline(violations: dict[str, list[Edge]]) -> str:
    """Render the current violation set in baseline-file format."""
    lines = [BASELINE_HEADER]
    keys = sorted({edge.key for edges in violations.values() for edge in edges})
    for key in keys:
        lines.append(f"{key}  # owner: TODO  # issue: TODO")
    if not keys:
        lines.append("# (empty: no enforced-rule violation on the current tree)")
    return "\n".join(lines) + "\n"


# --------------------------------------------------------------------------
# Reporting
# --------------------------------------------------------------------------


def build_report(root: Path = REPO_ROOT, baseline_path: Path = BASELINE_FILE) -> Report:
    """Run the whole contract over ``root`` and return the verdict."""
    graph = load_graph(root)
    violations = find_violations(graph)
    info = find_info_edges(graph)
    layer_sizes = {layer: 0 for layer in LAYERS}
    for module in graph.modules:
        layer_sizes[layer_of(module)] += 1
    baseline, baseline_errors = read_baseline(baseline_path)
    live_keys = {edge.key for edges in violations.values() for edge in edges}
    unmatched = sorted(key for key in baseline if key not in live_keys)
    return Report(
        graph=graph,
        violations=violations,
        info=info,
        layer_sizes=layer_sizes,
        unmatched_baseline=unmatched,
        baseline_errors=baseline_errors,
    )


def print_report(report: Report, baseline: dict[str, str]) -> bool:
    """Print the human-readable verdict; return whether the contract passes."""
    ok = True
    print("== Layer sizes ==")
    for layer in LAYERS:
        print(f"  {layer}: {report.layer_sizes[layer]}")
    print(f"  aggregators (re-export umbrellas, computed): {len(report.graph.aggregators)}")

    print("== Enforced rules ==")
    for rule in RULES:
        edges = report.violations[rule.rule_id]
        unbaselined = [edge for edge in edges if edge.key not in baseline]
        status = "PASS" if not unbaselined else "FAIL"
        allowed = len(edges) - len(unbaselined)
        suffix = f" ({allowed} baselined)" if allowed else ""
        print(
            f"  {rule.rule_id} {status}: {rule.source} must not import "
            f"{'/'.join(sorted(rule.forbidden))} -- {rule.summary}; "
            f"{len(unbaselined)} violation(s){suffix}"
        )
        for edge in edges:
            marker = "baselined" if edge.key in baseline else "VIOLATION"
            print(f"      [{marker}] {edge.describe()}")
        if unbaselined:
            ok = False

    print("== INFO (unranked, never fails) ==")
    print(
        f"  {len(report.info)} {INFO_SOURCE} -> {'/'.join(sorted(INFO_TARGETS))} edge(s); "
        "explicitly unordered, not violations, and not a work list"
    )
    for importer, target in report.info:
        print(f"      {importer} -> {target}")

    print("== Baseline ==")
    print(f"  {len(baseline)} entry/entries in {BASELINE_FILE.name}")
    for message in report.baseline_errors:
        print(f"  FAIL: malformed baseline: {message}")
        ok = False
    for key in report.unmatched_baseline:
        print(f"  FAIL: stale baseline entry (edge no longer exists): {key}")
        ok = False

    print("PASS: import-DAG contract satisfied" if ok else "FAIL: import-DAG contract violated")
    return ok


def main(argv: list[str] | None = None) -> int:
    """CLI entry point.  Return 0 on success, 1 on failure."""
    parser = argparse.ArgumentParser(description="IsingModel import-DAG layer contract.")
    group = parser.add_mutually_exclusive_group()
    group.add_argument(
        "--check",
        action="store_true",
        help="Check the enforced rules against the baseline (default).",
    )
    group.add_argument(
        "--baseline",
        action="store_true",
        help="Print the current violation set in baseline-file format.",
    )
    group.add_argument(
        "--self-test",
        action="store_true",
        help="Run the contract's own test suite (scripts/test_import_dag_contract.py).",
    )
    args = parser.parse_args(argv)

    if args.self_test:
        from test_import_dag_contract import run_suite  # noqa: PLC0415

        return run_suite()

    report = build_report()
    if args.baseline:
        sys.stdout.write(format_baseline(report.violations))
        return 0

    baseline, _ = read_baseline()
    return 0 if print_report(report, baseline) else 1


if __name__ == "__main__":
    sys.exit(main())

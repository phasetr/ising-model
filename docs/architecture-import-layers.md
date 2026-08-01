---
layout: default
title: Import-DAG layer contract
---

# Import-DAG layer contract (#4833)

`IsingModel/` is a single Lake target whose ~1900 modules form one large import
DAG. Nothing in the build system records *which direction* a dependency is
allowed to run in, so an inversion — a general result reaching down into a
specialization — costs nothing to introduce and is invisible afterwards. This
page is the layer map; `scripts/import_dag_contract.py` is its executable form,
and `scripts/test_import_dag_contract.py` is the proof that the checker can
fail.

The contract is **report-only** at the time of writing: it is not wired into
CI. Wiring it in is a separate change with its own tests and independent review.

## What this contract is not

It is **not** a total order over the source directories. `IsingModel/` has 25
top-level directories and 39 loose root files, and a naive strict order over
them reports dozens of violations, most of which are tagging artifacts rather
than inversions:

* `IsingModel/PhaseTransition/` is entirely `SimpleGraph`-generic (Glimm–Jaffe
  §5.1); `grep -rl "cubicBox\|latticeGraph" IsingModel/PhaseTransition/` is
  empty. Ranking it "concrete" because of its name invents two fake violations.
* `IsingModel/SumModel.lean` sits at the repository root but consumes
  `partitionFunction_monotone_subgraph` from `FreeEnergy/SubgraphBounds.lean`,
  so it is generic theory rather than model core. Ranking it "core" invents one
  more.

Directory is therefore not layer, and topic directories such as `Conditioning/`
or `ClusterExpansion/` legitimately hold both graph-generic and cubic-box
modules. The contract ranks only the zones whose direction is both semantically
load-bearing and empirically clean, and declares the rest explicitly unranked.

It also enforces **no file-count, path-depth or build-time quota**, offers no
"redundant import" verdict and suggests no deletion. The only input to a verdict
is the layer tag of the two endpoints of an edge. `lake exe shake` answers a
different question ("is this import needed?") and its output is never consumed
here. These absences are pinned by tests, not merely stated.

## The six layers

Membership is decided by the dotted module name: an exact list for `L1_MODEL`,
then the longest matching dotted prefix. A prefix matches only whole components
(`m == p` or `m.startswith(p + ".")`); bare `startswith` would be wrong, and the
tree contains live traps for it (`IsingModel.Lattice` versus
`IsingModel.LatticeExpSum`).

| Layer | Membership | Meaning | Modules |
|---|---|---|---|
| `L0_MATH` | `IsingModel.Analysis`, `IsingModel.Combinatorics` | mathlib-adjacent helpers, no Ising content | 2 |
| `L1_MODEL` | exactly `IsingModel.{Basic, Hamiltonian, GibbsMeasure, PartitionFunctionIso, SumGraph, RealTanhAux}` | finite-volume model definitions over an arbitrary `SimpleGraph` | 6 |
| `L2_THEORY` | everything unmatched (the default) | graph-generic theory; **deliberately unranked**, see below | 519 |
| `L3_AMBIENT` | `IsingModel.{AmbientLattice, AmbientLatticeSum, AmbientComplexAnalyticity, AmbientFKG, InfiniteVolume}` | the ambient/exhaustion **generality** layer | 370 |
| `L4_LATTICE` | `IsingModel.{Concrete, Peierls, PeierlsInfinite, Lattice, LatticeExpSum, PolyDecay}` | the concrete ℤ^d lattice specialization | 910 |
| `L5_CHAIN` | `IsingModel.TransferMatrix` | the 1D chain / transfer-matrix vertical | 109 |

Counts are the census on the delivering commit, including the root umbrella
`IsingModel.lean` in `L2_THEORY`; they are a description of the tree, never a
budget.

`L1_MODEL` is an enumerated list rather than "lives at the repository root",
because the root holds three different kinds of file: the model core listed
above, concrete lattice modules (`Lattice`, `LatticeExpSum`, `PolyDecay`,
`Peierls*`), and ordinary theory (`SumModel`, `Asano`, `JDerivative`, …).

`L5_CHAIN` sits above `L4_LATTICE` by measurement, not assumption: there are 8
`L5_CHAIN → L4_LATTICE` edges (7 of them `TransferMatrix/ → Concrete/`, spread
over 5 files) and 0 in the reverse direction, so the transfer-matrix track is a
consumer vertical rather than a peer.

Two boundary details worth knowing before editing the rules. The four root
modules `AmbientLatticeSum{FInfHSymMono, FreeEnergy, GeFerromagnetic, LogZ}` are
*not* under the `IsingModel.AmbientLatticeSum` prefix under whole-component
matching, so they tag `L2_THEORY`; tagging them `L3_AMBIENT` instead was
measured to produce zero additional violations, so the two readings agree on the
current tree and the narrower one is what the census above records. Conversely
`IsingModel.PeierlsInfinite` is listed explicitly, because the
`IsingModel.Peierls` rule does not reach it.

## Allowed directions

Rows are the importing layer, columns the imported layer. `Y` is allowed, `X` is
forbidden and enforced, `-` is unranked and reported as `INFO` only.

| | `L0` | `L1` | `L2` | `L3` | `L4` | `L5` |
|---|---|---|---|---|---|---|
| **`L0_MATH`** | Y | X | X | X | X | X |
| **`L1_MODEL`** | Y | Y | X | X | X | X |
| **`L2_THEORY`** | Y | Y | Y | - | - | - |
| **`L3_AMBIENT`** | Y | Y | Y | Y | **X** | **X** |
| **`L4_LATTICE`** | Y | Y | Y | Y | Y | **X** |
| **`L5_CHAIN`** | Y | Y | Y | Y | Y | Y |

### The four enforced rules

| id | rule | rationale |
|---|---|---|
| **R1** | `L0_MATH` imports nothing outside `L0_MATH` | mathlib-adjacent helpers carry no Ising content |
| **R2** | `L1_MODEL` imports only `L0_MATH` / `L1_MODEL` | the model core is defined before any theory about it |
| **R3** | `L3_AMBIENT` imports no `L4_LATTICE` / `L5_CHAIN` | **generality must not depend on specialization** |
| **R6** | `L4_LATTICE` does not import `L5_CHAIN` | the lattice layer does not depend on the 1D chain vertical |

R3 is the invariant the issue is actually about; R1, R2 and R6 are free-standing
true ones that give the checker breadth without a rewrite bill. All four hold on
the current tree, so the delivered exception baseline is empty.

The identifiers `R4` and `R5` are deliberately absent: they name the two
`L2_THEORY → L4_LATTICE` and `L2_THEORY → L5_CHAIN` directions, which are
reported but never enforced.

### Why `L2_THEORY` is unranked, and what the 28 `INFO` edges are not

There are **28** `L2_THEORY → L4_LATTICE`/`L5_CHAIN` import edges on the
delivering commit. They are reported as `INFO`; they are **not violations**,
they **never affect the exit status**, and they are **not a work list**.

Many of them are honest concrete capstones that merely live under a topic
directory — `Conditioning.CubicBoxComponentSize →
Concrete.…CubicBoxScreeningDecomp`, for instance, is correctly directed; the
*file* is arguably misfiled but the *edge* is fine. Enforcing this direction
would manufacture a 28-entry baseline and would implicitly demand a
file-relocation campaign, which is exactly the mechanical rewrite the issue
rules out. Anything arising from these edges needs its own evidence-first issue
and is not authorized by this page.

`INFO` reports the *literal* import edges of non-aggregator modules, because the
signal is "this generic-looking file names a concrete module" — a statement
about the file, so the umbrella pass-through described below (which exists to
stop a forbidden edge being laundered) does not apply.

## Compatibility umbrellas: pass-through, not exemption

A module whose every non-comment line is a lone `import` is an **aggregator** — a
re-export index. The set is *computed*, never hand-listed, so new umbrellas need
no maintenance; there are 102 on the delivering commit, including all eight
`Concrete/LatticeGraphCorrelation/Umbrella/*`, the root `IsingModel.lean` and the
small root re-export files.

That test involves **no keyword list in either direction**, and the reason is
Lean's grammar: commands are whitespace-insensitive, so

```lean
namespace Foo theorem d : True := trivial end Foo
```

is one physical line holding three commands, and it compiles. A rule phrased as
"the line opens no declaration" therefore fails open on the first spelling nobody
listed (`unsafe def`, `partial def`, `alias`, `macro_rules`, a keyword that does
not exist yet), and a rule phrased as "the line *starts with* something harmless"
fails open on the line above. Requiring the whole line to be an import avoids
both, at the price of not recognising the ten umbrellas that carry `namespace` /
`open` / `variable` scaffolding.

That price is the right way round. Under-recognising an umbrella is safe in
**both** roles the classification feeds: as a source the module simply stays
checkable, and as a target the edge into it is checked against its own layer tag
while its own outgoing edges are checked directly. Over-recognising is the only
dangerous direction, and this predicate makes it impossible. Measured: the strict
and the scaffolding-tolerant readings give the same verdict on this tree
(R1/R2/R3/R6 all 0, 28 `INFO`), so the safe one costs nothing here.

For the same reason the contract **fails** on any physical line carrying more
than one `import`. The repository's single import scanner
(`leaf_audit.build_import_graph`, reused here so the two tools cannot disagree
about the edges) reads one import per line, and Lean accepts
`import A import B`, so such a line would make an edge invisible to the graph and
therefore to every rule. The contract refuses to certify a file it cannot read
rather than reporting it clean. No line in `IsingModel/` has this shape today.

Two rules follow:

1. **An aggregator is never a violation source.** It is an index, not generality
   code, which is what keeps `IsingModel/AmbientLattice.lean` from being flagged
   for re-exporting its own subtree.
2. **An aggregator target is expanded transitively** to the first
   non-aggregator modules behind it, and *those* are checked.

So importing a compatibility umbrella stays fully supported, but an umbrella
cannot launder a reverse edge. Expansion rather than exemption was measured to
give the same (empty) baseline on the current tree, so the stricter semantics
costs nothing today and closes the hole pre-emptively.

## The exception baseline

`scripts/import_dag_baseline.txt` is an owner-annotated allowlist of edges that
are genuine inversions not yet fixed. It is currently **empty**.

* Each entry is one `importer -> imported` pair with a mandatory
  `# owner: <name>  # issue: #<number>` annotation. Both fields are matched
  **structurally**, because a substring test would let an edge be silenced with
  no owner and no tracker at all. The owner is a single identifier-shaped token
  starting with a letter (optionally `@`-prefixed) and running to the end of its
  field, so a look-alike label (`# notowner:`), an empty value, a bare `@`, and
  `TODO x` are all rejected; the issue must be `#<n>` with `n ≥ 1`.
* An entry whose edge no longer exists is itself a **failure**, so the allowlist
  cannot silently outlive its cause.
* `--baseline` regenerates the *edge set* deterministically; it is never
  hand-edited into silence. The skeleton it prints carries `TODO` placeholders
  and is rejected by the contract until a human fills them in — the edges are
  machine-derived, the ownership is not.

**A tagging bug is fixed in the tagging rules, never in the baseline.** A
baseline entry means "real inversion, scheduled". Using one to paper over a
mislabelled endpoint destroys that meaning — and the two archetypes above
(`PhaseTransition/`, `SumModel.lean`) show that mislabelled endpoints are the
likelier failure. The adjudication procedure is to read the importer and decide
whether the dependency is genuinely inverted or an endpoint is tagged wrong.

## The one edge that had to be fixed

Before this contract landed, R3 had exactly one violation:
`AmbientLattice/Monotonicity/PlusScreening.lean` imported
`Concrete/LatticeGraphCorrelation/CubicBoxScreening.lean`.

The import was load-bearing rather than a leftover, but the root cause was a
*misplaced declaration*, not a misdirected dependency: `boltzmannWeightJ_uniform_eq`
is a fully general `SimpleGraph ι` statement (the uniform-coupling specialization
of `boltzmannWeightJ`) that happened to be declared inside a cubic-box file. It
now lives in `Inequalities/FKGInhomogeneous.lean` next to `interactionEnergyJ`,
`hamiltonianJ` and `boltzmannWeightJ`, which is the weakest level at which it can
be stated — the same principle the archived
[#4506 refactoring record](plans/4506-refactoring-replan.html) applies elsewhere.
`PlusScreening` now imports `AmbientLattice/Monotonicity/InducedWeightFactor.lean`
and `Inequalities/MonotonicityExtremal.lean` instead, and the statement of the
relocated theorem is byte-identical.

## Usage

```
python3 scripts/import_dag_contract.py             # --check (default); exit 1 on violation
python3 scripts/import_dag_contract.py --baseline  # emit the current set in baseline format
python3 scripts/import_dag_contract.py --self-test # run the checker's own test suite
```

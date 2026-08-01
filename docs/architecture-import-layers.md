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

The contract runs in CI on every pull request, in its own toolchain-free
`import-dag-contract` job of `.github/workflows/lean_action_ci.yml`: the checker's
own tests first, then the gate. A violation therefore turns the pull request red
by itself, and a red Lean build cannot mask one. It is deliberately **not** a
required status check yet — making it blocking is a separate governance
decision — so a failure is visible rather than merge-blocking today.

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

A module that has imports and declares nothing is an **aggregator** — a re-export
index. The set is *computed*, never hand-listed, so new umbrellas need no
maintenance; there are 112 on the delivering commit, including all eight
`Concrete/LatticeGraphCorrelation/Umbrella/*`, the root `IsingModel.lean` and the
small root re-export files.

**Neither classification error is safe**, which is why this is the fiddliest part
of the checker:

* Calling a real module an umbrella exempts it as a violation source, so its
  forbidden import is never reported.
* Calling an umbrella a real module hides an inversion the other way. With an
  unrecognised `L2_THEORY` umbrella `U`, the chain `L3_AMBIENT → U → L4_LATTICE`
  splits into an allowed `L3 → L2` edge and an unranked `L2 → L4` edge, and
  nothing fires.

So the classification has to be *right*, not merely conservative in some
direction. Three sieves with deliberately different shapes stand behind it.

**Whole-line classification.** Lean's grammar is whitespace-insensitive at the
command level, so

```lean
namespace Foo theorem d : True := trivial end Foo
```

is one physical line holding three commands and it compiles: a rule phrased as
"the line *starts with* something harmless" accepts it, and a rule phrased as
"the line opens no declaration" fails open on the first spelling nobody listed
(`unsafe def`, `partial def`, `alias`, `macro_rules`, a keyword that does not
exist yet). Each line is instead matched in full against `import`, or against one
of the commands that declare nothing (`namespace`, `end`, `section`, `open`,
`universe`, `variable`), with argument classes that exclude the punctuation a
term needs and with the `in` command combinator rejected outright. Anything
unmatched is content, so the module stays checkable.

**A whole-file scan for punctuation-free declarations.** Whole-line matching is
still not enough on its own, because a few declarations need no punctuation at
all and so satisfy the argument class of a multi-argument `open` or `universe`:

```lean
universe u inductive Hidden
```

is a legal line declaring an empty inductive type. Anything requiring `:`, `:=`
or a bracket is already excluded, which leaves a short closed list of command and
modifier words; an umbrella candidate whose file mentions any of them, anywhere,
is demoted to a real module.

Both sieves read comment-stripped text, so the stripper is load-bearing and is
a hand-written scan rather than a regex: Lean's block comments **nest**, and a
non-greedy `/-.*?-/` closes `/- outer /- inner -/ still a comment -/` at the
first terminator, leaving the remainder behind as apparent code — enough to
demote a genuine umbrella. `--` inside a block comment, `/-` inside a line
comment, and `/-` inside a string literal are all inert.

**An independent parser.** The resulting set is re-derived over the real tree by
`scripts/dead_candidate_scan.py`, a separately written declaration parser in this
repository, and the two must agree in both directions. The reverse half of that
agreement is what makes under-recognition *loud*: a declaration-free module the
classifier fails to recognise turns the test suite red rather than quietly losing
its pass-through.

For the same reason the contract **fails** on any import line it cannot read.
`leaf_audit.build_import_graph` — the repository's single import scanner, reused
here so the two tools cannot disagree about the edges — reads one import per
physical line anchored at column 0, while Lean also accepts `import A import B`,
an indented `  import A`, a bare `import` with the module name on the next line,
`import/- c -/ A`, `import /-x-/A`, `import «IsingModel».Concrete.A`, and a
non-`IsingModel` import in front of an `IsingModel` one. Each makes an edge
invisible to the graph and therefore to every rule.

Enumerating those shapes turned out to be a losing game — six review rounds
produced six more — so the guard is an **equivalence check** instead: what Lean
sees on the comment-stripped line must equal what `leaf_audit`'s own regex
extracts from the raw one, over arguments restricted to plain dotted-identifier
spelling. The spelling restriction closes the guillemet class in one move rather
than one escape at a time: an escaped name either escapes the scanner entirely or
is captured in a spelling that matches no real module and so silently lands in
the default layer. Which lines are examined is still decided on the stripped
text, so prose mentioning "import" cannot trip the guard. Erring towards a false
failure here is deliberate: it is loud and fixable, whereas the alternative is an
edge nobody sees. No line in `IsingModel/` diverges today.

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
python3 scripts/test_import_dag_contract.py        # the same suite, standalone
```

CI runs the standalone suite and then `--check`, in that order, and
`CIWiringTest` reads the workflow back to pin that it still does. It pins the
`on:` trigger block and the whole `import-dag-contract` job **verbatim**, closes
the set of top-level workflow keys, and separately checks that the pinned text
still says what it claims: the two `run:` commands in that order, and none of
the keys that would change what they mean.

Pinning the text rather than a list of properties is what makes this converge.
Three independent review rounds each found a new way to spell "disabled" while
a property list stayed green — `if: false`, then a `run` key nested under `env:`
(an environment variable executes nothing) and `if : false` with a space (the
same mapping to YAML), then a merge-key alias and `with: ref:` pointing checkout
at another tree so the gate would grade the base commit. Each round the
enumeration was one spelling behind; an exact region cannot be out-spelled.
Closing the top-level key set covers the same ground one level up, where a new
`defaults:` or `concurrency:` would re-aim every job below.

The pin is deliberately brittle: reformatting either region, bumping the
checkout version or adding a step turns the suite red until the constant in
`scripts/test_import_dag_contract.py` is updated to match. That is the intent —
the update is a diff a reviewer sees. It is scoped, though: edits to the `build`
job (or to any other job) are none of its business and stay green, which is
verified rather than asserted. What it cannot defend against is an edit that
changes the workflow *and* the pin together, or a required-status-check decision
taken outside the repository; those are review questions, not test questions.

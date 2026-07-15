---
layout: default
title: Refactoring baseline and execution plan
---

# Refactoring baseline and execution plan (#4506)

This document is the repository-local canonical plan for issue #4506. It records the static
baseline, reconciles the active issues, and defines the gates for refactoring aimed at faster Lean
builds and simpler code. It supersedes the phase descriptions in older #4506 comments when those
descriptions conflict with the issue state below.

## Status and issue mapping

Status as of 2026-07-15:

- #4506 remains the open tracker for this refactoring programme.
- #4521 is the open B0 benchmark issue. Measurement is in progress, and its results will be recorded
  on that issue. It replaces the unsuccessful benchmark protocol work with a deliberately small
  measurement task.
- #4519 is closed as superseded. Revisions 1--22 produced no admissible timing rows, medians,
  percentage deltas, or performance verdict. In particular, Rev22 ended with two passing static
  tests and one fixture error; it is not a performance baseline.
- #4505 is reopened to correct the stale `docs/index.md` statement that Vitali--Porter remains an
  axiom. The theorem has been proved since #4280.
- Draft PR #4520 is an archive boundary for the #4519 evidence. It does not authorize a new
  benchmark protocol or a source refactor.

The completed historical work remains useful but does not establish a speedup:

- #4499 removed imports that Shake proved unnecessary; broad umbrella-to-child rewrites were
  declined.
- #4500 consolidated the PerStageComplex tree from 254 files to 35 files, but its original
  `20 modules or fewer` target was not met.
- #4501 restored the canonical Montel/Ascoli/Vitali infrastructure.
- #4502 removed dead declarations; the issue evidence should not be used as a precise deletion
  count without checking the merged diff.
- #4503 split `LayerSpectral.lean`; eight secondary split candidates were declined.
- #4504 closed as not planned because the finite/infinite families are specializations over the
  existing `Ambient` abstraction, not duplicate theorem bodies.

## Reproducible static baseline

The baseline is `origin/main` at
`94ceb4f83906dc23069b7566ce31242240e22855` (2026-07-15). These figures are static observations,
not build-time measurements:

| Measure | Baseline | Method |
| --- | ---: | --- |
| Lean modules under `IsingModel/` | 1,985 | Count tracked `*.lean` files under the source root |
| Lean source lines under `IsingModel/` | 291,661 | Sum physical lines in those files |
| Direct imports in `IsingModel.lean` | 490 | Count lines beginning with `import` |
| Longest in-repository import chain from the root | 197 modules / 196 edges | Longest path in the static import DAG |

The 196-edge path passes through both
`Concrete.LatticeGraphCorrelation.PerStageComplex` and `AmbientComplexAnalyticity`. This is a
strong candidate explanation for clean-build serialization, but only B0 measurements may turn it
into a performance claim.

The largest files are also candidates, not automatic split targets:

| File | Lines | Initial disposition |
| --- | ---: | --- |
| `Lemma_17_5_2/DerivativeLimitProviderInfiniteHLS.lean` | 1,690 | Keep unless a declaration-DAG audit finds parallel mathematical sections |
| `Lemma_17_5_2/PseudoMassFromParamsHighTempSandwich.lean` | 1,580 | Keep unless two or more independent consumers justify a boundary |
| `Lemma_17_5_2/DerivativeLimitProviderFiniteHLS.lean` | 1,481 | Keep unless a declaration-DAG audit finds parallel mathematical sections |
| `Lemma_17_5_2/Lipschitz.lean` | 1,364 | Keep unless a stable API boundary is demonstrated |
| `ClusterExpansion/MayerCore/MayerMontroll.lean` | 1,285 | First large-file split candidate because its mathematical sections are separable |

The `Lemma_17_5_2.lean` compatibility umbrella directly imports 115 child modules and has one
in-repository consumer,
`Umbrella/RegularityAndLatticeMass.lean`. This makes that consumer a bounded import-narrowing pilot;
the public compatibility umbrella itself must remain.

## Diagnosis

The repository has two different kinds of structural cost:

1. Wide compatibility umbrellas make an internal consumer depend on APIs that it may not use.
2. Long serial chains of small modules, especially around PerStageComplex and
   AmbientComplexAnalyticity, may limit clean-build parallelism even when each file is locally
   understandable.

Large source files are a secondary concern. Splitting a large file can improve incremental builds
when independent consumers need independent sections, but it can also add tasks and deepen a serial
chain. File length alone is therefore insufficient evidence.

The existing mathematical architecture is the default abstraction boundary:

- graph-independent results belong at the weakest useful `SimpleGraph` level;
- infinite-volume results should use the existing `Ambient` and `Exhaustion` interfaces;
- finite-volume, along-exhaustion, and lattice-graph declarations should be transport or capstone
  layers rather than independent proof copies;
- a new record, typeclass, macro, or common helper requires demonstrated consumers, not anticipated
  reuse.

## Execution order

Only one refactoring PR may be active at a time. Each implementation PR must be small enough to
merge or revert in one or two working days and must name its before/after benchmark commits.

### B0: establish the performance baseline (#4521)

Use isolated worktrees and isolated build directories for fixed commits. Preserve raw command,
environment, stdout, stderr, exit status, wall/user/system time, maximum RSS, warnings, and the list
of regenerated `.olean` files.

The minimum matrix is:

- cold full build: three runs per commit;
- warm no-op root build: five runs per commit;
- representative hub touch: five runs per commit;
- representative leaf touch: five runs per commit.

Compare medians; retain every valid row. A failed run is evidence, not a row to silently replace.
B0 must publish the exact commands and a small recomputation procedure. It must not recreate the
append-only signature and anchor machinery from #4519.

No source refactor may claim a speed improvement until B0 is complete. Static import changes can be
designed in parallel, but their performance acceptance remains pending.

### B1: narrow one internal umbrella import

Replace the single internal import of `Lemma_17_5_2` in
`Umbrella/RegularityAndLatticeMass.lean` with the smallest child import set required by that module.
Do not remove or change the public `Lemma_17_5_2.lean` compatibility umbrella.

Expand to `Concrete.LatticeGraphBED`, `AmbientLattice.Analyticity`, `IntLattice`, or `FKG` only after
the pilot passes. Each family is a separate PR and measurement decision.

Acceptance:

- at least 10% lower hub-touch median, or at least 20% fewer regenerated `.olean` files;
- no more than 5% regression in the cold root-build median;
- no public API change and no changed axiom set;
- targeted module, a downstream importer, and the root build pass with zero warnings.

Rollback:

- revert the pilot if it misses both incremental thresholds, regresses the cold build by more than
  5%, increases maximum RSS by more than 10%, or expands the import closure;
- do not roll an unsuccessful pilot into the next import family.

### B2: consolidate serial micro-modules

Measure the longest chain with timings and begin with one cohesive portion of
`AmbientComplexAnalyticity`. Coalesce only modules that have one consumer, form a serial import
chain, and belong to the same mathematical layer. Preserve boundaries such as Ascoli/Montel versus
Vitali/uniqueness and retain compatibility re-exports for public paths.

Acceptance:

- at least 15% reduction in the measured weighted critical path;
- at least 10% lower cold-build median;
- no regression in the B0 incremental scenarios;
- public imports, declarations, and axiom output remain compatible.

Rollback the consolidation when any of those performance or compatibility gates fails.

### A1: simplify proofs through existing abstractions

Audit a proposed family by statement, hypotheses, proof dependencies, and consumers before editing.
Extract a common lemma only when at least two real consumers share the proof core. Introduce a new
record or typeclass only when at least three consumers repeat the same hypothesis bundle and proof
skeleton.

Keep the core theorem at the weakest useful `SimpleGraph` or `Ambient` assumptions. Keep `Λ`,
along-exhaustion, and `ℤ^d` declarations as short transports or named capstones. Preserve existing
public names as thin wrappers when downstream users rely on them.

Reject an abstraction when the first consumer becomes longer, requires more explicit arguments,
widens its import closure, or merely hides genuinely different hypotheses behind a common name.

### F1: split a large file only after import work

The first candidate is `MayerMontroll.lean`. A design audit must identify declaration boundaries
for proper colorings, inclusion--exclusion, fibers, and analytic summability, and must show that the
resulting child modules can be consumed independently.

The four largest `Lemma_17_5_2` files remain unsplit by default. Their size triggers an audit, not a
mandatory edit. Do not cut source ranges mechanically; move complete declarations at section or doc
comment boundaries.

## Verification for every implementation PR

Every source refactor must provide:

- targeted module, downstream importer, and root builds with zero warnings;
- `lake exe GKSTest` and the repository's sentinel/property checks;
- no `sorry`, `admit`, or `native_decide` in `IsingModel/`;
- representative `#print axioms` output limited to `propext`, `Classical.choice`, and `Quot.sound`;
- `scripts/audit_gate.py --diff main` and Shake for touched modules;
- `#check` coverage for preserved public entry points;
- the B0 before/after scenario relevant to the change, with raw evidence retained.

Any public API break, unexpected axiom, warning, build failure, cold-build regression over 5%, RSS
regression over 10%, or increase in regenerated `.olean` files blocks merge. The PR must be reduced,
reworked, or reverted rather than justified by source-line reduction alone.

## Explicit non-goals

The following declined work must not be revived without new measured or consumer-based evidence:

- deleting public compatibility umbrellas;
- a repository-wide mechanical import rewrite;
- merging finite-volume and infinite-volume theorems whose types or hypotheses differ;
- merging the abstract `Ambient` layer with the concrete `ℤ^d` specialization;
- deleting zero-reference public wrappers solely from a text search;
- splitting every file above a line-count threshold.

This programme changes structure, not GJ mathematical content. New theorem work remains governed by
the book-order policy in `CLAUDE.local.md`.

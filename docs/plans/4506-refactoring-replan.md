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
| `ClusterExpansion/MayerCore/MayerMontroll.lean` | 1,285 | Secondary split declined in #4503; do not revive without new measured evidence |

The `Lemma_17_5_2.lean` compatibility umbrella directly imports 115 child modules and has one
in-repository consumer, `Umbrella/RegularityAndLatticeMass.lean`. This is a static fan-out
observation, not authorization for an import-narrowing change. #4499 deliberately declined that
scope, and it may not be revived without new measured evidence.

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

The canonical B0 measurement is complete. Its fixed primary metric failed, and #4524 is now the sole
authorized B1 implementation issue. No other source refactor is authorized. Tracker #4506 remains
open until #4505 and #4524 are resolved and the final measured classification is recorded.

### B0: completed performance baseline (#4521)

The fixed revisions were:

- **B = Before**: `6a2470114fe0b5dd5c6cdcbb0e02b8acca351fb4`;
- **A = After**: `94ceb4f83906dc23069b7566ce31242240e22855`.

The canonical private-theorem-toggle rows 28--37 were independently accepted by validators V1--V3.
All ten valid primary rows rebuilt the exact six-module closure, changed the hub `.olean` hash, exited
successfully with zero warnings, restored the exact source, and left clean worktrees. Rows 7--27 are
preserved as invalid evidence and excluded from all medians and percentages.

The completed result is:

| Workload | B median | A median | Improvement | Classification |
|---|---:|---:|---:|---|
| Primary six-module closure | 16.83 s | 16.72 s | 0.6535948% | **FAIL** against 10% |
| Cold full-build diagnostic | 1597.41 s | 1304.95 s | 18.3084% | Diagnostic only |

The cold result does not override the predeclared primary metric. #4521 is closed completed because
the measurement and independent verification finished, not because performance passed. The
canonical evidence is under `.self-local/benchmarks/4521/b0-20260715-rerun1/`.

### B1: flatten the measured internal umbrella tail (#4524)

#4524 is active and is the only authorized B1 candidate. Its implementation scope is exactly three
import edits:

1. remove `Umbrella.PartitionAndPerStage` from `Umbrella/PolymerRegularitySite.lean`;
2. remove `Umbrella.PolymerRegularitySite` from `Umbrella/TwoPointUniform.lean`;
3. import `Umbrella.PartitionAndPerStage`, `Umbrella.PolymerRegularitySite`, and
   `Umbrella.TwoPointUniform` as siblings from the public `LatticeGraphCorrelation.lean` root.

The supported public import remains `IsingModel.Concrete.LatticeGraphCorrelation`. No declaration,
theorem, proof, visibility, generated-shard name, documentation, or unrelated import change is in
scope. The required primary rebuilt closure is exactly four modules: `PerStageComplex`,
`Umbrella.PartitionAndPerStage`, public `LatticeGraphCorrelation`, and root `IsingModel`.

All #4524 correctness and performance gates are mandatory, including the public-API sentinel and
unchanged declaration inventory. The fixed numeric gates are:

- primary median at most **15.048 s**;
- exact four-module primary closure;
- cold median at most **1370.1975 s**;
- primary median maximum RSS at most **3,736,674,304 bytes** (`3736674304 B`).

Any correctness, API, audit, test, review, CI, performance, closure, cold, or RSS failure requires
rollback of the three import edits and closure of #4524 with the measured classification. Do not
broaden #4524 or automatically select another candidate.

## Unselected conditional categories

The remaining categories are not an ordered roadmap and are not authorized. The umbrella-to-child
narrowing declined in #4499, including `Lemma_17_5_2`, remains declined; #4524 authorizes only the
three generated-shard import edits above. Any further candidate requires new measured evidence,
design review, and a separate authorizing issue after #4524 is resolved.

### Candidate B2: serial micro-module consolidation

B0's FAIL does not authorize this category. Only after #4524 is resolved, if new timing evidence
identifies a weighted serial critical path, a separate issue may audit one cohesive portion of that
path. Coalesce only modules that have one consumer, form a measured serial chain, and belong to the
same mathematical layer. Preserve mathematical boundaries and compatibility re-exports.

Static chain length alone is not sufficient evidence. The new issue must state before/after commits,
the affected B0 workload, compatibility gates, and an explicit rollback threshold.

### Candidate A1: proof and API abstraction

B0's FAIL does not authorize this category. Only after #4524 is resolved, consider an abstraction
candidate if new measured evidence shows that repeated proof or API structure materially contributes
to build or maintenance cost. Selection requires Tier-2/design review and a separate authorizing
issue supported by real consumers. Audit the family by statement, hypotheses, proof dependencies,
and consumers before editing. Extract a common lemma only when at least two consumers share the
proof core. Introduce a new record or typeclass only when at least three consumers repeat the same
hypothesis bundle and proof skeleton.

Keep the core theorem at the weakest useful `SimpleGraph` or `Ambient` assumptions. Keep `Λ`,
along-exhaustion, and `ℤ^d` declarations as short transports or named capstones. Preserve existing
public names when downstream users rely on them.

Reject an abstraction when the first consumer becomes longer, requires more explicit arguments,
widens its import closure, or merely hides genuinely different hypotheses behind a common name.

### Candidate F1: large-file splitting

Large files remain audit triggers, not selected work. #4503 deliberately declined its secondary
split candidates, including `MayerMontroll.lean`; none may be revived without new measured evidence
and a separate issue. A candidate issue must identify declaration boundaries and independent
consumers, and show why splitting improves the measured workload rather than deepening a serial
chain.

Do not cut source ranges mechanically. Any authorized split must move complete declarations at
section or doc comment boundaries.

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

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

The B0 measurement is the only default next step. There is no preselected implementation sequence
after B0. Any later refactor requires a separate issue supported by the B0 result and a focused
import-graph and type/hypothesis design audit.

### B0: establish the performance baseline (#4521)

Use isolated worktrees and isolated build directories for the fixed comparison:

- **B = Before**: `6a2470114fe0b5dd5c6cdcbb0e02b8acca351fb4`;
- **A = After**: `94ceb4f83906dc23069b7566ce31242240e22855`.

Preserve raw command, environment, stdout, stderr, exit status, wall/user/system time, maximum RSS,
warnings, source hashes, dirty/clean checks, and the pre/post rebuilt IsingModel `.olean`
inventories.

Lake 5 uses content-hash traces, so an mtime-only touch, including a touch followed by `--rehash`,
does not exercise this workload when it produces only `Replayed` jobs and rebuilds zero IsingModel
`.olean` files. Preserve that pre-amendment attempt, exclude it from every repetition and statistic,
and label it invalid with reason
`Lake 5 content-hash trace: mtime-only mutation rebuilt 0 olean`.

The minimum matrix is:

- primary semantic-marker workload: in
  `IsingModel/Concrete/LatticeGraphCorrelation/PerStageComplex.lean`, insert the dedicated line
  `-- benchmark-4521-state: 0` at one fixed documented location, warm `IsingModel` outside timing,
  then toggle only that line to `-- benchmark-4521-state: 1` for the timed `IsingModel` build;
  perform five valid alternating B/A repetitions per revision;
- cold full build diagnostic: three runs per revision.

Before result-bearing repetitions, run one untimed state-0 to state-1 preflight on B and one on A.
Each preflight must exit successfully with zero warnings and rebuild more than zero IsingModel
`.olean` files; otherwise stop and amend #4521 before collecting rows.

For every preflight and timed repetition, start from exact tracked bytes and a clean worktree; record
the tracked, state-0, and state-1 source hashes and pre/post `.olean` inventories; verify that only the
one-line state toggle makes the worktree dirty during the timed build; then restore the exact tracked
bytes, verify the restored hash, and verify a clean worktree before continuing. Do not commit either
marker state.

Compare medians; retain every valid row and document every invalidated sample without counting it.
A failed run is evidence, not a row to silently replace. B0 must publish the exact commands and a
small recomputation procedure. It must not recreate the append-only signature and anchor machinery
from #4519.

The primary verdict is the median wall-time improvement for the five semantic-marker runs:

`100 * (B median - A median) / B median`.

PASS means at least 10%. A valid result closes #4521 completed whether PASS or FAIL, with the full
result posted to #4521 and #4506. No source refactor may claim a speed improvement until B0 is
complete.

## Conditional candidates after B0

These are audit categories, not an ordered roadmap or authorization to edit source. A candidate may
be selected only in a new issue after the conditions below are met.

### Candidate B1: import narrowing

Consider import narrowing only if B0 returns FAIL and the retained measurements show that import
fan-out or the weighted critical path materially contributes to the primary hub-touch workload.
Selection requires a separate issue with the measured evidence and a module-level import audit.

The umbrella-to-child narrowing declined in #4499, including the observed `Lemma_17_5_2` umbrella,
must not be revived merely from static import counts. A new issue must preserve public compatibility
umbrellas and define its own measured acceptance and rollback thresholds from B0 evidence.

### Candidate B2: serial micro-module consolidation

If B0 returns FAIL and timing evidence identifies a weighted serial critical path, a separate issue
may audit one cohesive portion of that path. Coalesce only modules that have one consumer, form a
measured serial chain, and belong to the same mathematical layer. Preserve mathematical boundaries
and compatibility re-exports.

Static chain length alone is not sufficient evidence. The new issue must state before/after commits,
the affected B0 workload, compatibility gates, and an explicit rollback threshold.

### Candidate A1: proof and API abstraction

Consider an abstraction candidate only if B0 returns FAIL and retained measurements provide evidence
that repeated proof or API structure materially contributes to the measured build or maintenance
cost. Selection requires Tier-2/design review and a separate authorizing issue supported by real
consumers. Audit the family by statement, hypotheses, proof dependencies, and consumers before
editing. Extract a common lemma only when at least two consumers share the proof core. Introduce a
new record or typeclass only when at least three consumers repeat the same hypothesis bundle and
proof skeleton.

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

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

Status as of 2026-07-16:

- #4506 remains the open tracker for this refactoring programme.
- #4521 is closed completed: its canonical measurement passed independent verification, but the
  primary performance result was **FAIL** (B 16.83 s, A 16.72 s, 0.6535948% improvement against the
  fixed 10% target).
- #4524 is closed completed through merged PR #4525. Its sole authorized three-import B1 change
  passed every API, correctness, performance, resource, review, CI, and issue-manager gate and was
  squash-merged to `main` as `bc793decec94be53ea19fb927186f54068ebca7b`.
- #4519 is closed not planned. Revisions 1--22 produced no admissible timing rows, medians,
  percentage deltas, or performance verdict. In particular, Rev22 ended with two passing static
  tests and one fixture error; it is not a performance baseline.
- #4505 is reopened to correct the stale `docs/index.md` statement that Vitali--Porter remains an
  axiom. The theorem has been proved since #4280.
- #4523 tracks the pre-existing U+0085 byte that independently blocks proof-guide pdfLaTeX; it was
  not introduced by #4505, PR #4522, #4524, or PR #4525.
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
static clean-build serialization observation, not a performance claim. The completed B0 primary
measurement did not meet its 10% target; #4524 is limited to the separately measured six-module
incremental closure and does not authorize broader path restructuring.

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

The canonical B0 measurement and the sole authorized B1 implementation are complete. No additional
source refactor is active or authorized. The next programme step is to merge the independently
verified #4505 documentation fix in PR #4522, then perform the #4506 completion audit. Tracker #4506
remains open until that audit records the final state.

### B0: completed performance baseline (#4521)

The fixed revisions were:

- **B = Before**: `6a2470114fe0b5dd5c6cdcbb0e02b8acca351fb4`;
- **A = After**: `94ceb4f83906dc23069b7566ce31242240e22855`.

Independent verification accepted the canonical identity, every per-run classification, and the
aggregate arithmetic for private-theorem-toggle rows 28--37. All ten valid primary rows rebuilt the
exact six-module closure, changed the hub `.olean` hash, exited successfully with zero warnings,
restored the exact source, and left clean worktrees. Rows 7--27 are preserved as invalid evidence and
excluded from all medians and percentages.

The completed result is:

| Workload | B median | A median | Improvement | Classification |
|---|---:|---:|---:|---|
| Primary six-module closure | 16.83 s | 16.72 s | 0.6535948% | **FAIL** against 10% |
| Cold full-build diagnostic | 1597.41 s | 1304.95 s | 18.3084% | Diagnostic only |

The cold result does not override the predeclared primary metric. #4521 is closed completed because
the measurement and independent verification finished, not because performance passed. The
canonical evidence is under `.self-local/benchmarks/4521/b0-20260715-rerun1/`.

### B1: completed internal umbrella-tail flattening (#4524, PR #4525)

#4524 authorized exactly three import edits:

1. remove `Umbrella.PartitionAndPerStage` from `Umbrella/PolymerRegularitySite.lean`;
2. remove `Umbrella.PolymerRegularitySite` from `Umbrella/TwoPointUniform.lean`;
3. import `Umbrella.PartitionAndPerStage`, `Umbrella.PolymerRegularitySite`, and
   `Umbrella.TwoPointUniform` as siblings from the public `LatticeGraphCorrelation.lean` root.

The supported public import remains `IsingModel.Concrete.LatticeGraphCorrelation`. No declaration,
theorem, proof, visibility, generated-shard name, documentation, or unrelated import change is in
scope. The required primary rebuilt closure is exactly four modules: `PerStageComplex`,
`Umbrella.PartitionAndPerStage`, public `LatticeGraphCorrelation`, and root `IsingModel`.

The candidate at `7f930464d57937f568acb3b31df9365bdeae82e1` passed the public-API sentinel,
unchanged declaration inventory, targeted/root/test/axiom checks, independent correctness and code
review, corrected Tier-2/design audit, GitHub CI, and issue-manager final resolution audit. The
accepted performance result is:

| Gate | Result | Verdict |
|---|---:|---|
| Fresh primary baseline → candidate | 16.89 s → 11.74 s (30.4914150%) | PASS |
| Fixed #4521 A → candidate | 16.72 s → 11.74 s (29.7846890%) | PASS, limit 15.048 s |
| Primary rebuilt closure | 6 modules → exactly 4 | PASS |
| Primary median maximum RSS | 3,396,485,120 bytes | PASS, limit 3,736,674,304 bytes |
| Candidate cold median | 1052.46 s | PASS, limit 1370.1975 s |
| Candidate cold RSS | 5,166,612,480 bytes | Diagnostic only |

PR #4525 was squash-merged after exact-head authority verification as
`bc793decec94be53ea19fb927186f54068ebca7b`; #4524 then closed automatically. The result authorizes
no scope broadening or automatic next candidate.

## Unselected conditional categories

The remaining categories are not an ordered roadmap and are not authorized. The umbrella-to-child
narrowing declined in #4499, including `Lemma_17_5_2`, remains declined; completed #4524 authorized
only the three generated-shard import edits above. Any further candidate requires new measured
evidence, design review, and a separate authorizing issue after the #4506 completion audit.

### Candidate B2: serial micro-module consolidation

The completed B0/B1 sequence does not authorize this category. If future new timing evidence
identifies a weighted serial critical path, a separate issue may audit one cohesive portion of that
path. Coalesce only modules that have one consumer, form a measured serial chain, and belong to the
same mathematical layer. Preserve mathematical boundaries and compatibility re-exports.

Static chain length alone is not sufficient evidence. The new issue must state before/after commits,
the affected B0 workload, compatibility gates, and an explicit rollback threshold.

### Candidate A1: proof and API abstraction

The completed B0/B1 sequence does not authorize this category. Consider an abstraction candidate
only if future new measured evidence shows that repeated proof or API structure materially
contributes to build or maintenance cost. Selection requires Tier-2/design review and a separate
authorizing issue supported by real consumers. Audit the family by statement, hypotheses, proof
dependencies, and consumers before editing. Extract a common lemma only when at least two consumers
share the proof core. Introduce a new record or typeclass only when at least three consumers repeat
the same hypothesis bundle and proof skeleton.

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
- the `lean-verify-audit` V1--V3 verification/audit gate and focused Shake/import review for touched
  modules; `scripts/leaf_audit.py` is a separate import-graph orphan/dead-candidate report, not a
  V1--V3 gate substitute;
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

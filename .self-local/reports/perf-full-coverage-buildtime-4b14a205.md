# Full-coverage per-module build-time measurement (HEAD 4b14a205)

**Verdict: the "exhausted" claim was again premature. Two NEW #4695-type outliers found
(one verified by A/B measurement), but this is now backed by 2011/2011 coverage.**

## Method (warm cache of the main tree untouched)
- `git worktree add --detach /tmp/claude-501/perf-4b14a205 4b14a205`; `.lake/packages`
  symlinked to the main tree (mathlib oleans reused, replayed, never rebuilt); `.lake/build`
  fresh => every one of the repo's own modules built from scratch.
- **Clean full build**: `lake build --no-ansi` -> `/tmp/claude-501/fullbuild.log`.
  Result: `Build completed successfully (5040 jobs)`, wall **17:02**, user 4031s, sys 2896s
  (677% CPU, 10 cores, lake has no `-j`).
- Per-module wall times parsed from `✔ [n/m] Built <Module> (Xs|Xms)`.
  **Coverage = 2011/2011 modules** (the earlier 2010 gap was a parse artifact: sub-second
  modules print `ms`, e.g. `PseudoMass.FromParamsBounds (385ms)`).
- Own-cost for the top ranks measured serially, warm, one Lean process at a time:
  `/usr/bin/time -p lake env lean -Dprofiler=true <file>`, **own = real − import**.
- Structure of the hot spots resolved with `-Dprofiler.threshold=250` and
  `-Dtrace.profiler=true` (Firefox-profile JSON, aggregated over all threads).

Caveat on the ranking metric: full-build wall times are inflated ~1.5-2x by 10-way
parallel contention. They are used only to *rank*; every conclusion below rests on the
serial own-cost re-measurement. Ranks 26-60 were also own-cost measured (max 4.90s) to
confirm the ranking is monotone and hides no outlier below the top-25.

## Per-module ranking, top 10 (clean-build wall)
| # | module | wall |
|---|---|---|
| 1 | ClusterExpansion.AlternatingCompleteGraph.CompleteGraphK4 | 22.0s |
| 2 | TransferMatrix.TwoSiteInteractingLayerSpectralData | 18.0s |
| 3 | PseudoMass.HLSCorrelationCapstone | 16.0s |
| 4 | ...Lemma_17_5_2.MassContinuityFiniteVolumeBindingPairDeriv | 14.0s |
| 5 | TransferMatrix.TwoSiteInteractingOpenStripInfiniteVolume | 13.0s |
| 6 | Peierls.CubicBoxPreconnected | 13.0s |
| 7 | ...Lemma_17_5_2.GlobalPseudoMassDistCubicInf | 13.0s |
| 8 | ClusterExpansion.MayerCompleteContribution | 12.0s |
| 9 | ...Lemma_17_5_2.GlobalPseudoMassDistCubicInfFV | 10.0s |
| 10 | Asano | 10.0s |

Distribution (wall): >=10s: 10 modules, 7-10s: 29, 5-7s: 318, 4-5s: 963, <4s: 691.
Sum of module wall times 8704s.

## Serial own-cost (real − import), top of the measured set
| own | real | import | file |
|---|---|---|---|
| 11.64 | 13.31 | 1.67 | ClusterExpansion/AlternatingCompleteGraph/CompleteGraphK4.lean |
| 9.29 | 11.30 | 2.01 | .../Lemma_17_5_2/MassContinuityFiniteVolumeBindingPairDeriv.lean |
| 8.79 | 10.72 | 1.93 | PseudoMass/HLSCorrelationCapstone.lean |
| 8.75 | 10.94 | 2.19 | TransferMatrix/TwoSiteInteractingLayerSpectralData.lean |
| 6.34 | 8.10 | 1.76 | Peierls/CubicBoxPreconnected.lean |
| 6.09 | 7.83 | 1.74 | .../Lemma_17_5_2/GlobalPseudoMassDistCubicInf.lean |
| 5.65 | 7.20 | 1.55 | Dobrushin/ResolventDecay.lean |
| 5.56 | 7.25 | 1.69 | ClusterExpansion/MayerCompleteContribution.lean |
| 5.35 | 7.52 | 2.17 | TransferMatrix/TwoSiteInteractingOpenStripInfiniteVolume.lean |
| 4.54 | 6.65 | 2.11 | ClusterExpansion/TwoPointCorrelationHTBound.lean |
| 4.43 | 6.38 | 1.95 | ClusterExpansion/TwoPointCorrelationInfiniteAnalytic.lean |
| 4.39 | 6.14 | 1.75 | ContinuousSpin/TwoComponentGriffithsIV.lean |
| 4.21 | 5.92 | 1.71 | ContinuousSpin/TwoComponentGriffiths.lean |
| 4.03 | 5.83 | 1.80 | .../Lemma_17_5_2/FiniteRegionPseudoMassDistFV.lean |
| 4.00 | 5.78 | 1.78 | .../Lemma_17_5_2/GlobalPseudoMassDistCubicInfFV.lean |
(ranks 26-60: 4.90 TwoComponentGriffithsII, 4.55 MassContinuityFiniteVolumeDartRatio,
3.70 ClusterConditioningFiberSplit, then <3.5 -> no outlier hides there.)

## Dominant-cost diagnosis per hot spot
| file | own | dominant | concentration |
|---|---|---|---|
| CompleteGraphK4 | 11.64 | `decide` tactic 4.96s + kernel type-checking 3.63s (line 34) | **OUTLIER 74%** |
| HLSCorrelationCapstone | 8.79 | 2x `positivity` interpreted `Positivity.evalDiv` 2.84s + 2.71s (lines 185, 189) | **OUTLIER 63%** |
| MassContinuityFiniteVolumeBindingPairDeriv | 9.29 | one `exact` 6.82s, category `Meta.isDefEq`/`whnf` (line 107, `HasDerivAt.comp`) | concentrated, hard |
| GlobalPseudoMassDistCubicInf | 6.09 | one `exact` 4.27s; trace: `Meta.isDefEq` 6.70s self | concentrated, hard |
| MayerCompleteContribution | 5.56 | one `rw` 3.89s; trace: `Meta.isDefEq` 5.92s self | concentrated, hard |
| Dobrushin/ResolventDecay | 5.65 | one `refine` 3.81s; trace: `Meta.isDefEq` 5.13s self | concentrated, hard |
| TwoSiteInteractingLayerSpectralData | 8.75 | many small nlinarith/normNum/`instantiate metavars` (<0.7s each) | diffuse (already peeled by #4699) |
| CubicBoxPreconnected | 6.34 | 4x `simp` ~0.56s | diffuse |
| TwoSiteInteractingOpenStripInfiniteVolume | 5.35 | nothing above 250ms | fully diffuse |
| TwoComponentGriffiths(IV), GlobalBranchRealAxis | 4.2-4.4 | `nlinarith` 0.6-0.8s + noise | diffuse |

## Undiscovered outliers: YES, two — ranked by expected saving
1. **CompleteGraphK4.lean:34 `decide` -> `decide +kernel` — VERIFIED −5.3s.**
   A/B measured on a standalone copy of the same goal (no repo file edited):
   `decide` real 13.01s (tactic 5.29s + kernel 3.83s) vs `decide +kernel` real 7.74s
   (kernel 3.72s only). The elaborator-side whnf evaluation is pure duplicate work; the
   kernel check is the irreducible part. Still `decide` (no `native_decide`), axiom set
   unchanged. **Risk: low.** Keep `set_option maxRecDepth 2000`.
2. **HLSCorrelationCapstone.lean:185 and :189 `positivity` -> explicit term — est. −4 to −5s.**
   **CORRECTION (added after PR #4713 review; `dev-review`/codex/`dev-audit-tier1`/
   `dev-issue-manager` independently converged): the line-189 goal/hypothesis below was
   originally misidentified in this report as `0 ≤ 2 / (1 + (M * latticeDistance d x₀ z)^α)`
   / `hMdx_nn`. That was wrong — `mul_le_mul`'s residual `c0` goal at line 189 is actually
   `0 ≤ 2 / (1 + (m_y * r')^α)`, needing `hmyr_nn` (the `b0` argument that would need
   `hMdx_nn`-shaped reasoning is on the next line and was already closed by the pre-existing
   `exact hRHS_x_pos.le`, unchanged). The text below is corrected to match; see issue #4712
   for the same correction applied to its body.**
   Exactly the PR #4695 pattern: goals are `0 ≤ 2 / (1 + (m_x * r')^α)` and
   `0 ≤ 2 / (1 + (m_y * r')^α)`; `positivity` re-descends the huge
   `set`-bound atoms (`pseudoMassFromParamsAtPair …`) through interpreted `evalDiv`
   (2.84s + 2.71s = 5.55s = 63% of own cost). The needed nonnegativity hypotheses are
   **already in context** (`hmxr_nn`, `hmyr_nn`), so:
   `exact div_nonneg zero_le_two (add_nonneg zero_le_one (pow_nonneg hmxr_nn α))` and
   `exact div_nonneg zero_le_two (add_nonneg zero_le_one (pow_nonneg hmyr_nn α))`.
   **Risk: low.** (Est. only; not A/B measured because the goal needs the full local context.)
3. (Class, not a silver bullet) **`Meta.isDefEq` cluster — 4 modules, ~4-7s each.**
   BindingPairDeriv:107, GlobalPseudoMassDistCubicInf, MayerCompleteContribution,
   ResolventDecay. Cost is defeq/whnf unification against giant
   `correlationAlongExhaustion` / `pseudoMassFromParamsAtPairFV` atoms, not tactic search.
   Evidence it is at the edge: enabling `-Dtrace.profiler` pushed BindingPairDeriv:107 past
   the 200k-heartbeat limit. Possible levers: explicit type ascription / explicit universe
   & function arguments on `HasDerivAt.comp`, splitting the `exact` into `refine` + typed
   `have`s, or `irreducible` on the pseudo-mass defs. **Expected 2-4s per site, medium risk,
   uncertain — needs per-site experimentation; NOT a #4695-style safe rewrite.**

Everything else in the top 25 is diffuse (no call above ~0.8s): no further outliers exist.

## `ring` -> `ring_nf` fallback sites: cost is negligible (honest answer)
Both sites do log `info: Try this: ring_nf ...` on every build
(`ContinuousSpin/Phi4AllOdd.lean:41`, `TransferMatrix/TwoSiteInteractingLayerOpenBoundaryWindow.lean:223`),
but the measured cumulative `ring` category is **33.9ms** and **121ms** respectively
(module own-costs 1.99s and 2.74s). This is a log-hygiene / `info`-noise issue, **not**
a build-time item. Do not spend a PR on it for performance reasons.

## Scale check (what a fix is worth)
Library user-CPU for a clean build = 4031s over 2011 modules (mean ~2.0s/module).
Items 1+2 together are ~10s (~0.25%). There is no remaining single change worth >1%.
Structural observation: serial `import` is 1.55-2.19s per module (mean ~1.8s) versus a
mean own-cost of ~2.0s, i.e. per-module olean loading is of the same order as all
elaboration in this repo. With 2011 modules, module *count* — not any tactic — is the
dominant structural cost driver. (Caveat: in the parallel build imports overlap and hit
the page cache, so this is an upper bound; a module-consolidation experiment would have
to be measured before acting, and it trades against build parallelism.)

## Regression prevention
- Store this ranking as the baseline. Re-run the clean-build ranking in a throwaway
  worktree after every ~20 PRs (17 min wall) and diff the top-50; a new entry >6s own-cost
  is a regression signal.
- Per-file own-cost budget gate for the known hot files (e.g. CompleteGraphK4 < 7s,
  HLSCorrelationCapstone < 4s after the fixes).
- Lint rule (already recommended in the 2db44a2b report, still violated):
  forbid `positivity`/`nlinarith` where an explicit
  `div_nonneg`/`add_nonneg`/`mul_nonneg`/`pow_nonneg` term closes the goal from
  hypotheses already in context.
- New rule: prefer `decide +kernel` over bare `decide` for finite-enumeration goals
  (avoids duplicated elaborator-side evaluation; `native_decide` remains banned).
- Never rank by `maxHeartbeats` markers, file size, or import-cone size — this run
  reconfirms they are uncorrelated with measured cost.

## Artifacts
- Full build log: `/tmp/claude-501/fullbuild.log` (ephemeral)
- Ranking: `/tmp/claude-501/ranked2.txt`; profiles: `/tmp/claude-501/prof/` (ephemeral)
- Measurement worktree was removed after the run; the main tree's `.lake` was never
  rebuilt (only mathlib oleans read through the symlink).

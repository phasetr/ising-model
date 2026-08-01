# Build-time measured audit — axis ③ (HEAD 2db44a2b)

## Method
- Per-module elaboration cost measured WITHOUT cascade via
  `/usr/bin/time -p lake env lean -Dprofiler=true <file>` against the already-built
  dependency oleans (`.lake/build`, 2030 oleans present).
- Metric: **own-cost = real − import**. `import` (~1.6 s typical) is fixed olean-load I/O;
  it is subtracted so ranking reflects the module's OWN elaboration/tactic work.
- Candidate set (48 files) = union of all 28 `set_option maxHeartbeats` files + top-25
  largest files + `TestGenerators.lean`. Serialized, one Lean process at a time
  (no other Lean build running; confirmed via pgrep). Full 2018-file sweep is ~8 h and
  was not run; candidate set is chosen to over-cover plausible hot-spots.
- For the top files the profiler `cumulative profiling times` block and per-call
  `... took Nms` lines were inspected.

## Ranked measured own-cost (top of 48 candidates)
real,import,own,file
11.57,1.62,9.95,IsingModel/Concrete/LatticeGraphCorrelation/TheoremEtaLe1/BallBoundaryInfinite.lean
9.62,1.78,7.84,IsingModel/TransferMatrix/TwoSiteInteractingLayerSpectralData.lean
5.98,1.7,4.28,IsingModel/ClusterExpansion/TwoPointCorrelationInfiniteAnalytic.lean
5.10,1.58,3.52,IsingModel/Concrete/LatticeGraphCorrelation/TheoremEtaLe1/Contraction/Factor.lean
5.05,1.61,3.44,IsingModel/Inequalities/ClusterConditioningFiberSplit.lean
4.64,1.62,3.02,IsingModel/Concrete/LatticeGraphCorrelation/TheoremEtaLe1/HighTempMassGap.lean
4.74,1.79,2.95,IsingModel/PseudoMass/HLSSharpPairBound.lean
4.69,2.04,2.65,IsingModel/ClusterExpansion/FieldAvoidingRatio.lean
4.35,1.75,2.60,IsingModel/TransferMatrix/TwoSiteInteractingLayerOpenBoundaryWindow.lean
4.16,1.56,2.60,IsingModel/LeeYang/IsingApplication.lean
4.26,1.7,2.56,IsingModel/ClusterExpansion/FieldVertexAvoidingRatio.lean
4.11,1.55,2.56,IsingModel/LeeYang/RatioBound.lean
3.99,1.54,2.45,IsingModel/TransferMatrix/LayerSpectral/FlipParityPartitionBounds.lean
4.02,1.62,2.40,IsingModel/Inequalities/SourcefreeConnectionEdgePivotal.lean
2.40,0,2.40,IsingModel/TestGenerators.lean

## Dominant category = `interpretation` (mathlib tactic elaborators run interpreted)
| file | own | interpretation | note |
|---|---|---|---|
| TheoremEtaLe1/BallBoundaryInfinite | 9.95s | 7.97s | single `positivity` (line 194) = 7.39s interpreted (`Positivity.evalAdd`) |
| TransferMatrix/TwoSiteInteractingLayerSpectralData | 7.84s | 6.19s | ~dozens of nlinarith/normNum @100-260ms each; tc 2.53s, simp 1.69s |
| PseudoMass/HLSSharpPairBound | 2.95s | 2.86s | dense arithmetic |
| ClusterExpansion/TwoPointCorrelationInfiniteAnalytic | 4.28s | 1.71s | typeclass inference 2.36s dominates here |
| TheoremEtaLe1/HighTempMassGap | 3.02s | 1.82s | |
| TheoremEtaLe1/Contraction/Factor | 3.52s | 1.06s | |
| TestGenerators | 2.40s | 0.47s | native_decide `example`s + IR/LCNF compilation |

## Findings
1. **Silver bullet — BallBoundaryInfinite line 194 `positivity` = 7.39s.**
   Goal is `0 ≤ h1.term*h2.term + h3.term*h4.term` with h1..h4 (`correlationInfinite_nonneg`)
   already in context. `positivity` re-descends the huge atomic `correlationInfinite …`
   subterms via `evalAdd`, interpreted. Replace with explicit
   `exact add_nonneg (mul_nonneg h1 h2) (mul_nonneg h3 h4)`.
   Expected: own 9.95s → ~2.5s (−7.4s). Correctness/warning-zero preserved.
2. **`interpretation` is the systemic top category** across heavy files: mathlib tactic
   elaborators (positivity/nlinarith/normNum) execute in Lean's interpreter downstream.
   No single silver bullet on TwoSiteInteractingLayerSpectralData (death-by-1000-nlinarith);
   converting provably-linear `nlinarith`→`linarith` on its ~15 heaviest calls could save
   ~1-2s but needs per-call verification (medium effort, low-medium risk).
3. **maxHeartbeats overrides do NOT mark hot-spots.** The entire Lemma_17_5_2 cluster
   (12 files carrying `maxHeartbeats` bumps) measures ~2.0s own each — average. Prior
   "build-speed" heuristics (file size, import cone, heartbeat bump) were uncorrelated
   with measured cost. Size example: 779-line TwoPointCorrelationInfiniteAnalytic = 4.28s;
   768-line IncrementCapstone = 2.08s; the 583-line BallBoundaryInfinite region is 9.95s.
4. **TestGenerators.lean** compiles native_decide `example` sanity checks (2.40s own) on the
   library critical path. These are non-deliverable test artifacts and the sole
   `native_decide` occurrences in IsingModel/. Moving them into the existing `test` lean_lib
   removes 2.40s from the library build AND removes native_decide from deliverables
   (audit hygiene per lean-verify-audit). Low risk.
5. **Import outlier — AmbientLatticeSum/InducedUnion**: import 8.0s vs ~1.6s typical
   (real 10.22s, own only 2.14s). It sits atop a ~5× larger transitive olean closure.
   Secondary: worth a `lake exe shake` / import-cone trim check; not an elaboration hot-spot.

## Regression prevention
- Keep a profiler gate: for the hottest modules run
  `lake env lean -Dprofiler=true <mod>` in CI and fail if own-cost (real−import) or
  `interpretation` exceeds a per-file budget (e.g. BallBoundaryInfinite < 4s after fix).
- Lint/CI rule: forbid `positivity`/`nlinarith` on goals discharge-able by an explicit
  `add_nonneg`/`mul_nonneg`/`linarith` term when hypotheses are already present.
- Forbid `native_decide` in `IsingModel/` (already an audit rule; TestGenerators violates).

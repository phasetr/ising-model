# perf: failed higher-order-unification `isDefEq` cluster (A/B measured, main c05432f9)

`dev-perf` measured this with `lake env lean -Dprofiler=true` (real−import, 3-4 replicate
median, serial, warm cache) plus `set_option trace.profiler true` / `trace.profiler.threshold`
and stub A/B experiments. This report was written by `dev-pr-clerk` transcribing `dev-perf`'s
results verbatim (dev-perf could not write the report itself due to a system constraint);
no technical judgment was added or re-derived here.

## Correction of prior report

The existing report `.self-local/reports/perf-full-coverage-buildtime-4b14a205.md` classified
these 4 modules as "medium risk, each 2-4s, needs individual experiments". That evaluation was
**incorrect**: all 4 (plus 2 more found during this investigation, total 6) are the **same
low-risk mechanism** (a failed higher-order-unification `isDefEq` path), not independent
medium-risk items. The prior report's "huge-atom `whnf`" diagnosis was half right but did not
capture the true root cause below.

## Measured own-cost (before -> after fix)

| Module | own (current) | own (fixed) | delta |
|---|---:|---:|---:|
| `IsingModel/Concrete/LatticeGraphCorrelation/Lemma_17_5_2/MassContinuityFiniteVolumeBindingPairDeriv.lean` | 8.26s | 1.82s | **-6.44s** |
| `IsingModel/Concrete/LatticeGraphCorrelation/Lemma_17_5_2/GlobalPseudoMassDistCubicInf.lean` | 5.69s | 1.68s | **-4.01s** |
| `IsingModel/ClusterExpansion/MayerCompleteContribution.lean` | 5.44s | 1.81s | **-3.63s** |
| `IsingModel/Dobrushin/ResolventDecay.lean` | 4.97s | 1.55s | **-3.42s** |
| (additional finding) `IsingModel/Concrete/LatticeGraphCorrelation/Lemma_17_5_2/FiniteRegionPseudoMassDistFV.lean` | 3.74s | 1.57s | **-2.17s** |
| (additional finding) `IsingModel/Concrete/LatticeGraphCorrelation/Lemma_17_5_2/GlobalPseudoMassDistCubicInfFV.lean` | 3.76s | 1.77s | **-1.99s** |
| **Total** | | | **-21.7s** |

## Mechanism (identical across all 6)

A failed higher-order-unification path in `isDefEq`. The lambda body of an argument has its
elaboration postponed, producing a metavariable **applied to an argument** (`?m x`, `?m (n+d)`,
`?m i`). Because this is not a Miller pattern, structural unification fails, and `isDefEq` falls
back to a delta-reduction descent that unfolds the definition stack all the way down and
**ultimately fails** (`❌`). Elaboration then succeeds via a different route (postponement), so
the seconds spent on the failed path are **100% wasted work**.

## Attribution and fix (each A/B-verified, proof-term-only, statement unchanged, risk = low)

1. `MassContinuityFiniteVolumeBindingPairDeriv.lean:107-108`, `finiteVolumeBindingPairDeriv`,
   local `hdiff` (79% of module own-cost) -> make the inner function of `HasDerivAt.comp`
   explicit via
   `(h := fun β' => Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d)
     (cubicExhaustion d) (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n)`.
2. `GlobalPseudoMassDistCubicInf.lean:133`, local `h1` (70%) -> `exact Finset.inf'_le _ hpair_mem`
   (let `_` be resolved from the goal). **REFUTED sub-hypothesis: making `(b := (x, z))`
   explicit had zero effect — the culprit is `f`, not `b`.**
3. `MayerCompleteContribution.lean:89-91`, `singlePolymer_ursell_term_eq` (67%) -> make `ω`
   explicit in `ursellCoefficient_complete_eq (ω := fun _ : Fin (m + 1) => P) …`.
4. `ResolventDecay.lean:106-107`, `isingInfluenceMatrix_tsum_shift_apply_le` (69%) -> make `f`
   explicit in `summable_nat_add_iff (f := fun i => ((isingInfluenceMatrix G β J) ^ i) x y) d`.
   **This is an existing idiom already used in this repo**
   (`Dobrushin/InfiniteVolumeUniformInfluence.lean:64,154`).
5. `FiniteRegionPseudoMassDistFV.lean:112` / `GlobalPseudoMassDistCubicInfFV.lean:40` — same line
   `Finset.inf'_le (fun q => …) hmem` -> `Finset.inf'_le _ hmem`.

## Unverified hypotheses (separate items, not included in the -21.7s total)

- `MassContinuityFiniteVolumeDartRatio.lean` (own 4.55s): two interpreted `positivity` calls
  measured at 927ms + 931ms; estimated -1.5 to -1.8s, but **no A/B experiment performed**.
- `TwoPointCorrelationHTBound.lean` (own 4.54s): no call cleared the 800ms threshold ->
  **confirmed diffuse** (no single-cause candidate).

## Ancillary finding (design item, not a perf item)

`finiteRegionPseudoMassDistFV_le_of_mem` (public, in `FiniteRegionPseudoMassDistFV.lean:106`)
and `finiteRegionPseudoMassDistFV_le_pair` (private, in
`GlobalPseudoMassDistCubicInfFV.lean:34`) have identical statements — a dedup candidate. This
is a design observation for a separate item, not a build-speed action for this issue/PR.

## Suggested regression-prevention (proposal only; not authorized/implemented here)

1. For any module with own-cost > 3s, enable
   `set_option trace.profiler true; set_option trace.profiler.threshold 400` and grep for
   `[Meta.isDefEq] [>1.0] ❌`. This was the **only** signal that caught all 6 modules; aggregate
   `-Dprofiler=true` numbers alone do not surface the `Meta.isDefEq` category and miss this class
   of bug.
2. When applying a lemma that takes a lambda argument, pin down the function/family with `_` or
   a named implicit argument, so as not to create a `?m x`-shaped metavariable application.

## Artifacts preserved

Copied from the ephemeral `/tmp/claude-501/isdefeq/` location (session-scoped, not durable) to
`.self-local/reports/perf-isdefeq-cluster-artifacts/`:
- Fixed-version Lean sources: `bpd_B1.lean.txt`, `bpd_B2.lean.txt`, `gpm_G1.lean.txt`,
  `gpm_G2.lean.txt`, `gpm_G3.lean.txt`, `mcc_M1.lean.txt`, `res_FIX.lean.txt`,
  `fv1_FIX.lean.txt`, `fv2_FIX.lean.txt`. They carry the `.lean.txt` suffix on purpose: the
  audit gate self-test `test_no_tracked_lean_file_lives_outside_the_checked_roots` requires
  every tracked `.lean` file to live under a checked root, and these are experiment records
  rather than library sources. Drop the `.txt` suffix locally to re-run them.
- Raw trace-profiler logs: `bpd_trace.out`, `gpm_trace.out`, `mcc_trace.out`.
- Measurement script: `measure.sh` (takes the Lean file to measure as its first argument).

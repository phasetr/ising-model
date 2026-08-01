# Perf audit C1 — `positivity` cost in `IsingModel/PseudoMass/HLSSharpPairBound.lean`

HEAD `8037cae1` (main). All runs serialized, warm oleans, `pgrep -fl "lean|lake"` empty
before start. Tool: `/usr/bin/time -p lake env lean -Dprofiler=true [...] <file>`.
Metric = **own-cost = real − import**. No repo file was modified (probes are copies in `$TMPDIR`).

## 1. Module own-cost (baseline)

| run | real | import | own |
|---|---|---|---|
| 1 | 5.20 | 1.80 | 3.40 |
| 2 | 4.74 | 1.70 | 3.04 |
| 3 | 4.77 | 1.70 | 3.07 |
| 4 | 4.94 | 1.74 | 3.20 |
| 5 | 4.69 | 1.63 | 3.06 |

**Baseline own-cost ≈ 3.10 s** (median; ±0.15 s run-to-run noise).
Earlier deep-dive (`refactor-buildtime-deepdive-978e8289.md`) recorded 2.84 s — same
module, machine-load variance, no regression.

Cumulative categories (`-Dprofiler=true`, warm):
interpretation 3.82 s(*) / typeclass inference 1.35 s / tactic execution 536 ms /
norm_num 207 ms / ring 157 ms / simp 127 ms / elaboration 115 ms.
(*) `interpretation` is the umbrella that contains the `positivity` elaborator work.

## 2. Where the cost actually is (per-declaration, `-Dprofiler.threshold=1`, JSON positions)

Positions are reported at declaration-start line.

| decl start | theorem | total | of which positivity |
|---|---|---|---|
| 397 | `darts_cross_sum_le_sharp_decay` (thm @414) | 1106 ms | **575 ms** |
| 253 | `tsum_mul_neighborFinset_sum_pow_neg_le` (@262) | 498 ms | **265 ms** |
| 41 | `summable_pow_neg_pair_translate` (@47) | 489 ms | 48 ms (dominated by nlinarith 241 ms @62) |
| 374 | `summable_mul_neighborFinset_sum_pow_neg` (@377) | 238 ms | **137 ms** |
| 98 | `tsum_correlationInfinite_pair_product_le_HLS_sharp_decay` (@117) | 335 ms | 18 ms |
| 318 | `correlationInfinite_le_maj` (@328) | 299 ms | 59 ms |
| 553 | `tsum_one_div_one_add_scaled_pow_pair_le` (@564) | 265 ms | 72 ms |
| 202 | `pow_neg_neighbour_shift_le` (@208) | 212 ms | 20 ms |
| 64 | `hls_conv_sharp_decay_real` (@72) | 113 ms | 41 ms |
| 223 | `neighborFinset_sum_pow_neg_le` (@230) | 91 ms | 11 ms |
| 615 | `exp_neg_scaled_dist_pair_le_one` (@623) | 68 ms | 0 |

Top individual calls:

| ms | decl | call |
|---|---|---|
| **405** | 397 | `Positivity.evalMul` |
| 241 | 41 | `nlinarith` (line 62, AM–GM with `sq_nonneg` hints) |
| **234** | 253 | `Positivity.evalMul` |
| **127** | 374 | `Positivity.evalMul` |
| 87 | 397 | `Positivity.evalRpow` |
| 57 | 202 | `linarith` |
| 35 | 553 | `Positivity.evalMul` |
| 34 | 615 | `linarith` |

**The distribution is NOT uniform.** Three `evalMul` calls = 766 ms of the ~1.25 s
total positivity work. The other ~30 sites average **≈8 ms each**.

## 3. A/B confirmation (stub-out probes, copies in `$TMPDIR`, `by positivity` → `by sorry`)

| variant | own-cost (replicates) | median own | Δ vs baseline |
|---|---|---|---|
| baseline (33 sites) | 3.40 / 3.04 / 3.07 / 3.20 / 3.06 | **3.10 s** | — |
| **top-3 sites only stubbed** (lines 296, 386, 538) | 2.54 / 2.58 / 2.45 / 2.44 | **2.50 s** | **−0.60 s** |
| all 33 positivity stubbed | 2.31 / 2.38 / 2.26 | **2.32 s** | **−0.78 s** |

⇒ **top-3 sites = 0.60 s (77 % of all positivity cost); remaining 30 sites = 0.19 s total.**
Stubbing is an upper bound: an explicit `mul_nonneg`/`Finset.sum_nonneg` term is not free
(~2–10 ms/site), so realistic recovery is **≈0.55 s for the 3 sites**, ≈0.10–0.15 s for the
other 30.

## 4. The three expensive sites — identical goal shape

All three close `0 ≤ (1 + dist)^(-α) * (∑ v ∈ (latticeGraph d).neighborFinset u, (1 + dist)^(-α))`,
i.e. a **product with a `Finset.sum` inside**, which forces `Positivity.evalMul` to recurse
through the `Finset.sum` extension and re-run `evalRpow` per summand:

| line | ms | context |
|---|---|---|
| **538** | ~405 | `darts_cross_sum_le_sharp_decay`: `(hsummable x z).sum_le_tsum _ (fun u' _ => by positivity)` |
| **296** | ~234 | `tsum_mul_neighborFinset_sum_pow_neg_le`: `have hlhs_nn : ∀ u, 0 ≤ … := fun u => by positivity` |
| **386** | ~127 | `summable_mul_neighborFinset_sum_pow_neg`: `Summable.of_nonneg_of_le (fun u => by positivity) …` |

Note: `research-C1-hls-positivity-sites.md` mis-classifies **line 296** as a flat single-rpow
goal in the "mechanically replaceable" bucket; the source at 296 is in fact the
sum-inside-product shape (its lines 293–296 span a multi-line `have`). Lines 386/538 were
already correctly flagged as "non-trivial". **So all three of the expensive sites live in the
research report's ≈7-site "non-trivial" class, and all ≈26 "mechanical" sites are cheap.**

The three share one goal shape ⇒ they are best fixed by **one shared private helper lemma**
(e.g. `pairKernelNeighborSum_nonneg : 0 ≤ (1+d x u)^(-α) * ∑ v ∈ neighborFinset u, (1+d z v)^(-α)`,
proved once as `mul_nonneg (Real.rpow_nonneg (by positivity) _) (Finset.sum_nonneg fun v _ => Real.rpow_nonneg (by positivity) _)`)
applied at all 3 call sites — a 3-call-site + 1-lemma edit, not a 33-site sweep.

## 5. What positivity replacement CANNOT touch

Residual own-cost after a full positivity sweep = **2.32 s (75 % of the module)**:
- `nlinarith` line 62 (241 ms) — genuine Positivstellensatz search with `sq_nonneg (a-b)` hints;
  not linear, not replaceable by `linarith` (same conclusion as the 978e8289 deep-dive for
  `HighTempMassGap`).
- typeclass inference 1.35 s — diffuse (`MulRightMono`/`MulLeftMono`/`OrderedSemiring` chains
  from `mul_le_mul_of_nonneg_left`/`calc`), no repeated instance worth caching (max single 20–30 ms).
- `linarith` 137 ms, `ring` 119 ms, `norm_num` 45 ms, `simp` 99 ms — all sub-100 ms, diffuse.

## 6. ROI verdict

**LIMITED — do the 3 sites, do NOT do the blanket 33-site sweep.**

- There is **no #4695-type outlier** here. #4695 was one 7390 ms call = 74 % of a 9.95 s module.
  The best call here is 405 ms = 13 % of a 3.10 s module — **18× smaller**.
- But the 3-site fix is **better ROI-per-site than #4699**: #4699 spent 4 sites for −0.9 s
  (0.22 s/site); this is 3 sites (+1 helper lemma) for **−0.55…0.60 s (≈0.19 s/site)** with
  strictly lower risk (nonnegativity side-goals, not arithmetic rewriting), and the three sites
  collapse into a single reusable lemma.
- The other **30 sites are worth 0.19 s in total (~8 ms each)** — after replacement overhead the
  net gain is ~0.1 s. A 30-site medium-risk edit for ~3 % of module own-cost is **not justified**;
  it also churns 30 proof lines and raises review cost for no measurable benefit.

### Priority list (do in this order, or as one PR)
| prio | site | expected gain | risk |
|---|---|---|---|
| 1 | line 538 (`darts_cross_sum_le_sharp_decay`) | ~0.40 s | low (nonneg side-goal under `sum_le_tsum`) |
| 2 | line 296 (`tsum_mul_neighborFinset_sum_pow_neg_le`) | ~0.23 s | low |
| 3 | line 386 (`summable_mul_neighborFinset_sum_pow_neg`) | ~0.12 s | low |
| — | remaining 30 `positivity` sites | ~0.10 s net, total | not worth it — **skip** |
| — | `nlinarith` line 62 | 0 (not convertible) | — |

Recommended shape: one `private lemma` for the shared goal + 3 call-site replacements.
Expected module own-cost after: **≈2.5 s** (from 3.10 s, −19 %).

## 7. Relative rank vs the rest of the repo (no re-measurement; per `refactor-buildtime-deepdive-978e8289.md`)

Own-cost ranking of the remaining hot tier (deep-dive items 3–13):
1. `ClusterExpansion/TwoPointCorrelationInfiniteAnalytic` 3.92 s — DIFFUSE (typeclass 2.2 s, max call 62 ms)
2. `TheoremEtaLe1/Contraction/Factor` 3.36 s — DIFFUSE (max call = 448 ms `refine`, structural, not exploitable)
3. `Inequalities/ClusterConditioningFiberSplit` 3.23 s — DIFFUSE (13× `Nonempty` @26 ms ≈ 0.34 s, marginal)
4. `TheoremEtaLe1/HighTempMassGap` 2.97 s — DIFFUSE (4 nlinarith 0.87 s, genuinely nonlinear)
5. **`PseudoMass/HLSSharpPairBound` 2.84 s (re-measured 3.10 s)** — has the **largest exploitable
   single call in the whole tier (405 ms)**
6. `LeeYang/IsingApplication` 2.53 s — DIFFUSE
7. `ClusterExpansion/FieldAvoidingRatio` 2.38 s — DIFFUSE

⇒ HLS is only #5 by own-cost, but it holds the **#1 remaining *actionable* concentration**:
every larger module's cost is diffuse or structurally unavoidable, whereas HLS's is 3 identical
tactic calls removable by one lemma. Confirms the deep-dive's global conclusion (no silver bullet
left) while correcting its HLS-specific estimate: the deep-dive said "convert ALL ~30 for ~0.8–1.0 s,
30-site medium-risk, low ROI" — measurement shows **3 sites give 0.60 s of that**, so the useful
fraction is cheap and the rest should be dropped.

## 8. Regression prevention
- Add a profiler budget gate for this module: fail if own-cost > 3.0 s (post-fix headroom from ~2.5 s).
  Same gate already suggested for `BallBoundaryInfinite` (< 4 s).
- Style rule (write-time, cheaper than after-the-fact profiling): **forbid `positivity` on goals
  containing `Finset.sum`/`tsum`** — that is exactly the shape that costs 100–400 ms here; use
  `Finset.sum_nonneg`/`tsum_nonneg` + a per-term proof instead. Flat products/rpow `positivity`
  (~8 ms) are fine and should NOT be linted.
- Keep the A/B stub method (`by positivity` → `by sorry` on a `$TMPDIR` copy, `real − import`,
  ≥3 replicates) as the standard attribution technique; per-call profiler attribution alone only
  resolves to declaration-start lines.

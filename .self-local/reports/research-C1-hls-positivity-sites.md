# Research: C1 — `positivity` sites in HLSSharpPairBound.lean

Target: `IsingModel/PseudoMass/HLSSharpPairBound.lean` (637 lines, 11 `theorem`s,
4 imports: `PseudoMassFromParamsRegularity`, `HLSCorrelationCapstone`,
`HLSConvolutionSharp`, `NeighborDegree`).

## 1. All `positivity` call sites (33 total)

Goal shapes fall into a small number of recurring atoms:
`d := latticeDistance d _ _ : ℕ` (cast to ℝ, always `≥ 0`), and
`(1 + (d:ℝ)) ^ (-α)` / `(2:ℝ) ^ α` (real `rpow`, base `> 0` ⇒ value `> 0`, base
`≥ 0` ⇒ value `≥ 0` regardless of exponent sign).

| line | enclosing context (goal being closed) | shape |
|---|---|---|
| 55 | `fun z => by positivity` — 1st arg of `Summable.of_nonneg_of_le`, goal `0 ≤ (1+d(x,z))^(-α)*(1+d(y,z))^(-α)` | product of two rpow-nonneg |
| 59 | `Real.rpow_mul (by positivity)` — goal `0 ≤ 1 + (latticeDistance d x z : ℝ)` | sum 1 + cast-nat |
| 61 | same pattern (y,z) | sum 1 + cast-nat |
| 84 | `fun z => by positivity`, goal `0 ≤ (1+d(x,z))^(-α)*(1+d(y,z))^(-α)` | product of two rpow-nonneg |
| 87 | `Real.rpow_nonneg (by positivity) _` — goal `0 ≤ 1+(latticeDistance d x y:ℝ)` | sum 1 + cast-nat |
| 95 | `ENNReal.ofReal_mul (by positivity)` — goal `0 ≤ (1+d(x,z))^(-α)` | single rpow-nonneg |
| 135 | `(by positivity)` for `hαnn : 0 ≤ (α:ℝ)` where `α:ℕ` | `Nat.cast_nonneg α` (trivial named lemma) |
| 136 | `by positivity`, goal `0 < 4*C^2*Chls` (hC_pos, hChls_pos in scope) | product of positives/squares |
| 167 (`by norm_num`, not positivity) | — | — |
| 198 | `by positivity`, goal `0 ≤ 4*C^2` | product of nonneg (norm_num const × sq) |
| 221 | `(by positivity)` inside `rpow_neg_half_le hαnn (by positivity) hlow` — goal `0 ≤ 1+(latticeDistance d z v:ℝ)` (arg name unclear, likely base positivity) | sum 1 + cast-nat |
| 235 | `have hMnn : 0 ≤ M := by rw [hM]; positivity` — `M = 2^α * (1+dist)^(-α)` | product of two rpow-nonneg (one base literal `2`) |
| 271 | `by positivity`, goal `0 < 2*(d:ℝ)*2^α*C0` (needs `d>0`, only available as `hd_one`/`hdpos` fact in context, not a hint positivity derives from the raw ℕ cast) | product of positives, **relies on context hyp `hdpos`/`hd_one`** |
| 285 | `mul_le_mul_of_nonneg_left (...) (by positivity)`, goal `0 ≤ (1+d(x,u))^(-α)` | single rpow-nonneg |
| 296 | `fun u => by positivity`, goal `0 ≤ (1+d(z,v))^(-α)` | single rpow-nonneg |
| 314 | `mul_le_mul_of_nonneg_left (...) (by positivity)`, goal `0 ≤ 2*d*2^α` | product of nonneg (nat cast × const-base rpow) |
| 340 | `have hdw_nn := by positivity`, goal `0 ≤ (latticeDistance d x w:ℝ)` | cast-nat nonneg |
| 344 | `positivity` (terminal tactic after `rw`), goal `0 ≤ 2*Cf*(1+d)^(-α)` (x=w case, RHS after subst) | product incl. rpow-nonneg |
| 351 | `have hMd_nn := by positivity`, goal `0 ≤ M*(latticeDistance d x w:ℝ)` (`hMpos` in scope) | product, needs `hMpos.le` |
| 386 | `fun u => by positivity`, goal `0 ≤ (1+d(x,u))^(-α)*(∑ ... )` — **sum inside `Finset.sum`**, each term itself an rpow | product incl. `Finset.sum_nonneg` over rpow-nonneg terms — **more work than a flat `mul_nonneg` chain** |
| 392 | `mul_le_mul_of_nonneg_left (...) (by positivity)`, goal `0 ≤ (1+d(x,u))^(-α)` | single rpow-nonneg |
| 430 | `by positivity`, goal `0 < (2:ℝ)^α` (`α:ℕ` here; ordinary `pow`, not `rpow`) | `pow_pos (by norm_num) α` |
| 447 | `fun u => by rw [hA]; positivity`, goal `0 ≤ (1+d(x,u))^(-α)` | single rpow-nonneg |
| 448 | same shape for `B` | single rpow-nonneg |
| 478 | `mul_le_mul_of_nonneg_left _ (by positivity)`, goal `0 ≤ (2*Cf)^2` | `sq_nonneg` |
| 504 | `Finset.sum_le_sum_of_subset_of_nonneg _ (fun w _ _ => by positivity)`, goal `0 ≤ (1+d(z,w))^(-α)` | single rpow-nonneg |
| 538 | `(hsummable x z).sum_le_tsum _ (fun u' _ => by positivity)`, goal `0 ≤ (1+d(x,u'))^(-α)*(∑ ...)` | product incl. `Finset.sum_nonneg` (same shape as 386) |
| 546 | `mul_le_mul_of_nonneg_left hfinle (by positivity)`, goal `0 ≤ (2*Cf)^2` | `sq_nonneg` |
| 548 | `mul_le_mul_of_nonneg_left (hC0bd x z) (by positivity)`, goal `0 ≤ (2*Cf)^2` | `sq_nonneg` |
| 575 | `mul_pos (...) (by positivity)`, goal `0 < (2:ℝ)^α` (`α:ℕ`, ordinary `pow`) | `pow_pos (by norm_num) α` |
| 576 | `by positivity`, goal `0 < Ct^2 * C0` (`hCt_pos`, `hC0` in scope) | product of positives |
| 583 | `have hdx_nn := by positivity`, goal `0 ≤ (latticeDistance d x z:ℝ)` | cast-nat nonneg |
| 584 | same for `y,z` | cast-nat nonneg |
| 597 | `fun z => by positivity`, goal `0 ≤ 1/(1+(t*d)^α) * (1/(1+(t*d)^α))` — **has division**, `α:ℕ` ordinary `pow` | product of two `1/pow_nonneg` (division, not rpow) |
| 612 | `mul_le_mul_of_nonneg_left (...) (by positivity)`, goal `0 ≤ Ct^2` | `sq_nonneg` |

Non-`positivity` heavy tactics also present: `nlinarith [sq_nonneg (a-b), ha2, hb2]`
at line 62 (AM–GM step, algebraic — not a `positivity` candidate),
`norm_num`/`div_le_div_of_nonneg_left` at 133/167/354/371 (small, not targeted by C1).

## 2. Classification

- **Machine-replaceable (mechanical, single/product-of-atoms nonneg or pos)**:
  lines 59, 61, 84 (via `mul_nonneg`+`Real.rpow_nonneg`), 87, 95, 135
  (`Nat.cast_nonneg`), 198, 221, 285, 296, 314, 340, 351, 392, 430, 447, 448,
  478, 504, 546, 548, 575, 583, 584, 597 (`div_nonneg`+`pow_nonneg`), 612.
  ≈ **26 sites** — these are all `mul_nonneg`/`add_nonneg`/`Real.rpow_nonneg`/
  `pow_nonneg`/`pow_pos`/`sq_nonneg`/`Nat.cast_nonneg`/`div_nonneg` compositions
  with hypotheses already visible or trivially derivable in-line, directly
  analogous to the PR #4695 pattern.
- **Non-trivial / needs care**: lines 55, 136, 176→235 (`hMnn`), 271, 344, 386,
  538, 576. ≈ **7 sites**:
  - 55, 84 restated as one product goal but nested inside a `fun z => by
    positivity` lambda passed as a *first-class argument* — mechanically
    still just `mul_nonneg (Real.rpow_nonneg h1 _) (Real.rpow_nonneg h2 _)`,
    but replacing requires supplying `h1`/`h2` inline (no pre-existing
    `have`), i.e. more verbose than a flat context-hypothesis substitution.
  - 136, 271, 576: strict-positivity (`0 <`) goals built from products of
    several named positivity facts (`hC_pos`, `hChls_pos`, `hd_one`/`hdpos`,
    `hC0`, `hCt_pos`) — mechanical but multi-hypothesis `mul_pos` chains.
  - 235 (`hMnn`): product of a literal-base rpow (`2^α`) and a
    sum-cast-base rpow — two-level composition.
  - 344: post-`subst`/`rw` terminal `positivity` closing a compound RHS
    (`2*Cf*(1+d)^(-α)`) with no visible intermediate `have`s to reuse.
  - 386, 538: goal is `0 ≤ f(u) * (∑_{v} g(v))`, i.e. involves
    `Finset.sum_nonneg` over an inner sum, not just flat `mul_nonneg` —
    structurally different from the #4695 pattern (which had no `Finset.sum`
    inside the positivity goal).

**Conclusion**: **≈26 mechanically replaceable, ≈7 non-trivial** (of 33
total `positivity` sites). The dominant reusable idiom across the file is
`Real.rpow_nonneg (base-nonneg proof) _` for `(1+dist)^(-α)` terms (rpow with
real exponent, base always `≥ 0`) and `Nat.cast_nonneg` for
`(latticeDistance ... : ℝ) ≥ 0`; `pow_pos (by norm_num) α` for `(2:ℝ)^α` where
`α:ℕ` (ordinary `pow`, not `rpow`) — note lines 271/314/430/575 mix both
`rpow` (`α:ℝ`) and ordinary `pow` (`α:ℕ`) forms depending on which theorem's
type-class context is in scope, so a blind copy-paste pattern will not work
uniformly; each site's `α` type must be checked before choosing
`Real.rpow_nonneg`/`Real.rpow_pos_of_pos` vs. `pow_nonneg`/`pow_pos`.

## 3. Other heavy tactics in the file (not `positivity`, informational only)

- `nlinarith [sq_nonneg (a - b), ha2, hb2]` — line 62 (single call, AM–GM
  algebraic step).
- `norm_num` — lines 133, 167, 354, 371 (small, discharging numeric facts
  like `(0:ℝ) < 4` or `2 ≠ 0`; not build-time hot-spots by inspection).
- No `decide`, no large `simp` calls in this file.

## 4. PR #4695 reference pattern (`git show 5e4b887b`)

Single-line diff in
`IsingModel/Concrete/LatticeGraphCorrelation/TheoremEtaLe1/BallBoundaryInfinite.lean:194`:
```
- positivity
+ exact add_nonneg (mul_nonneg h1 h2) (mul_nonneg h3 h4)
```
where `h1..h4` were already-proven nonnegativity facts for the four factors
(via `correlationInfinite_nonneg`), sitting directly above the `positivity`
call in a `have`-chain. The pattern is: goal = sum of two products of
already-named nonneg hypotheses → replace with `add_nonneg (mul_nonneg _ _)
(mul_nonneg _ _)`.

**Applicability to HLSSharpPairBound.lean**: most sites here do *not* have
pre-existing named `have`s for each rpow factor (unlike #4695's `h1..h4`), so
the direct analogue requires inlining `Real.rpow_nonneg (base-proof) _` calls
rather than referencing existing hypotheses — i.e. a bit more verbose per
site but structurally the same substitution strategy. Profiling of actual
per-call cost (which sites are the expensive interpreted `positivity` calls,
analogous to the 7.4s outlier at BallBoundaryInfinite.lean:194) was **not**
performed here (build/profiler runs are out of scope for this research
task) — recommend running `lake env lean -Dprofiler=true` per-site (or on
the whole file) before committing to which subset of the ~26 mechanical
sites to replace, since not all `positivity` calls are necessarily
expensive; some may be cheap single-atom lookups not worth touching.

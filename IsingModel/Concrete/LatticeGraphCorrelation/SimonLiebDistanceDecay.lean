import IsingModel.Inequalities.HighTemp.SimonLiebInfinite
import IsingModel.Concrete.LatticeGraphBED.NeighborDegree

/-!
# GJ §17.5 / §5.1 — Simon--Lieb one-step decay on the integer lattice

This module begins the prefactor-free distance-decay program for the
infinite-volume two-point function on `ℤ^d` (Issue #2931, Phase 3a).  The
single-step Simon--Lieb peeling inequality
`correlationInfinite_simon_lieb_latticeGraph` bounds a non-adjacent pair
correlation by `βJ` times the sum of the neighbour correlations of one endpoint.
Combined with the degree bound `latticeGraph_degree_le` (degree `≤ 2d`), a
uniform bound `C` on the neighbour correlations gives the clean one-step estimate
`⟨σ_iσ_j⟩^∞ ≤ βJ · 2d · C`.

Iterating the single-vertex bound *does* give a prefactor-free geometric distance
decay: `correlationInfinite_latticeGraph_le_betaJ_two_d_pow_of_dist_gt` proves
`⟨σ_iσ_j⟩^∞ ≤ (βJ·2d)^{dist(i,j) − 1}` by induction (each peeling step reduces the
separation by `1`; the final step at distance `1` from `j` contributes the base
factor `1`). The one-step estimate alone stalls at `βJ·2d`; this module builds the
single-vertex bound, its two-step (`dist ≥ 3`) and full iterated forms. The
separating-surface (ball-boundary) Simon--Lieb argument `ball_boundary_simon_lieb`
peels an entire cubic shell at once and avoids the near-`j` defect (one contraction
per shell rather than per lattice step); it is used for the contraction-factor decay
and the volume-convergence rate (Issue #2931).

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §5.1, pp. 76--79; §17.5, Theorem
  17.5.1 proof and Lemma 17.5.2, pp. 311--312.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, Prop. 9.31,
  p. 428.
-/

namespace IsingModel
namespace Ambient

/-- **Simon--Lieb one-step decay bound from a uniform neighbour bound**: for a
non-adjacent pair `i ≠ j` on `ℤ^d`, if every neighbour `k` of `i` satisfies
`⟨σ_kσ_j⟩^∞ ≤ C` for some `C ≥ 0`, then the Simon--Lieb peeling inequality and the
degree bound `degree i ≤ 2d` give
`⟨σ_iσ_j⟩^∞ ≤ βJ · 2d · C`.

This lemma proves the single-vertex one-step estimate; iterating it gives the
geometric decay `(βJ·2d)^{dist−1}`
(`correlationInfinite_latticeGraph_le_betaJ_two_d_pow_of_dist_gt`). The
separating-surface `ball_boundary_simon_lieb` argument on cubic shells gives the
defect-free one-contraction-per-shell decay used for the volume-convergence rate
(Issue #2931). -/
theorem correlationInfinite_latticeGraph_le_of_neighbors_le
    {d : ℕ} {β J : ℝ} (hβJ : 0 ≤ β * J)
    {i j : Fin d → ℤ} (hij : i ≠ j) (hnadj : ¬ (latticeGraph d).Adj i j)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ k ∈ (latticeGraph d).neighborFinset i,
      correlationInfinite (latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {k, j} ≤ C) :
    correlationInfinite (latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}
      ≤ β * J * (2 * d) * C := by
  have hSL := correlationInfinite_simon_lieb_latticeGraph hβJ hij hnadj
  -- Bound the neighbour sum by `card · C`.
  have hsum :
      ∑ k ∈ (latticeGraph d).neighborFinset i,
        correlationInfinite (latticeGraph d) (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {k, j}
        ≤ ((latticeGraph d).neighborFinset i).card * C := by
    calc ∑ k ∈ (latticeGraph d).neighborFinset i,
          correlationInfinite (latticeGraph d) (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {k, j}
        ≤ ∑ _k ∈ (latticeGraph d).neighborFinset i, C :=
          Finset.sum_le_sum hC
      _ = ((latticeGraph d).neighborFinset i).card • C := by rw [Finset.sum_const]
      _ = ((latticeGraph d).neighborFinset i).card * C := by rw [nsmul_eq_mul]
  -- The neighbour count is at most `2d`.
  have hcard : (((latticeGraph d).neighborFinset i).card : ℝ) ≤ 2 * d := by
    have hdeg := latticeGraph_degree_le d i
    rw [← SimpleGraph.card_neighborFinset_eq_degree] at hdeg
    calc (((latticeGraph d).neighborFinset i).card : ℝ)
        ≤ ((2 * d : ℕ) : ℝ) := by exact_mod_cast hdeg
      _ = 2 * d := by push_cast; ring
  calc correlationInfinite (latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}
      ≤ β * J *
          ∑ k ∈ (latticeGraph d).neighborFinset i,
            correlationInfinite (latticeGraph d) (cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {k, j} := hSL
    _ ≤ β * J * (((latticeGraph d).neighborFinset i).card * C) :=
        mul_le_mul_of_nonneg_left hsum hβJ
    _ ≤ β * J * ((2 * d) * C) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard hC0) hβJ
    _ = β * J * (2 * d) * C := by ring

/-- **Uniform one-step decay for non-adjacent pairs**: applying the one-step
bound with the universal correlation bound `⟨σ_kσ_j⟩^∞ ≤ 1` gives, for any
non-adjacent pair `i ≠ j` on `ℤ^d`,
`⟨σ_iσ_j⟩^∞ ≤ βJ · 2d`.

The bound holds under the standing hypothesis `0 ≤ βJ`; in the strict
high-temperature regime `0 ≤ βJ·2d < 1` it improves the universal `≤ 1` bound to
a contraction factor `< 1` for every non-adjacent pair, the first quantitative
decay step of the prefactor-free iteration (Issue #2931, Phase 3a). -/
theorem correlationInfinite_latticeGraph_le_betaJ_two_d_of_not_adj
    {d : ℕ} {β J : ℝ} (hβJ : 0 ≤ β * J)
    {i j : Fin d → ℤ} (hij : i ≠ j) (hnadj : ¬ (latticeGraph d).Adj i j) :
    correlationInfinite (latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}
      ≤ β * J * (2 * d) := by
  have h :=
    correlationInfinite_latticeGraph_le_of_neighbors_le hβJ hij hnadj (C := 1)
      (by norm_num)
      (fun k _ => correlationInfinite_le_one (latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {k, j})
  simpa using h

/-- **Two-step decay for far pairs**: for a pair `i, j` on `ℤ^d` at lattice distance
`≥ 3`, applying the one-step bound with the neighbour bound `⟨σ_kσ_j⟩^∞ ≤ βJ·2d`
(every neighbour `k` of `i` is still non-adjacent to `j`, since
`dist(k,j) ≥ dist(i,j) − 1 ≥ 2`) gives
`⟨σ_iσ_j⟩^∞ ≤ (βJ·2d)²`.

This is the second iterate of the prefactor-free Simon–Lieb spatial decay: in the
strict high-temperature regime `0 ≤ βJ·2d < 1` it squares the contraction factor for
pairs separated by distance `≥ 3`, the next quantitative decay step toward the
volume-convergence rate (GJ §17.5, Issue #2931 Phase 3a). -/
theorem correlationInfinite_latticeGraph_le_betaJ_two_d_sq_of_dist_ge_three
    {d : ℕ} {β J : ℝ} (hβJ : 0 ≤ β * J)
    {i j : Fin d → ℤ} (hdist : 3 ≤ latticeDistance d i j) :
    correlationInfinite (latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}
      ≤ (β * J * (2 * d)) ^ 2 := by
  have hij : i ≠ j := by
    intro h; rw [h, latticeDistance_self] at hdist; omega
  have hnadj : ¬ (latticeGraph d).Adj i j := by
    rw [latticeGraph_adj_iff_latticeDistance_eq_one]; omega
  have hC0 : (0 : ℝ) ≤ β * J * (2 * d) := mul_nonneg hβJ (by positivity)
  have hC : ∀ k ∈ (latticeGraph d).neighborFinset i,
      correlationInfinite (latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {k, j} ≤ β * J * (2 * d) := by
    intro k hk
    rw [SimpleGraph.mem_neighborFinset] at hk
    have hik1 : latticeDistance d i k = 1 :=
      (latticeGraph_adj_iff_latticeDistance_eq_one d i k).mp hk
    have htri : latticeDistance d i j
        ≤ latticeDistance d i k + latticeDistance d k j :=
      latticeDistance_triangle d i k j
    have hkj : k ≠ j := by
      intro h; rw [h] at hik1; omega
    have hknadj : ¬ (latticeGraph d).Adj k j := by
      rw [latticeGraph_adj_iff_latticeDistance_eq_one]; omega
    exact correlationInfinite_latticeGraph_le_betaJ_two_d_of_not_adj hβJ hkj hknadj
  have h := correlationInfinite_latticeGraph_le_of_neighbors_le hβJ hij hnadj hC0 hC
  calc correlationInfinite (latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}
      ≤ β * J * (2 * d) * (β * J * (2 * d)) := h
    _ = (β * J * (2 * d)) ^ 2 := by ring

/-- **Iterated naive Simon–Lieb geometric decay**: for any `n` and a pair `i, j` on
`ℤ^d` at lattice distance `≥ n + 1`,
`⟨σ_iσ_j⟩^∞ ≤ (βJ·2d)^n`.
Equivalently, `⟨σ_iσ_j⟩^∞ ≤ (βJ·2d)^{dist(i,j) − 1}`: the naive single-vertex peeling
iterates `dist − 1` times, the final step (a neighbour at distance `1` from `j`, i.e.
adjacent) contributing the base factor `1` rather than `βJ·2d`.

Proof by induction on `n`. Base `n = 0`: `(βJ·2d)^0 = 1` bounds every correlation. Step:
for `dist(i,j) ≥ n + 2`, each neighbour `k` of `i` has `dist(k,j) ≥ n + 1` (reverse
triangle), so the inductive hypothesis gives `⟨σ_kσ_j⟩^∞ ≤ (βJ·2d)^n`; the one-step
peeling bound `correlationInfinite_latticeGraph_le_of_neighbors_le` with `C = (βJ·2d)^n`
then yields `(βJ·2d)^{n+1}`.

This is the prefactor-free geometric decay obtained purely from the integer-lattice
Simon–Lieb peeling, with explicit base `βJ·2d` (no contraction-factor abstraction and no
ball-boundary shell-contraction axiom); in the strict high-temperature regime
`0 ≤ βJ·2d < 1` it is genuine exponential distance decay (GJ §17.5, Issue #2931). -/
theorem correlationInfinite_latticeGraph_le_betaJ_two_d_pow_of_dist_gt
    {d : ℕ} {β J : ℝ} (hβJ : 0 ≤ β * J) :
    ∀ (n : ℕ) (i j : Fin d → ℤ), n + 1 ≤ latticeDistance d i j →
      correlationInfinite (latticeGraph d) (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}
        ≤ (β * J * (2 * d)) ^ n := by
  have hbase : (0 : ℝ) ≤ β * J * (2 * d) := mul_nonneg hβJ (by positivity)
  intro n
  induction n with
  | zero =>
    intro i j _
    simpa using correlationInfinite_le_one (latticeGraph d) (cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}
  | succ m ih =>
    intro i j hdist
    have hij : i ≠ j := by
      intro h; rw [h, latticeDistance_self] at hdist; omega
    have hnadj : ¬ (latticeGraph d).Adj i j := by
      rw [latticeGraph_adj_iff_latticeDistance_eq_one]; omega
    have hC : ∀ k ∈ (latticeGraph d).neighborFinset i,
        correlationInfinite (latticeGraph d) (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {k, j} ≤ (β * J * (2 * d)) ^ m := by
      intro k hk
      rw [SimpleGraph.mem_neighborFinset] at hk
      have hik1 : latticeDistance d i k = 1 :=
        (latticeGraph_adj_iff_latticeDistance_eq_one d i k).mp hk
      have htri : latticeDistance d i j
          ≤ latticeDistance d i k + latticeDistance d k j :=
        latticeDistance_triangle d i k j
      exact ih k j (by omega)
    have h := correlationInfinite_latticeGraph_le_of_neighbors_le hβJ hij hnadj
      (pow_nonneg hbase m) hC
    calc correlationInfinite (latticeGraph d) (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}
        ≤ β * J * (2 * d) * (β * J * (2 * d)) ^ m := h
      _ = (β * J * (2 * d)) ^ (m + 1) := by rw [pow_succ]; ring

/-! ## Step 119 plan Step 5.7g: Simon-Lieb exp-form correlation bound -/

/-- **`simonLiebRate`**: the explicit Simon-Lieb high-temperature exponential
decay rate
`simonLiebRate β J d = -log(β·J·(2d))`.

In the high-temperature regime `0 < β·J·2d < 1`, `simonLiebRate > 0`,
yielding genuine exponential decay. This is the rate matching the existing
`correlationInfinite_latticeGraph_le_betaJ_two_d_pow_of_dist_gt` Simon-Lieb
peeling output, and parallels `highTempExpRate β J = -log(tanh(β·J))`
(`IsingModel/Conditioning/CorrelationRates/ExpRate.lean`) and the rate
`-log(β·J·(2d))` used inside `cubicTanhProfileBound`. -/
noncomputable def simonLiebRate (β J : ℝ) (d : ℕ) : ℝ :=
  -Real.log (β * J * (2 * d))

/-- **`simonLiebRate` is nonneg in the high-temperature regime**
(Step 119 plan Step 5.7g).

If `0 ≤ β·J·(2d) ≤ 1`, then `simonLiebRate β J d ≥ 0`. Strict positivity
requires the strict bound `0 < β·J·(2d) < 1` (see `simonLiebRate_pos`); the
endpoint `β·J·(2d) = 0` uses Lean's total `Real.log 0 = 0` and only yields
`simonLiebRate = 0`. -/
theorem simonLiebRate_nonneg {β J : ℝ} {d : ℕ}
    (hβJd_nn : 0 ≤ β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1) :
    0 ≤ simonLiebRate β J d := by
  unfold simonLiebRate
  exact neg_nonneg.mpr (Real.log_nonpos hβJd_nn hβJd_le)

/-- **`simonLiebRate` is strictly positive in the strict high-temperature
regime** (Step 119 plan Step 5.7g).

If `0 < β·J·(2d) < 1`, then `simonLiebRate β J d > 0`. -/
theorem simonLiebRate_pos {β J : ℝ} {d : ℕ}
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * (2 * d) < 1) :
    0 < simonLiebRate β J d := by
  unfold simonLiebRate
  exact neg_pos.mpr (Real.log_neg hβJd_pos hβJd_lt)

/-- **`(β·J·2d)^n = exp(-(simonLiebRate · n))` in the strict high-temperature
regime** (Step 119 plan Step 5.7g).

Direct calculation: for `0 < β·J·(2d)`, `(β·J·2d)^n = exp(n·log(β·J·2d))
= exp(-n·simonLiebRate)`. -/
theorem betaJ_two_d_pow_eq_exp_neg_simonLiebRate_mul {β J : ℝ} {d : ℕ}
    (hβJd_pos : 0 < β * J * (2 * d)) (n : ℕ) :
    (β * J * (2 * d)) ^ n = Real.exp (-(simonLiebRate β J d) * (n : ℝ)) := by
  unfold simonLiebRate
  rw [← Real.exp_log (pow_pos hβJd_pos n), Real.log_pow]
  ring_nf

/-- **Simon-Lieb decay in exp form**: under strict high-temperature
`0 < β·J·(2d)`, for `n + 1 ≤ latticeDistance d i j`,
`correlationInfinite ≤ exp(-(simonLiebRate · n))`
(Step 119 plan Step 5.7g).

Direct combination of
`correlationInfinite_latticeGraph_le_betaJ_two_d_pow_of_dist_gt` and the exp
identity `betaJ_two_d_pow_eq_exp_neg_simonLiebRate_mul`. Provides the
exp-form analytic correlation upper bound input shape consumed by the Step
5.7e/f composers (PRs #3176, #3177), with rate `simonLiebRate β J d
= -log(β·J·2d)`.

Note: the exponent is `n = dist - 1` (the Simon-Lieb peeling output), not
`dist`; converting to `correlation ≤ exp(-(M·dist))` for direct use with
Step 5.7e introduces a constant prefactor `exp(simonLiebRate) = 1/(β·J·2d)`.
This is a known artifact of the peeling structure (the final neighbour step
at distance 1 contributes factor 1 rather than `β·J·2d`). -/
theorem correlationInfinite_latticeGraph_le_exp_neg_simonLiebRate_pow_of_dist_gt
    {d : ℕ} {β J : ℝ} (hβJ : 0 ≤ β * J) (hβJd_pos : 0 < β * J * (2 * d)) :
    ∀ (n : ℕ) (i j : Fin d → ℤ), n + 1 ≤ latticeDistance d i j →
      correlationInfinite (latticeGraph d) (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}
        ≤ Real.exp (-(simonLiebRate β J d) * (n : ℝ)) := by
  intro n i j hdist
  have hbase := correlationInfinite_latticeGraph_le_betaJ_two_d_pow_of_dist_gt
    hβJ n i j hdist
  rw [betaJ_two_d_pow_eq_exp_neg_simonLiebRate_mul hβJd_pos n] at hbase
  exact hbase

/-! ## Step 119 plan Step 5.7h: dist ≥ 2 exp-form with M/2 rate -/

set_option linter.style.longLine false in
/-- **Simon-Lieb dist ≥ 2 exp-form bound with rate `simonLiebRate / 2`**
(Step 119 plan Step 5.7h).

For `dist ≥ 2`, the off-by-one `n = dist - 1` in Simon-Lieb peeling can be
absorbed into the rate: monotonicity of `exp` gives
`exp(-(M·(dist - 1))) ≤ exp(-(M/2·dist))` precisely because
`dist - 1 ≥ dist/2` for `dist ≥ 2`. Combined with PR #3178's exp-form
Simon-Lieb bound `correlationInfinite ≤ exp(-(simonLiebRate·n))` at
`n := dist - 1`, this yields the cleaner shape
`correlationInfinite ≤ exp(-(simonLiebRate/2 · dist))` directly usable with
the Step 5.7e/f composers (PRs #3176, #3177).

Hypotheses:
- `0 ≤ β·J` for Simon-Lieb peeling.
- `0 < β·J·(2d)` for the exp identity (positivity of base for `log`).
- `β·J·(2d) ≤ 1` to ensure `simonLiebRate ≥ 0`; otherwise the monotonicity
  step `exp(-(M·(dist - 1))) ≤ exp(-(M/2·dist))` reverses.
- `2 ≤ latticeDistance d i j` for `dist - 1 ≥ dist/2`.

The `dist = 1` case is excluded: Simon-Lieb gives only `correlation ≤ 1`
there, so no exponential decay survives; handling adjacent pairs requires a
separate single-step input. -/
theorem correlationInfinite_latticeGraph_le_exp_neg_half_simonLiebRate_dist_of_dist_ge_two
    {d : ℕ} {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {i j : Fin d → ℤ} (hdist : 2 ≤ latticeDistance d i j) :
    correlationInfinite (latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}
      ≤ Real.exp (-(simonLiebRate β J d / 2) *
          (latticeDistance d i j : ℝ)) := by
  set n : ℕ := latticeDistance d i j - 1 with hn_def
  have hn_pos : 1 ≤ n := by rw [hn_def]; omega
  have hn_plus_one_le : n + 1 ≤ latticeDistance d i j := by rw [hn_def]; omega
  have h_simonLieb :=
    correlationInfinite_latticeGraph_le_exp_neg_simonLiebRate_pow_of_dist_gt
      hβJ hβJd_pos n i j hn_plus_one_le
  have hsL_nn : 0 ≤ simonLiebRate β J d :=
    simonLiebRate_nonneg (le_of_lt hβJd_pos) hβJd_le
  have hdist_ge_two_real : (2 : ℝ) ≤ (latticeDistance d i j : ℝ) := by
    exact_mod_cast hdist
  have hn_eq : (n : ℝ) = (latticeDistance d i j : ℝ) - 1 := by
    rw [hn_def]
    have : 1 ≤ latticeDistance d i j := by omega
    rw [Nat.cast_sub this]
    simp
  have h_dist_pred_ge_half :
      simonLiebRate β J d / 2 * (latticeDistance d i j : ℝ) ≤
        simonLiebRate β J d * ((latticeDistance d i j : ℝ) - 1) := by
    have : (latticeDistance d i j : ℝ) ≤ 2 * ((latticeDistance d i j : ℝ) - 1) := by
      linarith
    have := mul_le_mul_of_nonneg_left this hsL_nn
    linarith
  have h_exp_mono : Real.exp (-(simonLiebRate β J d) * (n : ℝ)) ≤
      Real.exp (-(simonLiebRate β J d / 2) * (latticeDistance d i j : ℝ)) := by
    apply Real.exp_le_exp.mpr
    rw [hn_eq]
    linarith
  exact h_simonLieb.trans h_exp_mono

/-! ## Ferromagnetic-form Simon--Lieb helpers -/

/-- **Simon--Lieb power decay from `Ferromagnetic ⟨J, 0, β⟩`**. -/
theorem correlationInfinite_latticeGraph_le_betaJ_two_d_pow_of_ferromagnetic_dist_gt
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (n : ℕ) (i j : Fin d → ℤ) (hdist : n + 1 ≤ latticeDistance d i j) :
    correlationInfinite (latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}
      ≤ (β * J * (2 * d)) ^ n :=
  correlationInfinite_latticeGraph_le_betaJ_two_d_pow_of_dist_gt
    (mul_nonneg hf.hβ.le hf.hJ) n i j hdist

/-- **Simon--Lieb exp-form decay from `Ferromagnetic ⟨J, 0, β⟩`**. -/
theorem correlationInfinite_latticeGraph_le_exp_neg_simonLiebRate_pow_of_ferromagnetic_dist_gt
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d))
    (n : ℕ) (i j : Fin d → ℤ) (hdist : n + 1 ≤ latticeDistance d i j) :
    correlationInfinite (latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}
      ≤ Real.exp (-(simonLiebRate β J d) * (n : ℝ)) :=
  correlationInfinite_latticeGraph_le_exp_neg_simonLiebRate_pow_of_dist_gt
    (mul_nonneg hf.hβ.le hf.hJ) hβJd_pos n i j hdist

/-- **Simon--Lieb dist ≥ 2 `M / 2` form from
`Ferromagnetic ⟨J, 0, β⟩`**. -/
theorem
correlationInfinite_latticeGraph_le_exp_neg_half_simonLiebRate_dist_of_ferromagnetic_dist_ge_two
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {i j : Fin d → ℤ} (hdist : 2 ≤ latticeDistance d i j) :
    correlationInfinite (latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}
      ≤ Real.exp (-(simonLiebRate β J d / 2) *
          (latticeDistance d i j : ℝ)) :=
  correlationInfinite_latticeGraph_le_exp_neg_half_simonLiebRate_dist_of_dist_ge_two
    (mul_nonneg hf.hβ.le hf.hJ) hβJd_pos hβJd_le hdist

/-- **`simonLiebRate β J d ≥ 0` from `Ferromagnetic ⟨J, 0, β⟩`
and high temperature**. -/
theorem simonLiebRate_nonneg_of_ferromagnetic_high_temp
    {β J : ℝ} {d : ℕ}
    (_hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_nn : 0 ≤ β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1) :
    0 ≤ simonLiebRate β J d :=
  simonLiebRate_nonneg hβJd_nn hβJd_le

/-- **`simonLiebRate β J d > 0` from `Ferromagnetic ⟨J, 0, β⟩`
and strict high temperature**. -/
theorem simonLiebRate_pos_of_ferromagnetic_strict_high_temp
    {β J : ℝ} {d : ℕ}
    (_hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * (2 * d) < 1) :
    0 < simonLiebRate β J d :=
  simonLiebRate_pos hβJd_pos hβJd_lt

/-- **High-temperature `β·J·2d ≥ 0` from `Ferromagnetic`**. -/
theorem ferromagnetic_implies_betaJ_two_d_nonneg
    {J β : ℝ} {d : ℕ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ)) :
    0 ≤ β * J * (2 * d) :=
  mul_nonneg (mul_nonneg hf.hβ.le hf.hJ) (by positivity)

/-- **High-temperature `(β·J·2d) ∈ [0, 1)` from `Ferromagnetic` and `< 1`**. -/
theorem betaJ_two_d_mem_Ico_of_ferromagnetic_lt_one
    {β J : ℝ} {d : ℕ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_lt : β * J * (2 * d) < 1) :
    β * J * (2 * d) ∈ Set.Ico (0 : ℝ) 1 :=
  ⟨ferromagnetic_implies_betaJ_two_d_nonneg hf, hβJd_lt⟩

/-- **`simonLiebRate` is nonnegative from `Ferromagnetic` and `β·J·2d ≤ 1`**. -/
theorem simonLiebRate_nonneg_of_ferromagnetic_le_one
    {β J : ℝ} {d : ℕ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_le : β * J * (2 * d) ≤ 1) :
    0 ≤ simonLiebRate β J d :=
  simonLiebRate_nonneg_of_ferromagnetic_high_temp hf
    (ferromagnetic_implies_betaJ_two_d_nonneg hf) hβJd_le

end Ambient
end IsingModel

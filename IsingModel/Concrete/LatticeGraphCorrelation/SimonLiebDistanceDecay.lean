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

Note that naive single-vertex neighbour peeling does **not** itself iterate to a
genuine distance decay: at distance `2` it still only yields `βJ·2d` (a neighbour
adjacent to `j` contributes a correlation that can only be bounded by `1`), and
no `≤ βJ·2d` bound holds for adjacent pairs.  Prefactor-free exponential distance
decay instead requires the separating-surface (ball-boundary) Simon--Lieb
argument `ball_boundary_simon_lieb`, which peels an entire separating edge set at
once; assembling that for cubic shells is the remaining Phase-3a work
(Issue #2931).  The estimates here are the single-vertex building blocks.

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

This lemma proves only the single-vertex one-step estimate.  It does not by
itself give genuine distance decay (single-vertex peeling stalls at `βJ·2d`);
the prefactor-free exponential decay requires the separating-surface
`ball_boundary_simon_lieb` argument applied to cubic shells, which is the
remaining Phase-3a work (Issue #2931). -/
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

end Ambient
end IsingModel

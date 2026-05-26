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
`⟨σ_iσ_j⟩^∞ ≤ βJ · 2d · C`, the inductive step that iterates (over the lattice
distance) to the prefactor-free exponential decay `⟨σ_iσ_j⟩^∞ ≤ (βJ·2d)^{dist}`.

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

This lemma proves only the single-step estimate.  It is *intended* as the
inductive step of a prefactor-free distance-decay iteration — a bound on the
distance-`n` shell around `j` would propagate inward to the distance-`(n+1)`
shell with one extra factor `βJ·2d`, so that iterating `dist(i,j)` times would
yield `(βJ·2d)^{dist(i,j)}` without the volume-dependent prefactor of the naive
finite-volume bound — but that full distance induction is not proved here and
remains the substantive remaining work (Issue #2931, Phase 3a). -/
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

end Ambient
end IsingModel

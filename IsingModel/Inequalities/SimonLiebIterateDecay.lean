import IsingModel.Inequalities.SimonLiebIterate
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Exponential decay of the two-point function via Simon-Lieb iteration (FFS Ch 12 / GJ §18)

The iterated Simon-Lieb kernel (`simonLiebIterate`) yields an exponential-decay
bound on the two-point function in terms of the **graph distance**: if the target
`j` is more than `n` steps away from `i`, the `n`-step transfer never reaches the
absorbing diagonal value `K(j, j) = 1`, so every branch decays geometrically:

  `simonLiebIterate ⟨J,0,β⟩ j n i ≤ (β J · D)^n`   whenever  `n < dist i j`,

with `D` a vertex-degree bound.  Specialising `n = dist(i, j) − 1` gives the
**exponential decay of the correlation**

  `⟨σ_i σ_j⟩ ≤ (β J · D)^{dist(i, j) − 1}`,

which tends to `0` with the distance in the high-temperature regime `β J · D < 1`.
This is the random-walk (Simon-Lieb) derivation of high-temperature correlation
decay.

## References

* Fernández–Fröhlich–Sokal, *Random Walks, Critical Phenomena, and Triviality*
  (1992), Ch 12.
* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.
* Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017), §3.7.3.
-/

namespace IsingModel

open Finset

namespace Ambient

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
/-- **Distance-localised geometric bound on the iterated kernel** (FFS Ch 12 /
GJ §18): if the target `j` is more than `n` graph-steps from `i`
(`n < dist i j`), then `simonLiebIterate ⟨J,0,β⟩ j n i ≤ (β J · D)^n`.

Induction on `n`: the base (`0 < dist i j`, so the kernel is `K(j, i) ≤ 1`); for
`n+1`, `dist i j > n+1` forces `i ≠ j`, and every neighbour `u ∼ i` still has
`dist u j > n` (the edge moves the distance by at most one, `Adj.diff_dist_adj`),
so the induction hypothesis bounds each branch by `(β J · D)^n`; summing over the
`≤ D` neighbours and multiplying by `β J` gives `(β J · D)^{n+1}`. -/
theorem simonLiebIterate_le_pow_of_lt_dist (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    [DecidableRel (inducedGraph G Λ).Adj]
    {β J : ℝ} (hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ))
    {D : ℕ} (hD : ∀ v : ↑Λ, ((inducedGraph G Λ).neighborFinset v).card ≤ D)
    (j : ↑Λ) (n : ℕ) (i : ↑Λ) (hdist : n < (inducedGraph G Λ).dist i j) :
    simonLiebIterate G Λ (⟨J, 0, β⟩ : IsingParams ℝ) j n i ≤ (β * J * (D : ℝ)) ^ n := by
  have hβJ : 0 ≤ β * J := mul_nonneg hf.hβ.le hf.hJ
  have hβJD : 0 ≤ β * J * (D : ℝ) := mul_nonneg hβJ (Nat.cast_nonneg D)
  induction n generalizing i with
  | zero =>
    rw [simonLiebIterate_zero, pow_zero]
    exact simonLiebKernel_le_one G Λ _ j i
  | succ n ih =>
    have hij : i ≠ j := by
      rintro rfl
      rw [SimpleGraph.dist_self] at hdist
      exact absurd hdist (by omega)
    rw [simonLiebIterate_succ, if_neg hij]
    calc β * J * ∑ u ∈ (inducedGraph G Λ).neighborFinset i,
            simonLiebIterate G Λ (⟨J, 0, β⟩ : IsingParams ℝ) j n u
        ≤ β * J * ∑ _u ∈ (inducedGraph G Λ).neighborFinset i, (β * J * (D : ℝ)) ^ n := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun u hu => ?_) hβJ
          have hadj : (inducedGraph G Λ).Adj i u := by
            rwa [SimpleGraph.mem_neighborFinset] at hu
          have htri := hadj.diff_dist_adj (u := j)
          have hdu : n < (inducedGraph G Λ).dist u j := by
            rw [SimpleGraph.dist_comm] at hdist ⊢
            omega
          exact ih u hdu
      _ = β * J * (((inducedGraph G Λ).neighborFinset i).card * (β * J * (D : ℝ)) ^ n) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ β * J * ((D : ℝ) * (β * J * (D : ℝ)) ^ n) := by
          refine mul_le_mul_of_nonneg_left ?_ hβJ
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hD i) (pow_nonneg hβJD n)
      _ = (β * J * (D : ℝ)) ^ (n + 1) := by rw [pow_succ]; ring

set_option linter.unusedDecidableInType false in
/-- **Exponential decay of the two-point function** (FFS Ch 12 / GJ §18): for
distinct, reachable `i, j` (`0 < dist i j`),

`⟨σ_i σ_j⟩ ≤ (β J · D)^{dist(i, j) − 1}`,

which decays exponentially in the graph distance in the high-temperature regime
`β J · D < 1`.  Obtained by composing `correlation_inducedGraph_le_simonLiebIterate`
(`⟨σ_i σ_j⟩ ≤ simonLiebIterate … (dist−1) i`) with the distance-localised geometric
bound at `n = dist(i, j) − 1`. -/
theorem correlation_inducedGraph_le_pow_dist (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    [DecidableRel (inducedGraph G Λ).Adj]
    {β J : ℝ} (hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ))
    {D : ℕ} (hD : ∀ v : ↑Λ, ((inducedGraph G Λ).neighborFinset v).card ≤ D)
    {i j : ↑Λ} (hdist : 0 < (inducedGraph G Λ).dist i j) :
    correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}
      ≤ (β * J * (D : ℝ)) ^ ((inducedGraph G Λ).dist i j - 1) := by
  have hij : i ≠ j := by
    rintro rfl
    rw [SimpleGraph.dist_self] at hdist
    exact absurd hdist (lt_irrefl 0)
  have hlt : (inducedGraph G Λ).dist i j - 1 < (inducedGraph G Λ).dist i j := by omega
  exact le_trans
    (correlation_inducedGraph_le_simonLiebIterate G Λ hf hij ((inducedGraph G Λ).dist i j - 1))
    (simonLiebIterate_le_pow_of_lt_dist G Λ hf hD j _ i hlt)

end Ambient

end IsingModel

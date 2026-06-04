import IsingModel.Inequalities.WalkSumRepresentation
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Infinite walk-sum bound on the two-point function (FFS Ch 12 / GJ §18)

In the high-temperature regime `β J · D < 1` the finite-horizon walk-sum bound
(`correlation_inducedGraph_le_sum_walkSum_add_pow`) passes to the limit: the
geometric remainder `(β J · D)^n` vanishes and the walk sum converges, giving the
**random-walk upper representation**

  `⟨σ_i σ_j⟩ ≤ ∑_{k≥1} walkSum (β J) i j k`,

the discrete random-walk (FFS Ch 12) bound on the Ising two-point function.

The two analytic inputs are the geometric domination `walkSum (β J) i j n ≤
(β J · D)^n` (the number of length-`n` walks is at most `D^n`) and the resulting
summability of the walk sum for `β J · D < 1`.

## References

* Fernández–Fröhlich–Sokal, *Random Walks, Critical Phenomena, and Triviality*
  (1992), Ch 12.
* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.
* Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017), §3.7.3.
-/

namespace IsingModel

open Finset Filter Topology

namespace Ambient

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Geometric domination of the walk sum**: `walkSum z i j n ≤ (z · D)^n` for
`z ≥ 0` and a vertex-degree bound `D` (the number of length-`n` walks from `i` is
at most `D^n`).  Induction on `n` via the neighbour recurrence `walkSum_succ`. -/
theorem walkSum_le_pow_degree_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    {z : ℝ} (hz : 0 ≤ z) {D : ℕ} (hD : ∀ v : V, (G.neighborFinset v).card ≤ D)
    (i j : V) (n : ℕ) :
    walkSum G z i j n ≤ (z * (D : ℝ)) ^ n := by
  have hzD : 0 ≤ z * (D : ℝ) := mul_nonneg hz (Nat.cast_nonneg D)
  induction n generalizing i with
  | zero =>
    rw [pow_zero, walkSum_zero]
    split <;> norm_num
  | succ n ih =>
    rw [walkSum_succ]
    calc z * ∑ u ∈ G.neighborFinset i, walkSum G z u j n
        ≤ z * ∑ _u ∈ G.neighborFinset i, (z * (D : ℝ)) ^ n :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun u _ => ih u) hz
      _ = z * ((G.neighborFinset i).card * (z * (D : ℝ)) ^ n) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ z * ((D : ℝ) * (z * (D : ℝ)) ^ n) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (by exact_mod_cast hD i) (pow_nonneg hzD n)) hz
      _ = (z * (D : ℝ)) ^ (n + 1) := by rw [pow_succ]; ring

/-- **Summability of the walk sum at high temperature**: for `z ≥ 0` and
`z · D < 1`, the positive-length walk sum `n ↦ walkSum z i j (n+1)` is summable
(dominated by the geometric series `(z · D)^{n+1}`). -/
theorem summable_walkSum_of_lt_one (G : SimpleGraph V) [DecidableRel G.Adj]
    {z : ℝ} (hz : 0 ≤ z) {D : ℕ} (hD : ∀ v : V, (G.neighborFinset v).card ≤ D)
    (hlt : z * (D : ℝ) < 1) (i j : V) :
    Summable (fun n : ℕ => walkSum G z i j (n + 1)) := by
  have hzD : 0 ≤ z * (D : ℝ) := mul_nonneg hz (Nat.cast_nonneg D)
  have hgeo : Summable (fun n : ℕ => (z * (D : ℝ)) ^ (n + 1)) := by
    simpa only [pow_succ'] using (summable_geometric_of_lt_one hzD hlt).mul_left (z * (D : ℝ))
  exact Summable.of_nonneg_of_le (fun n => walkSum_nonneg G hz i j (n + 1))
    (fun n => walkSum_le_pow_degree_bound G hz hD i j (n + 1)) hgeo

omit [Fintype V] in
set_option linter.unusedDecidableInType false in
/-- **Random-walk upper representation of the two-point function** (FFS Ch 12 /
GJ §18): in the high-temperature regime `β J · D < 1`, for distinct `i ≠ j`,

`⟨σ_i σ_j⟩ ≤ ∑_{k≥1} walkSum (β J) i j k`,

the infinite-sum (discrete random-walk) bound on the Ising two-point function.
The finite-horizon bound `⟨σ_i σ_j⟩ ≤ ∑_{k=1}^{n} walkSum k + (β J · D)^n` passes to
the limit: the geometric remainder vanishes and the walk sum converges. -/
theorem correlation_inducedGraph_le_tsum_walkSum (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    [DecidableRel (inducedGraph G Λ).Adj]
    {β J : ℝ} (hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ))
    {D : ℕ} (hD : ∀ v : ↑Λ, ((inducedGraph G Λ).neighborFinset v).card ≤ D)
    (hlt : β * J * (D : ℝ) < 1) {i j : ↑Λ} (hij : i ≠ j) :
    correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}
      ≤ ∑' k : ℕ, walkSum (inducedGraph G Λ) (β * J) i j (k + 1) := by
  have hβJ : 0 ≤ β * J := mul_nonneg hf.hβ.le hf.hJ
  have hβJD : 0 ≤ β * J * (D : ℝ) := mul_nonneg hβJ (Nat.cast_nonneg D)
  have hsummable : Summable (fun n : ℕ => walkSum (inducedGraph G Λ) (β * J) i j (n + 1)) :=
    summable_walkSum_of_lt_one (inducedGraph G Λ) hβJ hD hlt i j
  have hpartial : Tendsto (fun n : ℕ =>
      ∑ k ∈ Finset.range n, walkSum (inducedGraph G Λ) (β * J) i j (k + 1)) atTop
      (𝓝 (∑' k : ℕ, walkSum (inducedGraph G Λ) (β * J) i j (k + 1))) :=
    hsummable.hasSum.tendsto_sum_nat
  have hrem : Tendsto (fun n : ℕ => (β * J * (D : ℝ)) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hβJD hlt
  have hsum : Tendsto (fun n : ℕ =>
      (∑ k ∈ Finset.range n, walkSum (inducedGraph G Λ) (β * J) i j (k + 1))
        + (β * J * (D : ℝ)) ^ n) atTop
      (𝓝 (∑' k : ℕ, walkSum (inducedGraph G Λ) (β * J) i j (k + 1))) := by
    simpa using hpartial.add hrem
  exact ge_of_tendsto' hsum
    (fun n => correlation_inducedGraph_le_sum_walkSum_add_pow G Λ hf hD hij n)

end Ambient

end IsingModel

import IsingModel.Concrete.LatticeGraphCorrelation.SimonLiebDecayLatticeDistance
import IsingModel.Concrete.CubicBoxConnectivity
import IsingModel.AmbientLattice.Exhaustion

/-!
# Infinite-volume Simon-Lieb exponential decay on ℤ^d (FFS Ch 12 / GJ §18)

The finite-volume random-walk (Simon-Lieb) decay bound
`correlation_inducedLatticeGraph_le_pow_latticeDistance` is **uniform in the
volume**: each cubic-exhaustion stage `cubicBox d n` carries the same bound
`(β J · 2d)^{latticeDistance(i, j) − 1}` (independent of `n`).  Hence the
thermodynamic limit `correlationInfinite = ⨆_n correlationAlongExhaustion`
inherits it:

  `⟨σ_i σ_j⟩_∞ ≤ (β J · 2d)^{latticeDistance(i, j) − 1}`,

the infinite-volume exponential decay of the ℤ^d Ising two-point function in the
high-temperature regime `β J · 2d < 1`, derived by the random-walk (Simon-Lieb)
route.  Reachability of distinct sites at every stage is discharged by the cubic
box connectivity (`inducedGraph_cubicBox_dist_pos`); stages not yet containing the
pair contribute `0`.

This is a contribution to the project's central long-term goal — the
infinite-volume limit.

## References

* Fernández–Fröhlich–Sokal, *Random Walks, Critical Phenomena, and Triviality*
  (1992), Ch 12.
* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.
* Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017), §3.7.3.
-/

namespace IsingModel

namespace Ambient

open Finset

/-- **Infinite-volume Simon-Lieb exponential decay on ℤ^d** (FFS Ch 12 / GJ §18):
in the high-temperature regime `β J · 2d < 1`, for distinct sites `i ≠ j`,

`correlationInfinite (latticeGraph d) (cubicExhaustion d) ⟨J,0,β⟩ {i, j}
   ≤ (β J · 2d)^{latticeDistance(i, j) − 1}`,

genuine exponential decay in the ℓ¹ lattice distance.  Each exhaustion stage is
bounded uniformly by the finite-volume random-walk bound
`correlation_inducedLatticeGraph_le_pow_latticeDistance` (reachability via cubic
box connectivity); stages not containing the pair contribute `0`; the supremum is
then bounded by `ciSup_le`. -/
theorem correlationInfinite_latticeGraph_le_pow_latticeDistance (d : ℕ)
    {β J : ℝ} (hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ))
    (hlt : β * J * (2 * (d : ℝ)) < 1) {i j : Fin d → ℤ} (hij : i ≠ j) :
    correlationInfinite (IsingModel.latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}
      ≤ (β * J * (2 * (d : ℝ))) ^ (IsingModel.latticeDistance d i j - 1) := by
  have hCnn : (0 : ℝ) ≤ (β * J * (2 * (d : ℝ))) ^ (IsingModel.latticeDistance d i j - 1) := by
    apply pow_nonneg
    exact mul_nonneg (mul_nonneg hf.hβ.le hf.hJ) (by positivity)
  rw [correlationInfinite_eq_ciSup]
  apply ciSup_le
  intro n
  by_cases hsub : ({i, j} : Finset (Fin d → ℤ)) ⊆ (cubicExhaustion d).volume n
  · have hi : i ∈ (cubicExhaustion d).volume n :=
      (Finset.insert_subset_iff.mp hsub).1
    have hj : j ∈ (cubicExhaustion d).volume n :=
      Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp hsub).2
    rw [correlationAlongExhaustion, dif_pos hsub, correlationΛ,
      liftFinset_pair hsub hi hj]
    have hne : (⟨i, hi⟩ : ↑((cubicExhaustion d).volume n)) ≠ ⟨j, hj⟩ :=
      fun h => hij (congrArg Subtype.val h)
    have hdist := inducedGraph_cubicBox_dist_pos d n hne
    exact correlation_inducedLatticeGraph_le_pow_latticeDistance d ((cubicExhaustion d).volume n)
      hf hlt.le hdist
  · rw [correlationAlongExhaustion, dif_neg hsub]
    exact hCnn

end Ambient

end IsingModel

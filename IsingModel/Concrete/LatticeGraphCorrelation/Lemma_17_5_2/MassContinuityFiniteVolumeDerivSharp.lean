import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityFiniteVolumeDerivCombine
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.LebowitzAlongExhaustion

/-!
# GJ §17.5 Theorem 17.5.1 — PR-FV3i: the finite-volume sharp β-derivative bound (p.312)

The finite-volume analogue of `abs_deriv_correlationInfinite_le_sharp` (#4359) — but at the finite
volume `A = volume n` (no `n → ∞` limit): for a non-adjacent in-box binding pair `x ≠ z`,
`|∂_β ⟨φ_x φ_z⟩_{σ,A}| ≤ ⟨sharp(C)⟩·⟨φ_x φ_z⟩_{σ,A}`,
where `⟨sharp(C)⟩ = J·[2(1+(m⁻_FV·r)^α)e^{m⁻_FV}C(1+r)^{−(2α−d)}] + J·[4d(1+2^α)e^{m⁻_FV}]`.

The finite-stage β-derivative is non-negative (GKS-II,
`correlationAlongExhaustion_latticeGraph_beta_deriv_nonneg`) and bounded by `c·⟨sharp⟩` divided by
`c` (PR-FV3h); together they give the absolute bound directly, with **no limit argument**.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, p.~312.
-/

namespace IsingModel
namespace Ambient

open Real

/-- **Finite-volume sharp β-derivative bound** (GJ p.312): for a non-adjacent in-box binding pair
`x ≠ z`, `∃ C>0, |∂_β ⟨φ_x φ_z⟩_{σ,A}| ≤ ⟨sharp(C)⟩·⟨φ_x φ_z⟩_{σ,A}`.  The finite-stage derivative
is non-negative (GKS-II) and `≤ c·⟨sharp⟩` (PR-FV3h), so its absolute value is bounded by
`⟨sharp⟩·c`. -/
theorem abs_deriv_correlationAlongExhaustion_le_sharp_finiteRegionFV {α d : ℕ} (hα : 1 ≤ α)
    (hd : 1 ≤ d) (hαd : d < 2 * α) (hαd2 : α < d) {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β) {n : ℕ}
    (hA : (finiteRegionDistinctPairs ((cubicExhaustion d).volume n)).Nonempty)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    (hx : x ∈ (cubicExhaustion d).volume n) (hz : z ∈ (cubicExhaustion d).volume n)
    (hbind : pseudoMassFromParamsAtPairFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n x z
      = finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA) :
    ∃ C : ℝ, 0 < C ∧
      |deriv (fun β' => Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d)
          (cubicExhaustion d) (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β|
      ≤ (J * (2 * (1 + (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA
              * (latticeDistance d x z : ℝ)) ^ α)
            * Real.exp (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA)
            * (C * (1 + (latticeDistance d x z : ℝ)) ^ (-(2 * (α : ℝ) - (d : ℝ)))))
          + J * ((4 * d : ℝ) * ((1 + (2 : ℝ) ^ α)
              * Real.exp (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA)
            + (1 + (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA) ^ α)
              * Real.exp (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA)
              / 2)))
        * Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n := by
  obtain ⟨C, hC, hbd⟩ :=
    combined_derivative_div_c_bound_tight_finiteRegionFV hα hd hαd hαd2 hJ hβ hA hxz
      hx hz hbind
  refine ⟨C, hC, ?_⟩
  have hxzsub : ({x, z} : Finset (Fin d → ℤ)) ⊆ (cubicExhaustion d).volume n := by
    intro w hw; rw [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact hx
    · exact hz
  have hc_pos : 0 < Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d)
      (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n :=
    (correlationAlongExhaustion_cubicExhaustion_pair_active hJ hβ hxz hxzsub).1
  have hnn : 0 ≤ deriv (fun β' => Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d)
      (cubicExhaustion d) (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β :=
    correlationAlongExhaustion_latticeGraph_beta_deriv_nonneg (cubicExhaustion d) J β hJ.le hβ
      {x, z} n
  rw [abs_of_nonneg hnn]
  exact (div_le_iff₀ hc_pos).mp hbd

end Ambient
end IsingModel

import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityFiniteVolumeDerivCombine
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityConvolutionMassUniformDart
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityFiniteVolumeMassLower
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityGlobalMassLowerIcc

/-!
# GJ §17.5 Theorem 17.5.1 — PR-FV4b: the mass-uniform combined β-derivative `/c` bound (p.312)

The β-uniform version of `combined_derivative_div_c_bound_tight_finiteRegionFV` (PR-FV3h): a
**single** convolution constant `C` works for *every* `β` in the high-temperature window `[β₁,β₂]`
(`β₂·J·2d < 1/2`), every stage `n`, and every in-box binding pair.  This is possible because the
finite-region mass `m⁻_FV(σ,n)` is bounded below by `mmin := globalPseudoMassDistRestrictedRate α
d J β₂ > 0` uniformly on the window (#4360 lower + #4380 `globalPseudoMassDist ≤ m⁻_FV`), hence the
**mass-uniform** dart convolution (`dart_profile_sum_le_convolution_mass_uniform`, the same `C` for
all scales `≥ mmin`) applies at every `β`.

This is exactly what the GJ p.312 uniform-in-`σ`(-and-`A`) Lipschitz estimate requires: the per-pair
sharp β-derivative bound with a `β`-independent convolution constant.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, p.~312.
-/

namespace IsingModel
namespace Ambient

open Real

/-- **Mass-uniform combined finite-volume β-derivative `/c` bound** (GJ p.312): for the
high-temperature window `[β₁,β₂]` (`0<β₁≤β₂`, `β₂·J·2d<1/2`), there is one `C>0` such that for every
`β ∈ [β₁,β₂]`, every `n`, and every in-box binding pair `x≠z`, the c-cancelling β-derivative `/c`
bound holds with this single `C`.  The finite-region mass is `≥ mmin` on the window (#4360 + #4380),
so the mass-uniform dart convolution supplies the
`β`-independent `C` to the core combine. -/
theorem combined_derivative_div_c_bound_mass_uniform_finiteRegionFV {α d : ℕ} (hα : 1 ≤ α)
    (hd : 1 ≤ d) (hαd : d < 2 * α) (hαd2 : α < d) {J β₁ β₂ : ℝ} (hJ : 0 < J) (hβ₁ : 0 < β₁)
    (hβ₁₂ : β₁ ≤ β₂) (hβ₂_half : β₂ * J * (2 * d) < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (β : ℝ), β ∈ Set.Icc β₁ β₂ →
      ∀ (hA : (finiteRegionDistinctPairs ((cubicExhaustion d).volume n)).Nonempty)
        (x z : Fin d → ℤ), x ≠ z →
        x ∈ (cubicExhaustion d).volume n → z ∈ (cubicExhaustion d).volume n →
        pseudoMassFromParamsAtPairFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n x z
          = finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA →
        deriv (fun β' => Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d)
            (cubicExhaustion d) (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β
          / Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n
        ≤ J * (2 * (1 + (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA
                * (latticeDistance d x z : ℝ)) ^ α)
              * Real.exp (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA)
              * (C * (1 + (latticeDistance d x z : ℝ)) ^ (-(2 * (α : ℝ) - (d : ℝ)))))
          + J * ((4 * d : ℝ) * ((1 + (2 : ℝ) ^ α)
              * Real.exp (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA)
            + (1 + (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA) ^ α)
              * Real.exp (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA)
              / 2)) := by
  have hβ₂_pos : 0 < β₂ := lt_of_lt_of_le hβ₁ hβ₁₂
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hd)
  have hβ₂Jd_pos : 0 < β₂ * J * (2 * d) := by positivity
  obtain ⟨C, hC, hCconv_u⟩ := dart_profile_sum_le_convolution_mass_uniform hd hαd hαd2
    (globalPseudoMassDistRestrictedRate_pos (α := α) hβ₂Jd_pos hβ₂_half)
  refine ⟨C, hC, fun n β hβmem hA x z hxz hx hz hbind => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβ₁ hβmem.1
  have hmmin_le : globalPseudoMassDistRestrictedRate α d J β₂
      ≤ finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA :=
    le_trans (globalPseudoMassDist_ge_restrictedRate_beta2 hα (by omega) hJ hβ₁ hβ₂_half β hβmem)
      (globalPseudoMassDist_le_finiteRegionPseudoMassDistFV hα hJ hβ hA)
  exact combined_derivative_div_c_bound_core_finiteRegionFV hα hJ hβ hA hxz hx hz hbind C
    (fun x' z' => hCconv_u _ hmmin_le n x' z')

end Ambient
end IsingModel

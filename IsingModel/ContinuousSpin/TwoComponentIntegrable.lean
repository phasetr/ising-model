import IsingModel.ContinuousSpin.TwoComponentSystem
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-!
# Integrability of the two-component single-spin weight (GJ §4.7)

The `SO(2)`-invariant single-spin density `exp(−A·(t²+q²)² − σ·(t²+q²))` is
integrable over `ℝ²` for `A > 0`, `σ ≥ 0`: in polar coordinates the radial
integral `∫₀^∞ r·exp(−A·r⁴ − σ·r²) dr` is finite (the quartic term forces
super-Gaussian decay), and the angular integral is `2π`.

This is the first integrability input toward the multi-site Gibbs measure of
Theorem 4.7.1 (Issue #3918).

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §4.7, (4.7.2)–(4.7.3), p. 70
-/

namespace IsingModel.ContinuousSpin

open Real MeasureTheory Set
open scoped ENNReal

/-- **Radial integrability**: `r ↦ r·exp(−A·r⁴ − σ·r²)` is integrable on
`(0, ∞)` for `A > 0`, `σ ≥ 0`. Dominated by `r·exp(−A·r⁴)` (Mathlib's
super-Gaussian) since `exp(−σr²) ≤ 1`. -/
theorem integrableOn_radial_single_spin {A σ : ℝ} (hA : 0 < A) (hσ : 0 ≤ σ) :
    IntegrableOn (fun r : ℝ => r * Real.exp (-A * r ^ 4 - σ * r ^ 2)) (Ioi 0) := by
  have hbase : IntegrableOn (fun r : ℝ => r ^ (1 : ℝ) * Real.exp (-A * r ^ (4 : ℝ)))
      (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) hA
  have h4 : (4 : ℝ) = ((4 : ℕ) : ℝ) := by norm_num
  have hbase' : IntegrableOn (fun r : ℝ => r * Real.exp (-A * r ^ 4)) (Ioi 0) := by
    refine hbase.congr_fun (fun r hr => ?_) measurableSet_Ioi
    rw [Real.rpow_one, h4, Real.rpow_natCast]
  refine Integrable.mono' hbase' ?_ ?_
  · refine (Continuous.aestronglyMeasurable ?_).restrict
    fun_prop
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun r hr => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (le_of_lt hr) (Real.exp_pos _).le)]
    have hexp_le : Real.exp (-A * r ^ 4 - σ * r ^ 2) ≤ Real.exp (-A * r ^ 4) := by
      apply Real.exp_le_exp.mpr
      have : 0 ≤ σ * r ^ 2 := mul_nonneg hσ (sq_nonneg r)
      linarith
    calc r * Real.exp (-A * r ^ 4 - σ * r ^ 2)
        ≤ r * Real.exp (-A * r ^ 4) :=
          mul_le_mul_of_nonneg_left hexp_le (le_of_lt hr)

/-- The `SO(2)`-invariant single-spin density `exp(−A(t²+q²)² − σ(t²+q²))`. -/
noncomputable def singleSpinDensity (A σ : ℝ) (ξ : ℝ × ℝ) : ℝ :=
  Real.exp (-A * (ξ.1 ^ 2 + ξ.2 ^ 2) ^ 2 - σ * (ξ.1 ^ 2 + ξ.2 ^ 2))

/-- The single-spin density is continuous. -/
theorem continuous_singleSpinDensity (A σ : ℝ) :
    Continuous (singleSpinDensity A σ) := by
  unfold singleSpinDensity
  fun_prop

/-- In polar coordinates the density at `(r·cosθ, r·sinθ)` is
`exp(−A·r⁴ − σ·r²)`. -/
theorem singleSpinDensity_polarCoord_symm (A σ : ℝ) (rθ : ℝ × ℝ) :
    singleSpinDensity A σ (polarCoord.symm rθ)
      = Real.exp (-A * rθ.1 ^ 4 - σ * rθ.1 ^ 2) := by
  obtain ⟨r, θ⟩ := rθ
  have hpolar : polarCoord.symm (r, θ) = (r * Real.cos θ, r * Real.sin θ) := rfl
  rw [hpolar]
  unfold singleSpinDensity
  have hnorm : (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
    have := Real.sin_sq_add_cos_sq θ
    nlinarith [this]
  rw [hnorm]
  congr 1
  ring

/-- **The two-component single-spin density is integrable** over `ℝ²` for
`A > 0`, `σ ≥ 0`: in polar coordinates the radial integral is finite. -/
theorem integrable_singleSpinDensity {A σ : ℝ} (hA : 0 < A) (hσ : 0 ≤ σ) :
    Integrable (singleSpinDensity A σ) := by
  have hmeas : AEStronglyMeasurable (singleSpinDensity A σ) volume :=
    (continuous_singleSpinDensity A σ).aestronglyMeasurable
  have hnn : 0 ≤ᵐ[volume] singleSpinDensity A σ :=
    Filter.Eventually.of_forall fun ξ => (Real.exp_pos _).le
  rw [← lintegral_ofReal_ne_top_iff_integrable hmeas hnn,
    ← lintegral_comp_polarCoord_symm
      (fun ξ => ENNReal.ofReal (singleSpinDensity A σ ξ))]
  -- the integrand on the target is `ofReal (r · exp (-A r⁴ - σ r²))`
  set g : ℝ → ENNReal :=
    fun r => ENNReal.ofReal (r * Real.exp (-A * r ^ 4 - σ * r ^ 2)) with hg
  have hint_eq : ∀ rθ ∈ polarCoord.target,
      ENNReal.ofReal rθ.1 • ENNReal.ofReal (singleSpinDensity A σ (polarCoord.symm rθ))
        = g rθ.1 := by
    intro rθ hrθ
    rw [singleSpinDensity_polarCoord_symm, smul_eq_mul, hg,
      ← ENNReal.ofReal_mul (le_of_lt hrθ.1)]
  rw [setLIntegral_congr_fun polarCoord.open_target.measurableSet hint_eq,
    show polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-π) π from rfl]
  -- the radial 1D lintegral is finite
  have hrad : IntegrableOn
      (fun r : ℝ => r * Real.exp (-A * r ^ 4 - σ * r ^ 2)) (Ioi 0) :=
    integrableOn_radial_single_spin hA hσ
  have hradnn : 0 ≤ᵐ[volume.restrict (Ioi 0)]
      fun r : ℝ => r * Real.exp (-A * r ^ 4 - σ * r ^ 2) :=
    (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun r hr =>
      mul_nonneg (le_of_lt hr) (Real.exp_pos _).le)
  have hrad_fin : (∫⁻ r in Ioi (0 : ℝ), g r) ≠ ∞ :=
    (lintegral_ofReal_ne_top_iff_integrable hrad.aestronglyMeasurable hradnn).mpr hrad
  have hgcont : Continuous fun r : ℝ => r * Real.exp (-A * r ^ 4 - σ * r ^ 2) := by
    fun_prop
  have hgmeas : Measurable g := by
    rw [hg]; exact hgcont.measurable.ennreal_ofReal
  -- factor the product lintegral: ∫⁻_{Ioi×ˢIoo} g(r) = volume(Ioo)·∫⁻_{Ioi} g
  have hfactor : (∫⁻ rθ in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, g rθ.1)
      = volume (Ioo (-π) π) * ∫⁻ r in Ioi (0 : ℝ), g r := by
    rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
      ← Measure.prod_restrict,
      lintegral_prod (fun rθ : ℝ × ℝ => g rθ.1)
        (hgmeas.comp measurable_fst).aemeasurable]
    simp_rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter]
    rw [lintegral_mul_const _ hgmeas, mul_comm]
  rw [hfactor]
  refine ENNReal.mul_ne_top ?_ hrad_fin
  rw [Real.volume_Ioo]
  exact ENNReal.ofReal_ne_top

end IsingModel.ContinuousSpin

import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempZeroBoundary

/-!
# ℤ^d monotonicity and a.e. differentiability on the closed half-line

Instantiates at `IsingModel.latticeGraph d`, for an arbitrary `Ambient.Exhaustion` of
`Fin d → ℤ` and a pair of sites at zero external field, the monotonicity of the
infinite-volume correlation on `Set.Ici 0` and, as a consequence through bounded variation,
its differentiability within `Set.Ici 0` at Lebesgue-almost every point. The statements cover
the inverse-temperature direction, under `0 ≤ J`, and the coupling direction, under `0 < β`.
No high-temperature condition is imposed, no condition is placed on the dimension, the
half-line reaches the origin, and the sites are not assumed distinct.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **MonotoneOn corr_∞ in β on the half-line Ici 0** (Step 183):
For `0 ≤ J`: corr_∞ is monotone non-decreasing in β on the entire half-line `Ici 0`.

Proof: at β > 0 use `correlationInfinite_monotone_beta` (Ioi 0);
at β = 0, corr_∞(0) = 0 ≤ corr_∞(β₂) by nonnegativity. -/
theorem correlationInfinite_monotoneOn_beta_Ici_zero
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (J : ℝ) (hJ : 0 ≤ J) :
    MonotoneOn
      (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Ici (0 : ℝ)) := by
  intro β₁ hβ₁ β₂ hβ₂ hβ
  simp only
  have hβ₁_nn : 0 ≤ β₁ := hβ₁
  rcases eq_or_lt_of_le hβ₁_nn with hβ₁0 | hβ₁_pos
  · rw [← hβ₁0, correlationInfinite_eq_zero_at_beta_zero]
    rcases eq_or_lt_of_le (hβ₁0.le.trans hβ) with hβ₂0 | hβ₂_pos
    · rw [← hβ₂0, correlationInfinite_eq_zero_at_beta_zero]
    · exact correlationInfinite_nonneg _ _ _ ⟨hJ, le_refl 0, hβ₂_pos⟩ _
  · have hβ₁_in : β₁ ∈ Set.Ioi (0 : ℝ) := hβ₁_pos
    have hβ₂_in : β₂ ∈ Set.Ioi (0 : ℝ) := hβ₁_pos.trans_le hβ
    exact correlationInfinite_monotone_beta (IsingModel.latticeGraph d) Λ hJ (le_refl 0) _
      hβ₁_in hβ₂_in hβ

/-- **A.e. differentiability of corr_∞ on Ici 0** (Step 183):
For `0 ≤ J`: `β ↦ corr_∞(β)` is differentiable within `Ici 0` at Lebesgue-a.e. β.

Proof: `MonotoneOn.locallyBoundedVariationOn` (Step 183 monotonicity) +
`LocallyBoundedVariationOn.ae_differentiableWithinAt`. No high-temperature condition needed. -/
theorem correlationInfinite_ae_differentiableWithinAt_beta_Ici_zero
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (J : ℝ) (hJ : 0 ≤ J) :
    ∀ᵐ β ∂MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ici (0 : ℝ)),
    DifferentiableWithinAt ℝ
      (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Ici (0 : ℝ)) β := by
  have hmono := correlationInfinite_monotoneOn_beta_Ici_zero Λ r_val s_val J hJ
  exact hmono.locallyBoundedVariationOn.ae_differentiableWithinAt measurableSet_Ici

/-- **MonotoneOn corr_∞ in J on the half-line Ici 0** (Step 237):
For `0 < β`: corr_∞ is monotone non-decreasing in J on the entire half-line `Ici 0`.

Direct J-direction analogue of Step 183. Direct application of
`correlationInfinite_monotone_J` at h = 0. -/
theorem correlationInfinite_monotoneOn_J_Ici_zero
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (β : ℝ) (hβ : 0 < β) :
    MonotoneOn
      (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Ici (0 : ℝ)) :=
  correlationInfinite_monotone_J (IsingModel.latticeGraph d) Λ (le_refl 0) hβ {r_val, s_val}

/-- **A.e. differentiability of corr_∞ on Ici 0 in J** (Step 237):
For `0 < β`: `J ↦ corr_∞(J)` is differentiable within `Ici 0` at Lebesgue-a.e. J.

Direct J-direction analogue of Step 183. Proof: `MonotoneOn.locallyBoundedVariationOn`
+ `LocallyBoundedVariationOn.ae_differentiableWithinAt`. No high-temperature condition. -/
theorem correlationInfinite_ae_differentiableWithinAt_J_Ici_zero
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (β : ℝ) (hβ : 0 < β) :
    ∀ᵐ J ∂MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ici (0 : ℝ)),
    DifferentiableWithinAt ℝ
      (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Ici (0 : ℝ)) J := by
  have hmono := correlationInfinite_monotoneOn_J_Ici_zero Λ r_val s_val β hβ
  exact hmono.locallyBoundedVariationOn.ae_differentiableWithinAt measurableSet_Ici

end Ambient
end IsingModel

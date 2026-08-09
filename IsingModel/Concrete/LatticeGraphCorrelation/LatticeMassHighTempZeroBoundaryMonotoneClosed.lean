import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempContinuousAt
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempZeroBoundary
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempZeroBoundaryContinuousOnClosed

/-!
# ℤ^d monotonicity and a.e. differentiability on a closed interval from the origin

Instantiates at `IsingModel.latticeGraph d`, for an arbitrary `Ambient.Exhaustion` of
`Fin d → ℤ` and a pair of sites at zero external field, the monotonicity of the
infinite-volume correlation on `Set.Icc 0 b` and, through bounded variation, its
differentiability within that interval at Lebesgue-almost every point. The statements are
given in the inverse-temperature direction, under `0 ≤ J`, and in the coupling direction,
under `0 < β`. Nothing further is assumed: the right endpoint `b` is an arbitrary real, no
high-temperature condition is imposed, no condition is placed on the dimension, and the sites
are not assumed distinct.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **MonotoneOn corr_∞ in β on closed interval [0, b]** (Step 179 helper):
The infinite-volume two-point function is monotone non-decreasing in β on `[0, b]`.

Proof: at β > 0 use `correlationInfinite_monotone_beta` (MonotoneOn `Ioi 0`);
at β = 0, corr_∞(0) = 0 ≤ corr_∞(β₂) by `correlationInfinite_nonneg`. -/
theorem correlationInfinite_monotoneOn_beta_zero_closed
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (J : ℝ) (hJ : 0 ≤ J) (b : ℝ) :
    MonotoneOn
      (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Icc 0 b) := by
  intro β₁ hβ₁ β₂ hβ₂ hβ
  -- Reduce lambda to be able to rewrite
  simp only
  rcases eq_or_lt_of_le hβ₁.1 with hβ₁0 | hβ₁_pos
  · -- β₁ = 0: corr_∞(0) = 0 ≤ corr_∞(β₂)
    rw [← hβ₁0, correlationInfinite_eq_zero_at_beta_zero]
    rcases eq_or_lt_of_le (hβ₁0.le.trans hβ) with hβ₂0 | hβ₂_pos
    · rw [← hβ₂0, correlationInfinite_eq_zero_at_beta_zero]
    · exact correlationInfinite_nonneg _ _ _ ⟨hJ, le_refl 0, hβ₂_pos⟩ _
  · -- β₁ > 0: use existing MonotoneOn on Ioi 0
    have hβ₁_in : β₁ ∈ Set.Ioi (0 : ℝ) := hβ₁_pos
    have hβ₂_in : β₂ ∈ Set.Ioi (0 : ℝ) := hβ₁_pos.trans_le hβ
    exact correlationInfinite_monotone_beta (IsingModel.latticeGraph d) Λ hJ (le_refl 0) _
      hβ₁_in hβ₂_in hβ

/-- **A.e. differentiability of corr_∞ on closed [0, b]** (Step 179):
For ferromagnetic h = 0, β ∈ [0, b]: `β ↦ corr_∞(β)` is differentiable within `[0, b]` at
Lebesgue-a.e. β.

Proof: corr_∞ is monotone on `[0, b]` (helper above), hence locally bounded variation
(`MonotoneOn.locallyBoundedVariationOn`), hence a.e. differentiable
(`LocallyBoundedVariationOn.ae_differentiableWithinAt`). Strengthens Step 171
from `[a, b]` (a > 0) to closed `[0, b]`. -/
theorem correlationInfinite_ae_differentiableWithinAt_beta_zero_closed
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (J : ℝ) (hJ : 0 ≤ J) (b : ℝ) :
    ∀ᵐ β ∂MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Icc 0 b),
    DifferentiableWithinAt ℝ
      (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Icc 0 b) β := by
  have hmono := correlationInfinite_monotoneOn_beta_zero_closed Λ r_val s_val J hJ b
  exact hmono.locallyBoundedVariationOn.ae_differentiableWithinAt measurableSet_Icc

/-- **MonotoneOn corr_∞ in J on closed interval [0, b]** (Step 233 helper):
For `0 < β`: `J ↦ corr_∞(r, s, J)` is monotone non-decreasing on `[0, b]`.

Direct J-direction analogue of `correlationInfinite_monotoneOn_beta_zero_closed`.
Proof: at J > 0 use `correlationInfinite_monotone_J` (MonotoneOn `Ici 0`);
at J = 0, corr_∞(0) = 0 ≤ corr_∞(J₂) by `correlationInfinite_nonneg`. -/
theorem correlationInfinite_monotoneOn_J_zero_closed
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (β : ℝ) (hβ : 0 < β) (b : ℝ) :
    MonotoneOn
      (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Icc 0 b) := by
  intro J₁ hJ₁ J₂ hJ₂ hJ_le
  simp only
  rcases eq_or_lt_of_le hJ₁.1 with hJ₁0 | hJ₁_pos
  · rw [← hJ₁0, correlationInfinite_eq_zero_at_J_zero]
    rcases eq_or_lt_of_le (hJ₁0.le.trans hJ_le) with hJ₂0 | hJ₂_pos
    · rw [← hJ₂0, correlationInfinite_eq_zero_at_J_zero]
    · exact correlationInfinite_nonneg _ _ _ ⟨hJ₂_pos.le, le_refl 0, hβ⟩ _
  · have hJ₁_in : J₁ ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr hJ₁_pos.le
    have hJ₂_in : J₂ ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr (hJ₁_pos.le.trans hJ_le)
    have hmono := correlationInfinite_monotone_J (IsingModel.latticeGraph d) Λ
      (le_refl 0) hβ {r_val, s_val} hJ₁_in hJ₂_in hJ_le
    exact hmono

/-- **A.e. differentiability of corr_∞ in J on closed [0, b]** (Step 233):
For `0 < β`, `b ∈ ℝ`: `J ↦ corr_∞(J)` is differentiable within `[0, b]` at Lebesgue-a.e. J.

Direct J-direction analogue of Step 179. Proof: corr_∞ is monotone on `[0, b]`
(helper above), hence locally bounded variation, hence a.e. differentiable. -/
theorem correlationInfinite_ae_differentiableWithinAt_J_zero_closed
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (β : ℝ) (hβ : 0 < β) (b : ℝ) :
    ∀ᵐ J ∂MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Icc 0 b),
    DifferentiableWithinAt ℝ
      (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Icc 0 b) J := by
  have hmono := correlationInfinite_monotoneOn_J_zero_closed Λ r_val s_val β hβ b
  exact hmono.locallyBoundedVariationOn.ae_differentiableWithinAt measurableSet_Icc

end Ambient

end IsingModel

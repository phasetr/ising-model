import Mathlib.Analysis.BoundedVariation
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempLipschitz.Lipschitz

/-!
# ℤ^d open-interval correlationInfinite BV / a.e.-differentiability wrappers

Narrow child module for four ℤ^d wrappers extracted from
`LatticeMassHighTempLipschitz.lean`:

* `correlationInfinite_locallyBoundedVariationOn_beta_of_high_temp` (Step 172),
* `correlationInfinite_ae_differentiableWithinAt_beta_of_high_temp_open`,
* `correlationInfinite_locallyBoundedVariationOn_J_of_high_temp` (Step 226),
* `correlationInfinite_ae_differentiableWithinAt_J_of_high_temp_open`.

Each combines the open-interval Lipschitz package with
`LipschitzOnWith.locallyBoundedVariationOn` and
`LocallyBoundedVariationOn.ae_differentiableWithinAt`.
-/

namespace IsingModel
namespace Ambient

/-- **Locally bounded variation of corr_∞ on the open high-temperature interval** (Step 172):
For `0 < J`, `1 ≤ d`, the function `β ↦ corr_∞(β)` has locally bounded variation on
the open interval `Ioo 0 (1/(J·2d))` (the high-temperature region).

Proof: For any `a, b ∈ Ioo 0 (1/(J·2d))` with `a ≤ b`, Step 168 gives
`LipschitzOnWith` on `Icc a b`, which implies `LocallyBoundedVariationOn` on `Icc a b`.
Restricted to `Ioo 0 (1/(J·2d)) ∩ Icc a b ⊆ Icc a b` it remains bounded variation. -/
theorem correlationInfinite_locallyBoundedVariationOn_beta_of_high_temp
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ_pos : 0 < J) :
    LocallyBoundedVariationOn
      (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))) := by
  have h2d_pos : (0 : ℝ) < ↑(2 * d) := by
    have : 0 < 2 * d := Nat.mul_pos (by norm_num) hd
    exact_mod_cast this
  have hJ2d_pos : 0 < J * ↑(2 * d) := mul_pos hJ_pos h2d_pos
  intro a b ha hb
  by_cases hab : a ≤ b
  · -- a ≤ b: apply Step 168 on Icc a b
    have ha_pos : 0 < a := ha.1
    have hb_lt : b < 1 / (J * ↑(2 * d)) := hb.2
    have hlt : b * J * ↑(2 * d) < 1 := by
      have h1 : b * (J * ↑(2 * d)) < 1 := by
        have := (lt_div_iff₀ hJ2d_pos).mp hb_lt
        linarith [this]
      linarith [h1]
    have hlip := correlationInfinite_lipschitzOnWith_beta_of_high_temp
      Λ r_val s_val hrs J hJ_pos.le a b ha_pos hab hlt
    have hbv_local := hlip.locallyBoundedVariationOn
    have hbv := hbv_local a b
      (Set.mem_Icc.mpr ⟨le_refl a, hab⟩)
      (Set.mem_Icc.mpr ⟨hab, le_refl b⟩)
    -- hbv : BoundedVariationOn corr_∞ (Icc a b ∩ Icc a b)
    rw [Set.inter_self] at hbv
    -- Need: BoundedVariationOn corr_∞ (Ioo 0 β_c ∩ Icc a b)
    exact hbv.mono Set.inter_subset_right
  · -- a > b: Icc a b is empty, hence intersection is empty
    have hba : b < a := lt_of_not_ge hab
    have hempty : Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) ∩ Set.Icc a b = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x ⟨_, hx_in⟩
      exact absurd (hx_in.1.trans hx_in.2) (not_le.mpr hba)
    -- BoundedVariationOn on empty set: variation is 0, hence ≠ ⊤
    have : BoundedVariationOn
        (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val})
        (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) ∩ Set.Icc a b) := by
      rw [hempty]
      have hev : eVariationOn (fun β =>
          correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) (∅ : Set ℝ) = 0 :=
        eVariationOn.subsingleton _ Set.subsingleton_empty
      simp [BoundedVariationOn]
    exact this

/-- **A.e. differentiability of corr_∞ on the open high-temperature interval** (Step 172):
For `0 < J`, `1 ≤ d`, the function `β ↦ corr_∞(β)` is differentiable within
`Ioo 0 (1/(J·2d))` at Lebesgue-a.e. β.

Proof: Step 172 (`correlationInfinite_locallyBoundedVariationOn_beta_of_high_temp`) +
`LocallyBoundedVariationOn.ae_differentiableWithinAt`. -/
theorem correlationInfinite_ae_differentiableWithinAt_beta_of_high_temp_open
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ_pos : 0 < J) :
    ∀ᵐ β ∂MeasureTheory.Measure.restrict MeasureTheory.volume
      (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))),
    DifferentiableWithinAt ℝ
      (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))) β := by
  have hbv := correlationInfinite_locallyBoundedVariationOn_beta_of_high_temp
    hd Λ r_val s_val hrs J hJ_pos
  exact LocallyBoundedVariationOn.ae_differentiableWithinAt hbv measurableSet_Ioo

/-- **Locally bounded variation of corr_∞ on Ioo 0 J_c in J** (Step 226):
For `0 < β`, `1 ≤ d`, `J ↦ corr_∞(J)` has locally bounded variation on the open
high-temperature interval `Ioo 0 (1/(β·2d))`.

Direct J-direction analogue of Step 172. Proof: for any `[a, b] ⊂ Ioo 0 (1/(β·2d))`,
Step 222 gives Lipschitz, which implies LocallyBoundedVariationOn. -/
theorem correlationInfinite_locallyBoundedVariationOn_J_of_high_temp
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ_pos : 0 < β) :
    LocallyBoundedVariationOn
      (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Ioo (0 : ℝ) (1 / (β * ↑(2 * d)))) := by
  have h2d_pos : (0 : ℝ) < ↑(2 * d) := by
    have : 0 < 2 * d := Nat.mul_pos (by norm_num) hd
    exact_mod_cast this
  have hβ2d_pos : 0 < β * ↑(2 * d) := mul_pos hβ_pos h2d_pos
  intro a b ha hb
  by_cases hab : a ≤ b
  · have ha_pos : 0 < a := ha.1
    have hb_lt : b < 1 / (β * ↑(2 * d)) := hb.2
    have hlt : b * β * ↑(2 * d) < 1 := by
      have h1 : b * (β * ↑(2 * d)) < 1 := by
        have := (lt_div_iff₀ hβ2d_pos).mp hb_lt
        linarith [this]
      linarith [h1]
    have hlip := correlationInfinite_lipschitzOnWith_J_of_high_temp
      Λ r_val s_val hrs β hβ_pos a b ha_pos hab hlt
    have hbv_local := hlip.locallyBoundedVariationOn
    have hbv := hbv_local a b
      (Set.mem_Icc.mpr ⟨le_refl a, hab⟩)
      (Set.mem_Icc.mpr ⟨hab, le_refl b⟩)
    rw [Set.inter_self] at hbv
    exact hbv.mono Set.inter_subset_right
  · have hba : b < a := lt_of_not_ge hab
    have hempty : Set.Ioo (0 : ℝ) (1 / (β * ↑(2 * d))) ∩ Set.Icc a b = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x ⟨_, hx_in⟩
      exact absurd (hx_in.1.trans hx_in.2) (not_le.mpr hba)
    have : BoundedVariationOn
        (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val})
        (Set.Ioo (0 : ℝ) (1 / (β * ↑(2 * d))) ∩ Set.Icc a b) := by
      rw [hempty]
      have hev : eVariationOn (fun J =>
          correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) (∅ : Set ℝ) = 0 :=
        eVariationOn.subsingleton _ Set.subsingleton_empty
      simp [BoundedVariationOn]
    exact this

/-- **A.e. differentiability of corr_∞ on Ioo 0 J_c in J** (Step 226):
For `0 < β`, `1 ≤ d`, `J ↦ corr_∞(J)` is differentiable within `Ioo 0 (1/(β·2d))` at
Lebesgue-a.e. J.

Direct J-direction analogue of Step 172 (open). -/
theorem correlationInfinite_ae_differentiableWithinAt_J_of_high_temp_open
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ_pos : 0 < β) :
    ∀ᵐ J ∂MeasureTheory.Measure.restrict MeasureTheory.volume
      (Set.Ioo (0 : ℝ) (1 / (β * ↑(2 * d)))),
    DifferentiableWithinAt ℝ
      (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Ioo (0 : ℝ) (1 / (β * ↑(2 * d)))) J := by
  have hbv := correlationInfinite_locallyBoundedVariationOn_J_of_high_temp
    hd Λ r_val s_val hrs β hβ_pos
  exact LocallyBoundedVariationOn.ae_differentiableWithinAt hbv measurableSet_Ioo

end Ambient
end IsingModel

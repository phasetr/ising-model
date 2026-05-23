import IsingModel.Concrete.CenteredSlab.InfiniteVolumeLimit

/-!
# Centered slab split — infinite-volume monotonicity, positivity, abs-h limit

Part of the split `IsingModel.Concrete.CenteredSlab` development.
-/

namespace IsingModel

namespace Concrete

variable {d : ℕ}

/-- **β-monotonicity** of `freeEnergyInfinite_centeredSlab`. -/
theorem freeEnergyInfinite_centeredSlab_monotone_beta
    {widths : Fin d → ℕ} (hw : ∀ j : Fin d, widths j ≠ 0)
    {J h : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₂ : 0 < β₂) (hβle : β₁ ≤ β₂) :
    freeEnergyInfinite_centeredSlab hw
        (⟨J, h, β₁⟩ : IsingParams ℝ) ⟨hJ, hh, hβ₁⟩
      ≤ freeEnergyInfinite_centeredSlab hw
        (⟨J, h, β₂⟩ : IsingParams ℝ) ⟨hJ, hh, hβ₂⟩ := by
  refine le_of_tendsto_of_tendsto'
    (freeEnergy_centeredSlab_tendsto_freeEnergyInfinite hw _ ⟨hJ, hh, hβ₁⟩)
    (freeEnergy_centeredSlab_tendsto_freeEnergyInfinite hw _ ⟨hJ, hh, hβ₂⟩) ?_
  intro n
  exact IsingModel.freeEnergy_monotone_beta _ J hJ h hh hβ₁ hβ₂ hβle

/-- **h-monotonicity** of `freeEnergyInfinite_centeredSlab`. -/
theorem freeEnergyInfinite_centeredSlab_monotone_h
    {widths : Fin d → ℕ} (hw : ∀ j : Fin d, widths j ≠ 0)
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh₁ : 0 ≤ h₁) (hh₂ : 0 ≤ h₂) (hhle : h₁ ≤ h₂) :
    freeEnergyInfinite_centeredSlab hw
        (⟨J, h₁, β⟩ : IsingParams ℝ) ⟨hJ, hh₁, hβ⟩
      ≤ freeEnergyInfinite_centeredSlab hw
        (⟨J, h₂, β⟩ : IsingParams ℝ) ⟨hJ, hh₂, hβ⟩ := by
  refine le_of_tendsto_of_tendsto'
    (freeEnergy_centeredSlab_tendsto_freeEnergyInfinite hw _ ⟨hJ, hh₁, hβ⟩)
    (freeEnergy_centeredSlab_tendsto_freeEnergyInfinite hw _ ⟨hJ, hh₂, hβ⟩) ?_
  intro n
  exact IsingModel.freeEnergy_monotone_h _ J β hJ hβ hh₁ hh₂ hhle

/-- **J-monotonicity** of `freeEnergyInfinite_centeredSlab`. -/
theorem freeEnergyInfinite_centeredSlab_monotone_J
    {widths : Fin d → ℕ} (hw : ∀ j : Fin d, widths j ≠ 0)
    {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β)
    {J₁ J₂ : ℝ} (hJ₁ : 0 ≤ J₁) (hJ₂ : 0 ≤ J₂) (hJle : J₁ ≤ J₂) :
    freeEnergyInfinite_centeredSlab hw
        (⟨J₁, h, β⟩ : IsingParams ℝ) ⟨hJ₁, hh, hβ⟩
      ≤ freeEnergyInfinite_centeredSlab hw
        (⟨J₂, h, β⟩ : IsingParams ℝ) ⟨hJ₂, hh, hβ⟩ := by
  refine le_of_tendsto_of_tendsto'
    (freeEnergy_centeredSlab_tendsto_freeEnergyInfinite hw _ ⟨hJ₁, hh, hβ⟩)
    (freeEnergy_centeredSlab_tendsto_freeEnergyInfinite hw _ ⟨hJ₂, hh, hβ⟩) ?_
  intro n
  exact IsingModel.freeEnergy_monotone_J _ h β hh hβ hJ₁ hJ₂ hJle

/-- **Strict positivity** `0 < freeEnergyInfinite_centeredSlab`. -/
theorem freeEnergyInfinite_centeredSlab_pos
    {widths : Fin d → ℕ} (hw : ∀ j : Fin d, widths j ≠ 0)
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) :
    0 < freeEnergyInfinite_centeredSlab hw
          (⟨J, h, β⟩ : IsingParams ℝ) ⟨hJ, hh, hβ⟩ :=
  lt_of_lt_of_le (Real.log_pos (by norm_num))
    (freeEnergyInfinite_centeredSlab_ge_log_two hw hJ hh hβ)

/-- **Non-vanishing** `freeEnergyInfinite_centeredSlab ≠ 0`. -/
theorem freeEnergyInfinite_centeredSlab_ne_zero
    {widths : Fin d → ℕ} (hw : ∀ j : Fin d, widths j ≠ 0)
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) :
    freeEnergyInfinite_centeredSlab hw
          (⟨J, h, β⟩ : IsingParams ℝ) ⟨hJ, hh, hβ⟩ ≠ 0 :=
  ne_of_gt (freeEnergyInfinite_centeredSlab_pos hw hJ hh hβ)

/-- **Fekete convergence for any real h** on the centered slab. -/
theorem freeEnergy_centeredSlab_tendsto_of_abs_h
    {widths : Fin d → ℕ} (hw : ∀ j : Fin d, widths j ≠ 0)
    {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (h : ℝ) :
    Filter.Tendsto
      (fun n => IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph (d + 1))
          (centeredSlab widths n))
        (⟨J, h, β⟩ : IsingParams ℝ))
      Filter.atTop
      (nhds (freeEnergyInfinite_centeredSlab hw
        (⟨J, |h|, β⟩ : IsingParams ℝ) ⟨hJ, abs_nonneg h, hβ⟩)) := by
  refine (freeEnergy_centeredSlab_tendsto_freeEnergyInfinite hw
    (⟨J, |h|, β⟩ : IsingParams ℝ) ⟨hJ, abs_nonneg h, hβ⟩).congr ?_
  intro n
  exact (IsingModel.freeEnergy_eq_abs_h _ J h β).symm


end Concrete

end IsingModel

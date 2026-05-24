import IsingModel.Concrete.LinearBrick.InfiniteVolume

namespace IsingModel

namespace Concrete

/-- **β-monotonicity** of `freeEnergyInfinite_linearBox` on `Set.Ioi 0`:
for ferromagnetic `0 ≤ J, 0 ≤ h`, `0 < β₁ ≤ β₂` implies
`freeEnergyInfinite_linearBox ⟨J, h, β₁⟩ ≤ freeEnergyInfinite_linearBox ⟨J, h, β₂⟩`. -/
theorem freeEnergyInfinite_linearBox_monotone_beta
    {J h : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₂ : 0 < β₂) (hβle : β₁ ≤ β₂) :
    freeEnergyInfinite_linearBox
        (⟨J, h, β₁⟩ : IsingParams ℝ) ⟨hJ, hh, hβ₁⟩
      ≤ freeEnergyInfinite_linearBox
        (⟨J, h, β₂⟩ : IsingParams ℝ) ⟨hJ, hh, hβ₂⟩ := by
  refine le_of_tendsto_of_tendsto'
    (freeEnergy_linearBox_tendsto_freeEnergyInfinite _ ⟨hJ, hh, hβ₁⟩)
    (freeEnergy_linearBox_tendsto_freeEnergyInfinite _ ⟨hJ, hh, hβ₂⟩) ?_
  intro n
  exact IsingModel.freeEnergy_monotone_beta _ J hJ h hh hβ₁ hβ₂ hβle

/-- **h-monotonicity** of `freeEnergyInfinite_linearBox` on `Set.Ici 0`. -/
theorem freeEnergyInfinite_linearBox_monotone_h
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh₁ : 0 ≤ h₁) (hh₂ : 0 ≤ h₂) (hhle : h₁ ≤ h₂) :
    freeEnergyInfinite_linearBox
        (⟨J, h₁, β⟩ : IsingParams ℝ) ⟨hJ, hh₁, hβ⟩
      ≤ freeEnergyInfinite_linearBox
        (⟨J, h₂, β⟩ : IsingParams ℝ) ⟨hJ, hh₂, hβ⟩ := by
  refine le_of_tendsto_of_tendsto'
    (freeEnergy_linearBox_tendsto_freeEnergyInfinite _ ⟨hJ, hh₁, hβ⟩)
    (freeEnergy_linearBox_tendsto_freeEnergyInfinite _ ⟨hJ, hh₂, hβ⟩) ?_
  intro n
  exact IsingModel.freeEnergy_monotone_h _ J β hJ hβ hh₁ hh₂ hhle

/-- **J-monotonicity** of `freeEnergyInfinite_linearBox` on `Set.Ici 0`. -/
theorem freeEnergyInfinite_linearBox_monotone_J
    {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β)
    {J₁ J₂ : ℝ} (hJ₁ : 0 ≤ J₁) (hJ₂ : 0 ≤ J₂) (hJle : J₁ ≤ J₂) :
    freeEnergyInfinite_linearBox
        (⟨J₁, h, β⟩ : IsingParams ℝ) ⟨hJ₁, hh, hβ⟩
      ≤ freeEnergyInfinite_linearBox
        (⟨J₂, h, β⟩ : IsingParams ℝ) ⟨hJ₂, hh, hβ⟩ := by
  refine le_of_tendsto_of_tendsto'
    (freeEnergy_linearBox_tendsto_freeEnergyInfinite _ ⟨hJ₁, hh, hβ⟩)
    (freeEnergy_linearBox_tendsto_freeEnergyInfinite _ ⟨hJ₂, hh, hβ⟩) ?_
  intro n
  exact IsingModel.freeEnergy_monotone_J _ h β hh hβ hJ₁ hJ₂ hJle

/-- **Strict positivity** `0 < freeEnergyInfinite_linearBox` under
ferromagnetic parameters. Immediate from
`freeEnergyInfinite_linearBox_ge_log_two` and `0 < log 2`. -/
theorem freeEnergyInfinite_linearBox_pos
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) :
    0 < freeEnergyInfinite_linearBox
          (⟨J, h, β⟩ : IsingParams ℝ) ⟨hJ, hh, hβ⟩ :=
  lt_of_lt_of_le (Real.log_pos (by norm_num))
    (freeEnergyInfinite_linearBox_ge_log_two hJ hh hβ)

/-- **Non-vanishing** `freeEnergyInfinite_linearBox ≠ 0` under ferromagnetic. -/
theorem freeEnergyInfinite_linearBox_ne_zero
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) :
    freeEnergyInfinite_linearBox
          (⟨J, h, β⟩ : IsingParams ℝ) ⟨hJ, hh, hβ⟩ ≠ 0 :=
  ne_of_gt (freeEnergyInfinite_linearBox_pos hJ hh hβ)

/-- **Fekete convergence for any real h** (not just `h ≥ 0`): the 1D
linearBox free-energy sequence at `⟨J, h, β⟩` converges to
`freeEnergyInfinite_linearBox ⟨J, |h|, β⟩` (ferromagnetic at |h|).
Proof: per-stage `freeEnergy_eq_abs_h` symmetry rewrites the sequence
at any real h to the sequence at |h|, which is Fekete-convergent. -/
theorem freeEnergy_linearBox_tendsto_of_abs_h
    {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (h : ℝ) :
    Filter.Tendsto
      (fun n => IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph 1) (linearBox n))
        (⟨J, h, β⟩ : IsingParams ℝ))
      Filter.atTop
      (nhds (freeEnergyInfinite_linearBox
        (⟨J, |h|, β⟩ : IsingParams ℝ) ⟨hJ, abs_nonneg h, hβ⟩)) := by
  refine (freeEnergy_linearBox_tendsto_freeEnergyInfinite
    (⟨J, |h|, β⟩ : IsingParams ℝ) ⟨hJ, abs_nonneg h, hβ⟩).congr ?_
  intro n
  -- `freeEnergy G ⟨J, |h|, β⟩ = freeEnergy G ⟨J, h, β⟩` by
  -- `IsingModel.freeEnergy_eq_abs_h` (symmetric).
  exact (IsingModel.freeEnergy_eq_abs_h _ J h β).symm


end Concrete

end IsingModel

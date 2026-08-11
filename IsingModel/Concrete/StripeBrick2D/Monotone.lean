import IsingModel.Concrete.StripeBrick2D.InfiniteVolume

/-!
# Monotonicity, positivity and field symmetry of the 2D stripe free energy

`freeEnergyInfinite_stripeBrick2D` takes a width `w : ℕ` with `w ≠ 0`, a parameter record
`p : IsingParams ℝ` and a proof of `Ferromagnetic p`, that is `0 ≤ p.J`, `0 ≤ p.h` and `0 < p.β`,
and returns the limit of the free energies of the graphs induced by the boxes `stripeBrick2D w n`
inside `latticeGraph 2`; that box is `Fintype.piFinset` of `Finset.Ico (0 : ℤ) n` in the first
coordinate and `Finset.Ico (0 : ℤ) w` in the second, so the stripe grows in one direction while
its width stays fixed. Every statement below carries the width hypothesis, spells the parameter
record out as `⟨J, h, β⟩`, and builds its ferromagnetism proof from the separate sign hypotheses
it takes.

The monotonicity statements each move one coordinate and hold the other two fixed: the value is
monotone in `β` for `0 < β₁ ≤ β₂` at nonnegative `J` and `h`, monotone in `h` for `0 ≤ h₁ ≤ h₂`
at nonnegative `J` and positive `β`, and monotone in `J` for `0 ≤ J₁ ≤ J₂` at nonnegative `h` and
positive `β`. Each follows from the corresponding monotonicity of `IsingModel.freeEnergy` at
every stage, carried to the limit by comparing two convergent stage sequences.

Positivity is inherited from the lower bound of the value by `Real.log 2`, which is itself
positive; being positive, the value is in particular nonzero, and both are stated at nonnegative
`J` and `h` and positive `β`.

The last statement removes the sign restriction on the field. For nonnegative `J`, positive `β`
and an arbitrary real `h`, the stage sequence of free energies at `⟨J, h, β⟩` converges to
`freeEnergyInfinite_stripeBrick2D hw ⟨J, |h|, β⟩`: the stagewise identity
`IsingModel.freeEnergy_eq_abs_h` makes that sequence equal to the sequence at `|h|`, whose limit
is the ferromagnetic value.
-/

namespace IsingModel

namespace Concrete

/-- **β-monotonicity** of `freeEnergyInfinite_stripeBrick2D`. -/
theorem freeEnergyInfinite_stripeBrick2D_monotone_beta
    {w : ℕ} (hw : w ≠ 0)
    {J h : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₂ : 0 < β₂) (hβle : β₁ ≤ β₂) :
    freeEnergyInfinite_stripeBrick2D hw
        (⟨J, h, β₁⟩ : IsingParams ℝ) ⟨hJ, hh, hβ₁⟩
      ≤ freeEnergyInfinite_stripeBrick2D hw
        (⟨J, h, β₂⟩ : IsingParams ℝ) ⟨hJ, hh, hβ₂⟩ := by
  refine le_of_tendsto_of_tendsto'
    (freeEnergy_stripeBrick2D_tendsto_freeEnergyInfinite hw _ ⟨hJ, hh, hβ₁⟩)
    (freeEnergy_stripeBrick2D_tendsto_freeEnergyInfinite hw _ ⟨hJ, hh, hβ₂⟩) ?_
  intro n
  exact IsingModel.freeEnergy_monotone_beta _ J hJ h hh hβ₁ hβ₂ hβle

/-- **h-monotonicity** of `freeEnergyInfinite_stripeBrick2D`. -/
theorem freeEnergyInfinite_stripeBrick2D_monotone_h
    {w : ℕ} (hw : w ≠ 0)
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh₁ : 0 ≤ h₁) (hh₂ : 0 ≤ h₂) (hhle : h₁ ≤ h₂) :
    freeEnergyInfinite_stripeBrick2D hw
        (⟨J, h₁, β⟩ : IsingParams ℝ) ⟨hJ, hh₁, hβ⟩
      ≤ freeEnergyInfinite_stripeBrick2D hw
        (⟨J, h₂, β⟩ : IsingParams ℝ) ⟨hJ, hh₂, hβ⟩ := by
  refine le_of_tendsto_of_tendsto'
    (freeEnergy_stripeBrick2D_tendsto_freeEnergyInfinite hw _ ⟨hJ, hh₁, hβ⟩)
    (freeEnergy_stripeBrick2D_tendsto_freeEnergyInfinite hw _ ⟨hJ, hh₂, hβ⟩) ?_
  intro n
  exact IsingModel.freeEnergy_monotone_h _ J β hJ hβ hh₁ hh₂ hhle

/-- **J-monotonicity** of `freeEnergyInfinite_stripeBrick2D`. -/
theorem freeEnergyInfinite_stripeBrick2D_monotone_J
    {w : ℕ} (hw : w ≠ 0)
    {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β)
    {J₁ J₂ : ℝ} (hJ₁ : 0 ≤ J₁) (hJ₂ : 0 ≤ J₂) (hJle : J₁ ≤ J₂) :
    freeEnergyInfinite_stripeBrick2D hw
        (⟨J₁, h, β⟩ : IsingParams ℝ) ⟨hJ₁, hh, hβ⟩
      ≤ freeEnergyInfinite_stripeBrick2D hw
        (⟨J₂, h, β⟩ : IsingParams ℝ) ⟨hJ₂, hh, hβ⟩ := by
  refine le_of_tendsto_of_tendsto'
    (freeEnergy_stripeBrick2D_tendsto_freeEnergyInfinite hw _ ⟨hJ₁, hh, hβ⟩)
    (freeEnergy_stripeBrick2D_tendsto_freeEnergyInfinite hw _ ⟨hJ₂, hh, hβ⟩) ?_
  intro n
  exact IsingModel.freeEnergy_monotone_J _ h β hh hβ hJ₁ hJ₂ hJle

/-- **Strict positivity** `0 < freeEnergyInfinite_stripeBrick2D`. -/
theorem freeEnergyInfinite_stripeBrick2D_pos
    {w : ℕ} (hw : w ≠ 0) {J h β : ℝ}
    (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) :
    0 < freeEnergyInfinite_stripeBrick2D hw
          (⟨J, h, β⟩ : IsingParams ℝ) ⟨hJ, hh, hβ⟩ :=
  lt_of_lt_of_le (Real.log_pos (by norm_num))
    (freeEnergyInfinite_stripeBrick2D_ge_log_two hw hJ hh hβ)

/-- **Non-vanishing** `freeEnergyInfinite_stripeBrick2D ≠ 0`. -/
theorem freeEnergyInfinite_stripeBrick2D_ne_zero
    {w : ℕ} (hw : w ≠ 0) {J h β : ℝ}
    (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) :
    freeEnergyInfinite_stripeBrick2D hw
          (⟨J, h, β⟩ : IsingParams ℝ) ⟨hJ, hh, hβ⟩ ≠ 0 :=
  ne_of_gt (freeEnergyInfinite_stripeBrick2D_pos hw hJ hh hβ)

/-- **Fekete convergence for any real h** on the 2D stripe. -/
theorem freeEnergy_stripeBrick2D_tendsto_of_abs_h
    {w : ℕ} (hw : w ≠ 0) {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (h : ℝ) :
    Filter.Tendsto
      (fun n => IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph 2) (stripeBrick2D w n))
        (⟨J, h, β⟩ : IsingParams ℝ))
      Filter.atTop
      (nhds (freeEnergyInfinite_stripeBrick2D hw
        (⟨J, |h|, β⟩ : IsingParams ℝ) ⟨hJ, abs_nonneg h, hβ⟩)) := by
  refine (freeEnergy_stripeBrick2D_tendsto_freeEnergyInfinite hw
    (⟨J, |h|, β⟩ : IsingParams ℝ) ⟨hJ, abs_nonneg h, hβ⟩).congr ?_
  intro n
  exact (IsingModel.freeEnergy_eq_abs_h _ J h β).symm


end Concrete

end IsingModel

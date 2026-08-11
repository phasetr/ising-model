import IsingModel.Concrete.LinearBrick.InfiniteVolume

/-!
# Monotonicity, positivity and field symmetry of the 1D box free energy

`freeEnergyInfinite_linearBox` takes a parameter record `p : IsingParams ℝ` together with a proof
of `Ferromagnetic p`, that is `0 ≤ p.J`, `0 ≤ p.h` and `0 < p.β`, and returns the limit of the
free energies of the graphs induced by the boxes `linearBox n` inside `latticeGraph 1`; the box
at stage `n` is `Fintype.piFinset fun _ => Finset.Ico (0 : ℤ) n` in `Fin 1 → ℤ`. Every statement
below spells the parameter record out as `⟨J, h, β⟩` and builds its ferromagnetism proof from the
separate sign hypotheses it takes, so the coordinates can be varied one at a time.

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
`freeEnergyInfinite_linearBox ⟨J, |h|, β⟩`: the stagewise identity `IsingModel.freeEnergy_eq_abs_h`
makes that sequence equal to the sequence at `|h|`, whose limit is the ferromagnetic value.
-/

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

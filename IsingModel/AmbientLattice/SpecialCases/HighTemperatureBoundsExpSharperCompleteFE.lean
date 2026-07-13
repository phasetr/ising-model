import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansion
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharper
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharperSandwich

/-!
# Ambient alongExhaustion sharper-exp freeEnergy complete-summary wrapper at h = 0

Narrow child module for the §18.3-§18.4 ambient alongExhaustion
sharper-exp freeEnergy complete-summary wrapper extracted from
`HighTemperatureBoundsExpSharperComplete.lean`:

* `freeEnergyAlongExhaustion_high_temp_h_zero_complete_summary_exp`

The wrapper bundles the sharper-exp sandwich (lower + upper) with
the two J=0 / β=0 trivial-slice values `f = log 2`, under
`0 ≤ β·J` and `(Λ.volume n).Nonempty`. The theorem name is
unchanged from the former `HighTemperatureBoundsExpSharper`
declaration.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Along-ex sharper f complete-summary exp bundle at stage `n`**:
under `0 ≤ β·J` and `0 < |Λ_n|`, single statement bundling sharper
sandwich + trivial-slice values. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_complete_summary_exp
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    Real.log 2 +
        ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
          (Λ.volume n).card * Real.log (Real.cosh (β * J))
      ≤ freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n ∧
    freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
      ≤ Real.log 2 +
          β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
            (Λ.volume n).card ∧
    freeEnergyAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n = Real.log 2 ∧
    freeEnergyAlongExhaustion G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) n = Real.log 2 := by
  have hcard : 0 < (Λ.volume n).card := hne.card_pos
  obtain ⟨h1, h2⟩ := freeEnergyAlongExhaustion_high_temp_h_zero_sandwich_exp
    G Λ J β hβJ n hcard
  refine ⟨h1, h2, ?_, ?_⟩
  · exact freeEnergyAlongExhaustion_zero_params G Λ β n hne
  · exact freeEnergyAlongExhaustion_beta_zero G Λ J 0 n hne

end Ambient

end IsingModel

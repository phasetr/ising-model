import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansion
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviation
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviationStrict

/-!
# Ambient alongExhaustion ratio-LogFe `_of_nonempty` freeEnergy wrappers

Narrow child module for the two ambient
`freeEnergyAlongExhaustion_high_temp_*_of_nonempty` wrappers
extracted from `HighTemperatureBoundsRatioLogFe.lean`:

* `freeEnergyAlongExhaustion_high_temp_h_zero_deviation_bound_exp_of_nonempty`
* `freeEnergyAlongExhaustion_high_temp_h_zero_deviation_pos_of_nonempty`

The corresponding partition-function `_pow_two_lt_of_nonempty`
wrapper now lives in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioLogFeNonemptyZ`
and is re-imported through this parent module. Each remaining
wrapper is a thin pass-through of the corresponding `*_card_pos`
or related lemma. The theorem names are unchanged from the former
`HighTemperatureBoundsRatioLogFe` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]


/-- **Along-ex f deviation bound under `(Λ.volume n).Nonempty`**:
under `0 ≤ β·J` and `(Λ.volume n).Nonempty`,
`f_n - log 2 ≤ β·J·|E_n|/|Λ_n|`. Bridges from the Nonempty hypothesis. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_deviation_bound_exp_of_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n - Real.log 2
      ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
          (Λ.volume n).card :=
  freeEnergyAlongExhaustion_high_temp_h_zero_deviation_bound_exp
    G Λ J β hβJ n hne.card_pos

/-- **Along-ex f strict deviation under nonempty volume**. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_deviation_pos_of_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 < β * J) (n : ℕ) (hne : (Λ.volume n).Nonempty)
    (hEpos : 0 < (inducedGraph G (Λ.volume n)).edgeFinset.card) :
    0 < freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n - Real.log 2 :=
  freeEnergyAlongExhaustion_high_temp_h_zero_deviation_pos
    G Λ J β hβJ n hne.card_pos hEpos

/-! ## Moved: 1 Z `pow_two_lt_of_nonempty` wrapper

The
`partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_pow_two_lt_of_nonempty`
wrapper now lives in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioLogFeNonemptyZ`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

end Ambient
end IsingModel

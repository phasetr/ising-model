import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansion
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviation
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviationStrict

/-!
# Ambient alongExhaustion Z `pow_two_lt_of_nonempty` wrapper

Narrow child module for the §18.3-§18.4 ambient alongExhaustion
`partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_pow_two_lt_of_nonempty`
wrapper extracted from
`HighTemperatureBoundsRatioLogFeNonempty.lean`.

The result is a thin pass-through of the corresponding
`*_pow_two_lt` lemma. The theorem name is unchanged from the
former `HighTemperatureBoundsRatioLogFe` declaration.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex Z strict deviation under nonempty volume**. -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_pow_two_lt_of_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 < β * J) (n : ℕ)
    (hEpos : 0 < (inducedGraph G (Λ.volume n)).edgeFinset.card) :
    (2 : ℝ) ^ (Λ.volume n).card
      < partitionFunctionAlongExhaustion G Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_pow_two_lt
    G Λ J β hβJ n hEpos

end Ambient
end IsingModel

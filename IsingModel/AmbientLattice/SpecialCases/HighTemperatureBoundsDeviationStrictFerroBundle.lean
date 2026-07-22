import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviationStrict

/-!
# Ambient alongExhaustion strict-deviation bundle wrapper at h = 0

Narrow child module for the §18.3-§18.4 ambient alongExhaustion
`Z + log Z + f` strict-deviation bundle wrapper extracted from
`HighTemperatureBoundsDeviationStrictFerro.lean`:

* `partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_strict_deviation_bundle`

The bundle assembles three strict-positivity facts from
`partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_pow_two_lt`,
`log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_deviation_pos`,
and `freeEnergyAlongExhaustion_high_temp_h_zero_deviation_pos`. The
theorem name is unchanged from the former
`HighTemperatureBoundsDeviationStrictFerro` declaration.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Along-ex Z + log Z + f strict deviation bundle at stage `n`**. -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_strict_deviation_bundle
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 < β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card)
    (hEpos : 0 < (inducedGraph G (Λ.volume n)).edgeFinset.card) :
    (2 : ℝ) ^ (Λ.volume n).card
        < partitionFunctionAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n ∧
    0 < Real.log (partitionFunctionAlongExhaustion G Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n)
        - ((Λ.volume n).card : ℝ) * Real.log 2 ∧
    0 < freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n - Real.log 2 :=
  ⟨partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_pow_two_lt
     G Λ J β hβJ n hEpos,
   log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_deviation_pos
     G Λ J β hβJ n hEpos,
   freeEnergyAlongExhaustion_high_temp_h_zero_deviation_pos
     G Λ J β hβJ n hne hEpos⟩

end Ambient

end IsingModel

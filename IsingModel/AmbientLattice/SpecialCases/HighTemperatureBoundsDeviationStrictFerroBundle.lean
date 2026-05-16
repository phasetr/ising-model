import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviationStrict

/-!
# Ambient alongExhaustion strict-deviation bundle wrappers at h = 0

Narrow child module for the two §18.3-§18.4 ambient alongExhaustion
`Z + log Z + f` strict-deviation bundle wrappers extracted from
`HighTemperatureBoundsDeviationStrictFerro.lean`:

* `partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_strict_deviation_bundle`
* `partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_`
  `strict_deviation_bundle_ferromagnetic`

The general bundle assembles three strict-positivity facts from
`partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_pow_two_lt`,
`log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_deviation_pos`,
and `freeEnergyAlongExhaustion_high_temp_h_zero_deviation_pos`. The
ferromagnetic specialization derives `0 < β * J` from `0 < J` and
`0 < β` and reuses the general bundle. Theorem names are unchanged
from the former `HighTemperatureBoundsDeviationStrictFerro`
declarations.
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

/-- **Along-ex ferromagnetic Z + log Z + f strict deviation bundle at stage `n`**. -/
theorem
partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_strict_deviation_bundle_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 < J) (hβ : 0 < β) (n : ℕ) (hne : 0 < (Λ.volume n).card)
    (hEpos : 0 < (inducedGraph G (Λ.volume n)).edgeFinset.card) :
    (2 : ℝ) ^ (Λ.volume n).card
        < partitionFunctionAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n ∧
    0 < Real.log (partitionFunctionAlongExhaustion G Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n)
        - ((Λ.volume n).card : ℝ) * Real.log 2 ∧
    0 < freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n - Real.log 2 :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_strict_deviation_bundle
    G Λ J β (mul_pos hβ hJ) n hne hEpos

end Ambient

end IsingModel

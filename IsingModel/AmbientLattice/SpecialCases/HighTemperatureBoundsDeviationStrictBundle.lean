import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviationStrict

/-!
# Strict zero-field deviation of `Z`, `log Z` and `f`, packaged along an exhaustion

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

Write `|E|` for the edge count of the stage subgraph and `|Λ|` for the cardinality of the
stage volume.

Under `0 < β * J`, `0 < |Λ|` and `0 < |E|`, a conjunction records at the parameter record
`⟨J, 0, β⟩` that `2 ^ |Λ| < Z`, that `0 < log Z - |Λ| * Real.log 2`, and that
`0 < f - Real.log 2`.
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

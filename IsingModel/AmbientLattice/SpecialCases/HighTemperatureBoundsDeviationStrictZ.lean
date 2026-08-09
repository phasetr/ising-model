import IsingModel.AmbientLattice.Exhaustion

/-!
# Strict zero-field deviation of `Z` and `log Z`, along an exhaustion

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

Write `|E|` for the edge count of the stage subgraph and `|Λ|` for the cardinality of the
stage volume.

Under `0 < β * J` and `0 < |E|`, the partition function at the parameter record `⟨J, 0, β⟩`
is strictly greater than `2 ^ |Λ|`, and its logarithm is strictly greater than
`|Λ| * Real.log 2`.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Along-ex Z strict deviation at stage `n`**. -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_pow_two_lt
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 < β * J) (n : ℕ)
    (hEpos : 0 < (inducedGraph G (Λ.volume n)).edgeFinset.card) :
    (2 : ℝ) ^ (Λ.volume n).card
      < partitionFunctionAlongExhaustion G Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n := by
  change _ < partitionFunctionΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
  exact partitionFunctionΛ_high_temp_expansion_h_zero_pow_two_lt
    G (Λ.volume n) J β hβJ hEpos

/-- **Along-ex log Z strict deviation at stage `n`**. -/
theorem log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_deviation_pos
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 < β * J) (n : ℕ)
    (hEpos : 0 < (inducedGraph G (Λ.volume n)).edgeFinset.card) :
    0 < Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n)
        - ((Λ.volume n).card : ℝ) * Real.log 2 := by
  change 0 < Real.log (partitionFunctionΛ G (Λ.volume n)
      (⟨J, 0, β⟩ : IsingParams ℝ)) - _
  exact log_partitionFunctionΛ_high_temp_expansion_h_zero_deviation_pos
    G (Λ.volume n) J β hβJ hEpos

end Ambient
end IsingModel

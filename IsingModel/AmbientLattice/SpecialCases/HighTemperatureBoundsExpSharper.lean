import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansion
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansionLowerUpper

/-!
# Exponential upper bounds on the zero-field `Z` and `log Z`, along an exhaustion

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

Write `|E|` for the edge count of the stage subgraph and `|Λ|` for the cardinality of the
stage volume.

Under `0 ≤ β * J`, the partition function at the parameter record `⟨J, 0, β⟩` is at most
`2 ^ |Λ| * Real.exp (β * J * |E|)`, and its logarithm is at most
`|Λ| * Real.log 2 + β * J * |E|`.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Along-ex sharper Z upper bound at stage `n`**: under `0 ≤ β·J`,
`Z_n(⟨J, 0, β⟩) ≤ 2^|Λ_n| · exp(β·J·|E_n|)`. Stage-`n` Λ-level
specialization of
`partitionFunction_high_temp_expansion_h_zero_upper_bound_exp`. -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_upper_bound_exp
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
      ≤ (2 : ℝ) ^ (Λ.volume n).card *
          Real.exp (β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card) := by
  change partitionFunctionΛ G (Λ.volume n)
      (⟨J, 0, β⟩ : IsingParams ℝ) ≤ _
  exact partitionFunctionΛ_high_temp_expansion_h_zero_upper_bound_exp
    G (Λ.volume n) J β hβJ

/-- **Along-ex sharper log Z upper bound at stage `n`**: under
`0 ≤ β·J`, `log Z_n ≤ |Λ_n|·log 2 + β·J·|E_n|`. Stage-`n` Λ-level
specialization of
`log_partitionFunction_high_temp_expansion_h_zero_upper_bound_exp`. -/
theorem log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_upper_bound_exp
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n)
      ≤ ((Λ.volume n).card : ℝ) * Real.log 2
        + β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card := by
  change Real.log (partitionFunctionΛ G (Λ.volume n)
      (⟨J, 0, β⟩ : IsingParams ℝ)) ≤ _
  exact log_partitionFunctionΛ_high_temp_expansion_h_zero_upper_bound_exp
    G (Λ.volume n) J β hβJ

end Ambient

end IsingModel

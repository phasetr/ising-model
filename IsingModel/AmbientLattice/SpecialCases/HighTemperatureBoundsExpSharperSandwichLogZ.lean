import IsingModel.AmbientLattice.Exhaustion

/-!
# Two-sided zero-field bounds on `log Z` in exponential form

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

Write `|E|` for the edge count of the stage subgraph and `|Λ|` for the cardinality of the
stage volume.

Under `0 ≤ β * J`, the logarithm of the partition function at the parameter record
`⟨J, 0, β⟩` lies between `|Λ| * Real.log 2 + |E| * Real.log (Real.cosh (β * J))` and
`|Λ| * Real.log 2 + β * J * |E|`.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Along-ex sharper log Z sandwich at stage `n`**: under `0 ≤ β·J`,
`|Λ_n|·log 2 + |E_n|·log cosh(β·J) ≤ log Z_n ≤ |Λ_n|·log 2 + β·J·|E_n|`. -/
theorem log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_sandwich_exp
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    ((Λ.volume n).card : ℝ) * Real.log 2
        + ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) *
            Real.log (Real.cosh (β * J))
      ≤ Real.log (partitionFunctionAlongExhaustion G Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n) ∧
    Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n)
      ≤ ((Λ.volume n).card : ℝ) * Real.log 2
        + β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card := by
  change ((Λ.volume n).card : ℝ) * _ + _ * _ ≤
      Real.log (partitionFunctionΛ G (Λ.volume n)
        (⟨J, 0, β⟩ : IsingParams ℝ)) ∧ _
  exact log_partitionFunctionΛ_high_temp_expansion_h_zero_sandwich_exp
    G (Λ.volume n) J β hβJ

end Ambient

end IsingModel

import IsingModel.AmbientLattice.Defs
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.PartitionFunctionClosedFormsPartitionJZero

/-!
# Closed form of the log partition function at `J = 0`

Stage-`n` statement for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. It takes `DecidableEq V` and
the stagewise `Fintype` instance on that subgraph's edge set, and carries no Prop-valued
hypothesis.

At `J = 0` with `h` and `β` arbitrary, the logarithm of the stage partition function equals
`(Λ.volume n).card * Real.log (2 * Real.cosh (β * h))`. The proof rewrites with the
corresponding partition-function closed form and then with `Real.log_pow`.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-- **Log form**: `log (partitionFunctionAlongExhaustion G Λ ⟨0, h, β⟩ n)
= |Λ.volume n| · log (2·cosh(β·h))`. Follows from
`partitionFunctionAlongExhaustion_J_zero` via `Real.log_pow`
(`2·cosh(β·h) > 0`). -/
theorem log_partitionFunctionAlongExhaustion_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨0, h, β⟩ : IsingParams ℝ) n)
      = ((Λ.volume n).card : ℝ) * Real.log (2 * Real.cosh (β * h)) := by
  rw [partitionFunctionAlongExhaustion_J_zero, Real.log_pow]

end Ambient
end IsingModel

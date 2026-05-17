import IsingModel.AmbientLattice.Defs
import IsingModel.AmbientLattice.Exhaustion

/-!
# Partition-function J=0 closed form along an exhaustion

Narrow child module for the along-exhaustion
`partitionFunctionAlongExhaustion_J_zero` closed-form wrapper
extracted from `PartitionFunctionClosedFormsPartition.lean`. The
wrapper is a thin pass-through to
`IsingModel.partitionFunction_J_zero`. The theorem name is
unchanged from the former `PartitionFunctionClosedForms`
declaration.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-! ## J = 0 closed form for `partitionFunctionAlongExhaustion` -/

/-- **Along-exhaustion J=0 partition function closed form**:
`partitionFunctionAlongExhaustion G Λ ⟨0, h, β⟩ n = (2·cosh(β·h))^|Λ.volume n|`
for any `h, β` and any ambient graph `G, Λ`.

Specialization of `IsingModel.partitionFunction_J_zero`
(`Z_G ⟨0, h, β⟩ = (2·cosh(β·h))^|ι|`, graph-independent) with
`Fintype.card_coe` (`|↑Λ| = |Λ|`). -/
theorem partitionFunctionAlongExhaustion_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ (⟨0, h, β⟩ : IsingParams ℝ) n
      = (2 * Real.cosh (β * h)) ^ (Λ.volume n).card := by
  change partitionFunction (inducedGraph G (Λ.volume n))
      (⟨0, h, β⟩ : IsingParams ℝ) = _
  rw [IsingModel.partitionFunction_J_zero, Fintype.card_coe]

end Ambient
end IsingModel

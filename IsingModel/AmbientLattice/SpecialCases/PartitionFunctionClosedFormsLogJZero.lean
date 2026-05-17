import IsingModel.AmbientLattice.Defs
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.PartitionFunctionClosedFormsPartitionJZero

/-!
# log-form J=0 partition-function closed form along an exhaustion

Narrow child module for the along-exhaustion
`log_partitionFunctionAlongExhaustion_J_zero` closed-form wrapper
extracted from `PartitionFunctionClosedForms.lean`. The wrapper
follows from `partitionFunctionAlongExhaustion_J_zero` via
`Real.log_pow`. The theorem name is unchanged from the former
`PartitionFunctionClosedForms` declaration.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-! ## J = 0 closed form for `log_partitionFunctionAlongExhaustion` -/

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

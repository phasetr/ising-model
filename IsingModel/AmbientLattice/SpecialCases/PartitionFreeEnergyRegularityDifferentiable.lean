import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyRegularityDifferentiableH

/-!
# Ambient `partitionFunctionAlongExhaustion` `Differentiable` β/J general-h wrappers

Narrow child module for the two ambient
`partitionFunctionAlongExhaustion_differentiable_*_general_h`
β/J general-h regularity wrappers extracted from
`PartitionFreeEnergyRegularity.lean`:

* `partitionFunctionAlongExhaustion_differentiable_beta_general_h`
* `partitionFunctionAlongExhaustion_differentiable_J_general_h`

The corresponding `h`-direction wrapper now lives in
`IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyRegularityDifferentiableH`
and is re-imported through this parent module. Each wrapper is a
thin pass-through of the corresponding Λ-level
`partitionFunctionΛ_differentiable_*` lemma. Theorem names are
unchanged from the former `PartitionFreeEnergyRegularity`
declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: partitionFunction Differentiable in `β` at general
`h`**. -/
theorem partitionFunctionAlongExhaustion_differentiable_beta_general_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (n : ℕ) :
    Differentiable ℝ (fun β' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J, h, β'⟩ n) :=
  partitionFunctionΛ_differentiable_beta_general_h G (Λ.volume n) J h

/-- **Along-ex: partitionFunction Differentiable in `J` at general
`h`**. -/
theorem partitionFunctionAlongExhaustion_differentiable_J_general_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β h : ℝ) (n : ℕ) :
    Differentiable ℝ (fun J' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J', h, β⟩ n) :=
  partitionFunctionΛ_differentiable_J_general_h G (Λ.volume n) β h

/-! ## Moved: 1 Differentiable in `h` wrapper

The `partitionFunctionAlongExhaustion_differentiable_h` h-direction
wrapper now lives in
`IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyRegularityDifferentiableH`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

end Ambient
end IsingModel

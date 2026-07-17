import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaPerDirection

/-!
# Ambient `partitionFunctionAlongExhaustion` `Differentiable` in `h` wrapper

Narrow child module for the along-exhaustion
`partitionFunctionAlongExhaustion_differentiable_h` h-direction
regularity wrapper extracted from
`PartitionFreeEnergyRegularityDifferentiable.lean`. The wrapper is
a thin pass-through to `partitionFunctionΛ_differentiable_h`. The
theorem name is unchanged from the former
`PartitionFreeEnergyRegularity` declaration.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: partitionFunction Differentiable in `h`**. -/
theorem partitionFunctionAlongExhaustion_differentiable_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    Differentiable ℝ (fun h' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J, h', β⟩ n) :=
  partitionFunctionΛ_differentiable_h G (Λ.volume n) J β

end Ambient
end IsingModel

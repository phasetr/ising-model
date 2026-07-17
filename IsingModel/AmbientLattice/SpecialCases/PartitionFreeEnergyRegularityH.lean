import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaPerDirection

/-!
# Ambient partition-function `Continuous` in `h` wrapper

Narrow child module for the along-exhaustion
`partitionFunctionAlongExhaustion_continuous_h` h-direction
regularity wrapper extracted from
`PartitionFreeEnergyRegularity.lean`. The wrapper is a thin
pass-through to `partitionFunctionΛ_continuous_h`. The theorem
name is unchanged from the former `PartitionFreeEnergyRegularity`
declaration.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: partitionFunction Continuous in `h`**. -/
theorem partitionFunctionAlongExhaustion_continuous_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    Continuous (fun h' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J, h', β⟩ n) :=
  partitionFunctionΛ_continuous_h G (Λ.volume n) J β

end Ambient
end IsingModel

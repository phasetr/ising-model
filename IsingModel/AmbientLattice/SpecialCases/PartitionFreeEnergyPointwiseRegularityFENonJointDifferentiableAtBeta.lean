import IsingModel.AmbientLattice.Exhaustion

/-!
# Ambient `freeEnergyAlongExhaustion` DifferentiableAt β wrapper

Narrow child module for the along-exhaustion
`freeEnergyAlongExhaustion_differentiableAt_beta` β-direction
pointwise wrapper extracted from
`PartitionFreeEnergyPointwiseRegularityFENonJointDifferentiableAt.lean`.
The wrapper is a thin pass-through to
`freeEnergyΛ_differentiable_beta` via the `.differentiableAt`
projection. The theorem name is unchanged from the former
`PartitionFreeEnergyPointwiseRegularity` /
`PartitionFreeEnergyPointwiseRegularityFE` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **freeEnergyAlongExhaustion DifferentiableAt β** (general h). -/
theorem freeEnergyAlongExhaustion_differentiableAt_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    DifferentiableAt ℝ (fun β' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J, h, β'⟩ n) β :=
  (freeEnergyΛ_differentiable_beta G (Λ.volume n) J h).differentiableAt

end Ambient
end IsingModel

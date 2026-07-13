import IsingModel.AmbientLattice.Exhaustion

/-!
# Ambient `freeEnergyAlongExhaustion` ContinuousAt β wrapper

Narrow child module for the along-exhaustion
`freeEnergyAlongExhaustion_continuousAt_beta` β-direction pointwise
wrapper extracted from
`PartitionFreeEnergyPointwiseRegularityFENonJoint.lean`. The wrapper
is a thin pass-through to `freeEnergyΛ_continuous_beta` via the
`.continuousAt` projection. The theorem name is unchanged from the
former `PartitionFreeEnergyPointwiseRegularity` /
`PartitionFreeEnergyPointwiseRegularityFE` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **freeEnergyAlongExhaustion ContinuousAt β** (general h). -/
theorem freeEnergyAlongExhaustion_continuousAt_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    ContinuousAt (fun β' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J, h, β'⟩ n) β :=
  (freeEnergyΛ_continuous_beta G (Λ.volume n) J h).continuousAt

end Ambient
end IsingModel

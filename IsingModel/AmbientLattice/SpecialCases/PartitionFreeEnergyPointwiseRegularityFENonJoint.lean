import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyPointwiseRegularityFENonJointDifferentiableAt

/-!
# Ambient `freeEnergyAlongExhaustion` non-joint pointwise `ContinuousAt` wrappers

Narrow child module for the three ambient
`freeEnergyAlongExhaustion_continuousAt_{beta,field,J}` non-joint
pointwise wrappers extracted from
`PartitionFreeEnergyPointwiseRegularityFE.lean`. Each wrapper is a
thin pass-through to the corresponding `freeEnergyΛ_continuous_*`
ambient lemma via the `.continuousAt` projection. Theorem names
are unchanged from the former
`PartitionFreeEnergyPointwiseRegularity` /
`PartitionFreeEnergyPointwiseRegularityFE` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### Along-exhaustion free-energy pointwise wrappers -/

/-- **freeEnergyAlongExhaustion ContinuousAt β** (general h). -/
theorem freeEnergyAlongExhaustion_continuousAt_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    ContinuousAt (fun β' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J, h, β'⟩ n) β :=
  (freeEnergyΛ_continuous_beta G (Λ.volume n) J h).continuousAt

/-! ## Moved: 3 freeEnergyAlongExhaustion_differentiableAt_* wrappers

The three `DifferentiableAt ℝ` non-joint pointwise wrappers
(`freeEnergyAlongExhaustion_differentiableAt_beta`,
`freeEnergyAlongExhaustion_differentiableAt_field`,
`freeEnergyAlongExhaustion_differentiableAt_J`) now live in
`IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyPointwiseRegularityFENonJointDifferentiableAt`.
The legacy import path is preserved by re-exporting the new child
from this parent module and from `Legacy.lean`.
-/

/-- **freeEnergyAlongExhaustion ContinuousAt h**. -/
theorem freeEnergyAlongExhaustion_continuousAt_field
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    ContinuousAt (fun h' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J, h', β⟩ n) h :=
  (freeEnergyΛ_continuous_field G (Λ.volume n) J β).continuousAt

/-- **freeEnergyAlongExhaustion ContinuousAt J**. -/
theorem freeEnergyAlongExhaustion_continuousAt_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    ContinuousAt (fun J' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J', h, β⟩ n) J :=
  (freeEnergyΛ_continuous_J G (Λ.volume n) h β).continuousAt

end Ambient
end IsingModel

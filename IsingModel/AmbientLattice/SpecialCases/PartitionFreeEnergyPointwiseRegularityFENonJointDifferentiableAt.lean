import IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyPointwiseRegularityFENonJointDifferentiableAtBeta

/-!
# Ambient `freeEnergyAlongExhaustion` non-joint pointwise `DifferentiableAt` h/J wrappers

Narrow child module for the two ambient
`freeEnergyAlongExhaustion_differentiableAt_{field,J}` non-joint
pointwise wrappers extracted from
`PartitionFreeEnergyPointwiseRegularityFENonJoint.lean`:

* `freeEnergyAlongExhaustion_differentiableAt_field`
* `freeEnergyAlongExhaustion_differentiableAt_J`

The corresponding `_differentiableAt_beta` wrapper now lives in a
sibling `_FENonJointDifferentiableAtBeta` child module (re-imported
through this parent). Each wrapper is a
thin pass-through to the corresponding `freeEnergyΛ_differentiable_*`
ambient lemma via the `.differentiableAt` projection. Theorem
names are unchanged from the former
`PartitionFreeEnergyPointwiseRegularity` /
`PartitionFreeEnergyPointwiseRegularityFE` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ## Moved: 1 DifferentiableAt β wrapper

The `freeEnergyAlongExhaustion_differentiableAt_beta` β-direction
wrapper now lives in the sibling
`_FENonJointDifferentiableAtBeta` child module. The earlier
import path is preserved by re-exporting the new child from this
parent module and from the umbrella `SpecialCases.lean`.
-/

/-- **freeEnergyAlongExhaustion DifferentiableAt h**. -/
theorem freeEnergyAlongExhaustion_differentiableAt_field
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    DifferentiableAt ℝ (fun h' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J, h', β⟩ n) h :=
  (freeEnergyΛ_differentiable_field G (Λ.volume n) J β).differentiableAt

/-- **freeEnergyAlongExhaustion DifferentiableAt J**. -/
theorem freeEnergyAlongExhaustion_differentiableAt_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    DifferentiableAt ℝ (fun J' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J', h, β⟩ n) J :=
  (freeEnergyΛ_differentiable_J G (Λ.volume n) h β).differentiableAt

end Ambient
end IsingModel

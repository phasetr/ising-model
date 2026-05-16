import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion

/-!
# Ambient `freeEnergyAlongExhaustion` non-joint pointwise `DifferentiableAt` wrappers

Narrow child module for the three ambient
`freeEnergyAlongExhaustion_differentiableAt_{beta,field,J}` non-joint
pointwise wrappers extracted from
`PartitionFreeEnergyPointwiseRegularityFENonJoint.lean`:

* `freeEnergyAlongExhaustion_differentiableAt_beta`
* `freeEnergyAlongExhaustion_differentiableAt_field`
* `freeEnergyAlongExhaustion_differentiableAt_J`

Each wrapper is a thin pass-through to the corresponding
`freeEnergyΛ_differentiable_*` ambient lemma via the
`.differentiableAt` projection. Theorem names are unchanged from
the former
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

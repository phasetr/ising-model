import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaPerDirection

/-!
# Ambient `partitionFunctionAlongExhaustion` general-h pointwise `DifferentiableAt`

Narrow child module for the two ambient
`partitionFunctionAlongExhaustion_differentiableAt_*_general_h`
pointwise wrappers extracted from
`PartitionFreeEnergyPointwiseRegularityPartitionGeneralH.lean`:

* `partitionFunctionAlongExhaustion_differentiableAt_beta_general_h`
* `partitionFunctionAlongExhaustion_differentiableAt_J_general_h`

Each wrapper is a thin pass-through to the corresponding Λ-level
`partitionFunctionΛ_differentiable_*_general_h` lemma via the
`.differentiableAt` projection. Theorem names are unchanged from
the former `PartitionFreeEnergyPointwiseRegularity` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **partitionFunctionAlongExhaustion DifferentiableAt β at general h**. -/
theorem partitionFunctionAlongExhaustion_differentiableAt_beta_general_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    DifferentiableAt ℝ (fun β' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J, h, β'⟩ n) β :=
  (partitionFunctionΛ_differentiable_beta_general_h G (Λ.volume n) J h).differentiableAt

/-- **partitionFunctionAlongExhaustion DifferentiableAt J at general h**. -/
theorem partitionFunctionAlongExhaustion_differentiableAt_J_general_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    DifferentiableAt ℝ (fun J' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J', h, β⟩ n) J :=
  (partitionFunctionΛ_differentiable_J_general_h G (Λ.volume n) β h).differentiableAt

end Ambient
end IsingModel

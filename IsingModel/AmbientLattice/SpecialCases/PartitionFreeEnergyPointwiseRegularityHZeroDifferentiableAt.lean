import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaSection186

/-!
# Ambient `partitionFunctionAlongExhaustion` h = 0 pointwise `DifferentiableAt` wrappers

Narrow child module for the two ambient
`partitionFunctionAlongExhaustion_differentiableAt_*_h_zero`
pointwise wrappers extracted from
`PartitionFreeEnergyPointwiseRegularityHZero.lean`:

* `partitionFunctionAlongExhaustion_differentiableAt_beta_h_zero`
* `partitionFunctionAlongExhaustion_differentiableAt_J_h_zero`

Each wrapper is a thin pass-through to the corresponding Λ-level
`partitionFunctionΛ_differentiable_*_h_zero` lemma via the
`.differentiableAt` projection. Theorem names are unchanged from
the former `PartitionFreeEnergyPointwiseRegularity` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **partitionFunctionAlongExhaustion DifferentiableAt β at h = 0**. -/
theorem partitionFunctionAlongExhaustion_differentiableAt_beta_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    DifferentiableAt ℝ (fun β' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J, 0, β'⟩ n) β :=
  (partitionFunctionΛ_differentiable_beta_h_zero G (Λ.volume n) J).differentiableAt

/-- **partitionFunctionAlongExhaustion DifferentiableAt J at h = 0**. -/
theorem partitionFunctionAlongExhaustion_differentiableAt_J_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    DifferentiableAt ℝ (fun J' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J', 0, β⟩ n) J :=
  (partitionFunctionΛ_differentiable_J_h_zero G (Λ.volume n) β).differentiableAt

end Ambient
end IsingModel

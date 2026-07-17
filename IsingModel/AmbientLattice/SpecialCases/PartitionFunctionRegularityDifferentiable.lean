import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaSection186

/-!
# Ambient partition-function `Differentiable` at h = 0 wrappers

Narrow child module for the two ambient
`partitionFunctionAlongExhaustion_differentiable_*_h_zero`
regularity wrappers extracted from
`PartitionFunctionRegularity.lean`:

* `partitionFunctionAlongExhaustion_differentiable_beta_h_zero`
* `partitionFunctionAlongExhaustion_differentiable_J_h_zero`

Each result is a thin pass-through of the corresponding Λ-level
`partitionFunctionΛ_differentiable_*_h_zero` lemma. Theorem names
are unchanged from the former `PartitionFunctionRegularity`
declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: partitionFunction Differentiable in `β` at `h = 0`**. -/
theorem partitionFunctionAlongExhaustion_differentiable_beta_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) (n : ℕ) :
    Differentiable ℝ (fun β : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J, 0, β⟩ n) :=
  partitionFunctionΛ_differentiable_beta_h_zero G (Λ.volume n) J

/-- **Along-ex: partitionFunction Differentiable in `J` at `h = 0`**. -/
theorem partitionFunctionAlongExhaustion_differentiable_J_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (n : ℕ) :
    Differentiable ℝ (fun J : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J, 0, β⟩ n) :=
  partitionFunctionΛ_differentiable_J_h_zero G (Λ.volume n) β

end Ambient
end IsingModel

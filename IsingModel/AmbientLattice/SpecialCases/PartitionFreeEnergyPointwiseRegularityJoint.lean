import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaSection186

/-!
# Ambient `partitionFunctionAlongExhaustion` joint pointwise wrappers

Narrow child module for the two ambient
`partitionFunctionAlongExhaustion_*_joint` pointwise wrappers
extracted from `PartitionFreeEnergyPointwiseRegularity.lean`:

* `partitionFunctionAlongExhaustion_continuousAt_joint`
* `partitionFunctionAlongExhaustion_differentiableAt_joint`

Each wrapper is a thin pass-through to the corresponding Λ-level
`partitionFunctionΛ_{continuous,differentiable}_joint` lemma via
the `.continuousAt` / `.differentiableAt` projection. Theorem
names are unchanged from the former
`PartitionFreeEnergyPointwiseRegularity` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **partitionFunctionAlongExhaustion jointly ContinuousAt**. -/
theorem partitionFunctionAlongExhaustion_continuousAt_joint
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (n : ℕ) (p : ℝ × ℝ × ℝ) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨q.2.1, q.2.2, q.1⟩ n) p :=
  (partitionFunctionΛ_continuous_joint G (Λ.volume n)).continuousAt

/-- **partitionFunctionAlongExhaustion jointly DifferentiableAt**. -/
theorem partitionFunctionAlongExhaustion_differentiableAt_joint
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (n : ℕ) (p : ℝ × ℝ × ℝ) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ × ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨q.2.1, q.2.2, q.1⟩ n) p :=
  (partitionFunctionΛ_differentiable_joint G (Λ.volume n)).differentiableAt

end Ambient
end IsingModel

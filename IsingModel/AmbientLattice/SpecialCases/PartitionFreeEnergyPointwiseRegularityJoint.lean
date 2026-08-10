import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaSection186

/-!
# Joint regularity of the stage partition function at a point of `(β, J, h)`-space

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set, and carries
no Prop-valued hypothesis.

Reading the parameter triple as the point `(β, J, h) : ℝ × ℝ × ℝ`, the stage partition
function is continuous at every such point and differentiable over `ℝ` at every such point.
Each statement is the `.continuousAt` or `.differentiableAt` projection of the corresponding
regularity on all of `ℝ × ℝ × ℝ`.
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

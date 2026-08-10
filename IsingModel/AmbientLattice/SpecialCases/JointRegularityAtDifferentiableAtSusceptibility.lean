import IsingModel.AmbientLattice.SpecialCases.JointRegularityDifferentiableSusceptibility

/-!
# Joint differentiability of the stage susceptibility at a point of `(β, J, h)`-space

Stage-`n` statement for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. It takes `DecidableEq V` and
the stagewise `Fintype` instance on that subgraph's edge set, and carries no Prop-valued
hypothesis.

Reading the parameter triple as the point `(β, J, h) : ℝ × ℝ × ℝ`, the stage susceptibility at
a site `i : V` is differentiable over `ℝ` at every such point. The statement is the
`.differentiableAt` projection of the corresponding differentiability on all of `ℝ × ℝ × ℝ`.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: susceptibility jointly DifferentiableAt** (general G). -/
theorem susceptibilityAlongExhaustion_differentiableAt_joint_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (i : V) (n : ℕ) (p : ℝ × ℝ × ℝ) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ × ℝ =>
      susceptibilityAlongExhaustion G Λ ⟨q.2.1, q.2.2, q.1⟩ i n) p :=
  (susceptibilityAlongExhaustion_differentiable_joint_gen G Λ i n).differentiableAt

end Ambient
end IsingModel

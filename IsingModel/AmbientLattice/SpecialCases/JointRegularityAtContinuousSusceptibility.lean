import IsingModel.AmbientLattice.SpecialCases.JointRegularityContinuousSusceptibility

/-!
# Joint continuity of the stage susceptibility at a point of `(β, J, h)`-space

Stage-`n` statement for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. It takes `DecidableEq V` and
the stagewise `Fintype` instance on that subgraph's edge set, and carries no Prop-valued
hypothesis.

Reading the parameter triple as the point `(β, J, h) : ℝ × ℝ × ℝ`, the stage susceptibility at
a site `i : V` is continuous at every such point. The statement is the `.continuousAt`
projection of the corresponding continuity on all of `ℝ × ℝ × ℝ`.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: susceptibility jointly ContinuousAt** (general G). -/
theorem susceptibilityAlongExhaustion_continuousAt_joint_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (i : V) (n : ℕ) (p : ℝ × ℝ × ℝ) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ =>
      susceptibilityAlongExhaustion G Λ ⟨q.2.1, q.2.2, q.1⟩ i n) p :=
  (susceptibilityAlongExhaustion_continuous_joint_gen G Λ i n).continuousAt

end Ambient
end IsingModel

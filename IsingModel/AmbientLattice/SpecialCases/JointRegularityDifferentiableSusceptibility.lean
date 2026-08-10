import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.MagnetizationAlongExhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaMagSuscep

/-!
# Joint differentiability of the stage susceptibility in `(β, J, h)`

Stage-`n` statement for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. It takes `DecidableEq V` and
the stagewise `Fintype` instance on that subgraph's edge set, and carries no Prop-valued
hypothesis.

Reading the parameter triple as the point `(β, J, h) : ℝ × ℝ × ℝ`, the stage susceptibility at
a site `i : V` is differentiable over `ℝ`. The site is arbitrary: the proof splits on
`i ∈ Λ.volume n`, applying the finite-volume joint differentiability on one branch and reading
the stage susceptibility as a constant on the other.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: susceptibility jointly Differentiable ℝ in `(β, J, h)`** (general G). -/
theorem susceptibilityAlongExhaustion_differentiable_joint_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (i : V) (n : ℕ) :
    Differentiable ℝ (fun p : ℝ × ℝ × ℝ =>
      susceptibilityAlongExhaustion G Λ ⟨p.2.1, p.2.2, p.1⟩ i n) := by
  unfold susceptibilityAlongExhaustion
  by_cases hi : i ∈ Λ.volume n
  · simp only [hi, dif_pos]
    exact susceptibilityΛ_differentiable_joint G (Λ.volume n) ⟨i, hi⟩
  · simp only [hi, dif_neg, not_false_iff]
    exact differentiable_const _

end Ambient
end IsingModel

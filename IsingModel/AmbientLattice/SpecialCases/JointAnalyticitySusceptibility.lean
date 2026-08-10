import IsingModel.AmbientLattice.MagnetizationAlongExhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaMagSuscep

/-!
# Joint real-analyticity of the stage susceptibility in `(β, J, h)`

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set, and carries
no Prop-valued hypothesis.

Reading the parameter triple as the point `(β, J, h) : ℝ × ℝ × ℝ`, the stage susceptibility at
a site `i : V` is real-analytic at every such point, and the same fact is packaged as
`AnalyticOnNhd ℝ · Set.univ`. The site is arbitrary: the pointwise proof splits on
`i ∈ Λ.volume n`, applying the finite-volume joint analyticity on one branch and reading the
stage susceptibility as a constant on the other.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: susceptibility jointly AnalyticAt** (general G). -/
theorem susceptibilityAlongExhaustion_analyticAt_joint_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (i : V) (n : ℕ) (β J h : ℝ) :
    AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ =>
      susceptibilityAlongExhaustion G Λ ⟨p.2.1, p.2.2, p.1⟩ i n) (β, J, h) := by
  unfold susceptibilityAlongExhaustion
  by_cases hi : i ∈ Λ.volume n
  · simp only [hi, dif_pos]
    exact susceptibilityΛ_analyticAt_joint G (Λ.volume n) ⟨i, hi⟩ β J h
  · simp only [hi, dif_neg, not_false_iff]
    exact analyticAt_const

/-- **Along-ex: susceptibility jointly AnalyticOnNhd over Set.univ** (general G). -/
theorem susceptibilityAlongExhaustion_analyticOnNhd_joint_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (i : V) (n : ℕ) :
    AnalyticOnNhd ℝ (fun p : ℝ × ℝ × ℝ =>
      susceptibilityAlongExhaustion G Λ ⟨p.2.1, p.2.2, p.1⟩ i n) Set.univ :=
  fun ⟨β, J, h⟩ _ => susceptibilityAlongExhaustion_analyticAt_joint_gen G Λ i n β J h

end Ambient
end IsingModel

import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.MagnetizationAlongExhaustion
import IsingModel.AmbientLattice.SpecialCases.JointAnalyticityMagnetization
import IsingModel.AmbientLattice.SpecialCases.JointAnalyticityPartitionFreeEnergy
import IsingModel.AmbientLattice.SpecialCases.JointAnalyticitySusceptibility

/-!
# Joint real-analyticity of the stage correlation in `(β, J, h)`

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set, and carries
no Prop-valued hypothesis.

Reading the parameter triple as the point `(β, J, h) : ℝ × ℝ × ℝ`, the stage correlation of a
finite observable set `A : Finset V` is real-analytic at every such point, and the same fact
is packaged as `AnalyticOnNhd ℝ · Set.univ`. The observable set is arbitrary: the pointwise
proof splits on `A ⊆ Λ.volume n`, applying the finite-volume joint analyticity on one branch
and reading the stage correlation as a constant on the other.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: correlation jointly AnalyticAt in `(β, J, h)`** (general G). -/
theorem correlationAlongExhaustion_analyticAt_joint_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (A : Finset V) (n : ℕ) (β J h : ℝ) :
    AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ =>
      correlationAlongExhaustion G Λ ⟨p.2.1, p.2.2, p.1⟩ A n) (β, J, h) := by
  unfold correlationAlongExhaustion
  by_cases hA : A ⊆ Λ.volume n
  · simp only [hA, dif_pos]
    exact correlationΛ_analyticAt_joint G (Λ.volume n) (liftFinset A hA) β J h
  · simp only [hA, dif_neg, not_false_iff]
    exact analyticAt_const

/-- **Along-ex: correlation jointly AnalyticOnNhd over Set.univ** (general G). -/
theorem correlationAlongExhaustion_analyticOnNhd_joint_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (A : Finset V) (n : ℕ) :
    AnalyticOnNhd ℝ (fun p : ℝ × ℝ × ℝ =>
      correlationAlongExhaustion G Λ ⟨p.2.1, p.2.2, p.1⟩ A n) Set.univ :=
  fun ⟨β, J, h⟩ _ => correlationAlongExhaustion_analyticAt_joint_gen G Λ A n β J h

end Ambient
end IsingModel

import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.MagnetizationAlongExhaustion
import IsingModel.AmbientLattice.SpecialCases.JointRegularityDifferentiable
import IsingModel.AmbientLattice.SpecialCases.JointRegularityContinuousSusceptibility

/-!
# Joint continuity of the stage correlation and magnetization in `(β, J, h)`

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set, and carries
no Prop-valued hypothesis.

Reading the parameter triple as the point `(β, J, h) : ℝ × ℝ × ℝ`, the stage correlation of a
finite observable set `A : Finset V` is continuous, and so is the stage magnetization at a
site `i : V`. The observable set and the site are arbitrary: each proof splits on the
containment of the support in the stage volume — `A ⊆ Λ.volume n` and `{i} ⊆ Λ.volume n`
respectively — applying the finite-volume joint continuity on one branch and reading the
observable as a constant on the other.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: correlation jointly Continuous in `(β, J, h)`** (general G). -/
theorem correlationAlongExhaustion_continuous_joint_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (A : Finset V) (n : ℕ) :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      correlationAlongExhaustion G Λ ⟨p.2.1, p.2.2, p.1⟩ A n) := by
  unfold correlationAlongExhaustion
  by_cases hA : A ⊆ Λ.volume n
  · simp only [hA, dif_pos]
    exact correlationΛ_continuous_joint G (Λ.volume n) (liftFinset A hA)
  · simp only [hA, dif_neg, not_false_iff]
    exact continuous_const

/-- **Along-ex: magnetization jointly Continuous in `(β, J, h)`** (general G). -/
theorem magnetizationAlongExhaustion_continuous_joint
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (i : V) (n : ℕ) :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      magnetizationAlongExhaustion G Λ ⟨p.2.1, p.2.2, p.1⟩ i n) := by
  unfold magnetizationAlongExhaustion correlationAlongExhaustion
  by_cases hi : ({i} : Finset V) ⊆ Λ.volume n
  · simp only [hi, dif_pos]
    exact correlationΛ_continuous_joint G (Λ.volume n) (liftFinset {i} hi)
  · simp only [hi, dif_neg, not_false_iff]
    exact continuous_const

end Ambient
end IsingModel

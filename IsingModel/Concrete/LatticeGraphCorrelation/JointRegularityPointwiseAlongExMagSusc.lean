import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.JointRegularity

/-!
# ℤ^d AlongExhaustion joint pointwise mag + susc wrappers

Narrow child module for four ℤ^d AlongExhaustion joint pointwise
wrappers extracted from `JointRegularityPointwiseAlongEx.lean`:

* `magnetizationAlongExhaustion_latticeGraph_continuousAt_joint`,
* `magnetizationAlongExhaustion_latticeGraph_differentiableAt_joint`,
* `susceptibilityAlongExhaustion_latticeGraph_continuousAt_joint`,
* `susceptibilityAlongExhaustion_latticeGraph_differentiableAt_joint`.

Each result is a thin pass-through of the ambient
`Ambient.{magnetization,susceptibility}AlongExhaustion_*_joint*`
lemma at `G := IsingModel.latticeGraph d`. The theorem names are
unchanged from the former `JointRegularityPointwiseAlongEx`
declarations.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: magnetizationAlongExhaustion jointly ContinuousAt**. -/
theorem magnetizationAlongExhaustion_latticeGraph_continuousAt_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (i : Fin d → ℤ) (n : ℕ) (p : ℝ × ℝ × ℝ) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ =>
      Ambient.magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨q.2.1, q.2.2, q.1⟩ i n) p :=
  Ambient.magnetizationAlongExhaustion_continuousAt_joint
    (IsingModel.latticeGraph d) Λ i n p

/-- **ℤ^d along-ex: magnetizationAlongExhaustion jointly DifferentiableAt**. -/
theorem magnetizationAlongExhaustion_latticeGraph_differentiableAt_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (i : Fin d → ℤ) (n : ℕ) (p : ℝ × ℝ × ℝ) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ × ℝ =>
      Ambient.magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨q.2.1, q.2.2, q.1⟩ i n) p :=
  Ambient.magnetizationAlongExhaustion_differentiableAt_joint
    (IsingModel.latticeGraph d) Λ i n p

/-- **ℤ^d along-ex: susceptibilityAlongExhaustion jointly ContinuousAt**. -/
theorem susceptibilityAlongExhaustion_latticeGraph_continuousAt_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (i : Fin d → ℤ) (n : ℕ) (p : ℝ × ℝ × ℝ) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ =>
      Ambient.susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨q.2.1, q.2.2, q.1⟩ i n) p :=
  Ambient.susceptibilityAlongExhaustion_continuousAt_joint_gen
    (IsingModel.latticeGraph d) Λ i n p

/-- **ℤ^d along-ex: susceptibilityAlongExhaustion jointly DifferentiableAt**. -/
theorem susceptibilityAlongExhaustion_latticeGraph_differentiableAt_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (i : Fin d → ℤ) (n : ℕ) (p : ℝ × ℝ × ℝ) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ × ℝ =>
      Ambient.susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨q.2.1, q.2.2, q.1⟩ i n) p :=
  Ambient.susceptibilityAlongExhaustion_differentiableAt_joint_gen
    (IsingModel.latticeGraph d) Λ i n p

end Ambient
end IsingModel

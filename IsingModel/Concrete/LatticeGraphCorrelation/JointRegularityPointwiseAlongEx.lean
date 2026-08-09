import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.JointRegularity
import IsingModel.AmbientLattice.SpecialCases.JointRegularityAt

/-!
# ℤ^d pointwise joint regularity of the along-exhaustion correlation

Concrete `latticeGraph d` statements that, for a fixed finite subset of `Fin d → ℤ` and at a
fixed stage of an arbitrary `Ambient.Exhaustion`, the correlation of that subset, read as a
function of the triple `(β, J, h)`, is continuous at an arbitrary prescribed triple and
differentiable over `ℝ` there. Each requires a `Fintype` instance on the edge set induced at
every stage, and that instance is its entire requirement: no `Prop`-typed hypothesis is
carried here.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: correlationAlongExhaustion jointly ContinuousAt**. -/
theorem correlationAlongExhaustion_latticeGraph_continuousAt_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (A : Finset (Fin d → ℤ)) (n : ℕ) (p : ℝ × ℝ × ℝ) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ =>
      Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨q.2.1, q.2.2, q.1⟩ A n) p :=
  Ambient.correlationAlongExhaustion_continuousAt_joint_gen
    (IsingModel.latticeGraph d) Λ A n p

/-- **ℤ^d along-ex: correlationAlongExhaustion jointly DifferentiableAt**. -/
theorem correlationAlongExhaustion_latticeGraph_differentiableAt_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (A : Finset (Fin d → ℤ)) (n : ℕ) (p : ℝ × ℝ × ℝ) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ × ℝ =>
      Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨q.2.1, q.2.2, q.1⟩ A n) p :=
  Ambient.correlationAlongExhaustion_differentiableAt_joint_gen
    (IsingModel.latticeGraph d) Λ A n p

end Ambient
end IsingModel

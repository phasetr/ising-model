import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.JointRegularity
import IsingModel.AmbientLattice.SpecialCases.JointRegularityAt

/-!
# ℤ^d AlongExhaustion joint pointwise regularity wrappers

Narrow child module for two ℤ^d AlongExhaustion joint pointwise wrappers
(`correlationAlongExhaustion_latticeGraph_*_joint`
with `continuousAt` and `differentiableAt`) extracted from
`JointRegularityPointwise.lean`. Each wrapper is a thin pass-through to the
corresponding ambient joint pointwise lemma at `IsingModel.latticeGraph d`.
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

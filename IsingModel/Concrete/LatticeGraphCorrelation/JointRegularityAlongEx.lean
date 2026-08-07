import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.JointRegularity

/-!
# Concrete along-exhaustion joint regularity wrappers

Instantiates the joint (all-parameter) continuity and differentiability of the
along-exhaustion correlation at `IsingModel.latticeGraph d`, the ℤ^d entry point for the
GJ §17.5–§17.6 derivative arguments.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: correlationAlongExhaustion jointly Continuous in `(β, J, h)`**. -/
theorem correlationAlongExhaustion_latticeGraph_continuous_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (A : Finset (Fin d → ℤ)) (n : ℕ) :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨p.2.1, p.2.2, p.1⟩ A n) :=
  Ambient.correlationAlongExhaustion_continuous_joint_gen
    (IsingModel.latticeGraph d) Λ A n

/-- **ℤ^d along-ex: correlationAlongExhaustion jointly Differentiable ℝ in `(β, J, h)`**. -/
theorem correlationAlongExhaustion_latticeGraph_differentiable_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (A : Finset (Fin d → ℤ)) (n : ℕ) :
    Differentiable ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨p.2.1, p.2.2, p.1⟩ A n) :=
  Ambient.correlationAlongExhaustion_differentiable_joint_gen
    (IsingModel.latticeGraph d) Λ A n

end Ambient
end IsingModel

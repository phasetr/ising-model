import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.JointRegularity

/-!
# ℤ^d joint regularity of the along-exhaustion magnetization and susceptibility

Concrete `latticeGraph d` statements that, at a fixed site of `Fin d → ℤ` and a fixed stage
of an arbitrary `Ambient.Exhaustion`, the magnetization and the susceptibility of that stage,
read as functions of the triple `(β, J, h)`, are continuous and differentiable over `ℝ` on
the whole parameter space. Every statement requires a `Fintype` instance on the edge set
induced at every stage, and that instance is its entire requirement: no `Prop`-typed
hypothesis is carried anywhere in this module.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: magnetizationAlongExhaustion jointly Continuous in `(β, J, h)`**. -/
theorem magnetizationAlongExhaustion_latticeGraph_continuous_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (i : Fin d → ℤ) (n : ℕ) :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      Ambient.magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨p.2.1, p.2.2, p.1⟩ i n) :=
  Ambient.magnetizationAlongExhaustion_continuous_joint
    (IsingModel.latticeGraph d) Λ i n

/-- **ℤ^d along-ex: magnetizationAlongExhaustion jointly Differentiable ℝ in `(β, J, h)`**. -/
theorem magnetizationAlongExhaustion_latticeGraph_differentiable_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (i : Fin d → ℤ) (n : ℕ) :
    Differentiable ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨p.2.1, p.2.2, p.1⟩ i n) :=
  Ambient.magnetizationAlongExhaustion_differentiable_joint
    (IsingModel.latticeGraph d) Λ i n

/-- **ℤ^d along-ex: susceptibilityAlongExhaustion jointly Continuous in `(β, J, h)`**. -/
theorem susceptibilityAlongExhaustion_latticeGraph_continuous_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (i : Fin d → ℤ) (n : ℕ) :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      Ambient.susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨p.2.1, p.2.2, p.1⟩ i n) :=
  Ambient.susceptibilityAlongExhaustion_continuous_joint_gen
    (IsingModel.latticeGraph d) Λ i n

/-- **ℤ^d along-ex: susceptibilityAlongExhaustion jointly Differentiable ℝ in `(β, J, h)`**. -/
theorem susceptibilityAlongExhaustion_latticeGraph_differentiable_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (i : Fin d → ℤ) (n : ℕ) :
    Differentiable ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨p.2.1, p.2.2, p.1⟩ i n) :=
  Ambient.susceptibilityAlongExhaustion_differentiable_joint_gen
    (IsingModel.latticeGraph d) Λ i n

end Ambient
end IsingModel

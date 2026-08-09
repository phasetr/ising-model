import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaMagSuscep

/-!
# ℤ^d joint regularity of the finite-volume magnetization and susceptibility

Concrete `latticeGraph d` statements that, at a fixed vertex of a fixed finite volume, the
magnetization and the susceptibility of that volume, read as functions of the triple
`(β, J, h)`, are continuous and differentiable over `ℝ` on the whole parameter space. Every
statement is made over the subgraph induced by that volume and requires a `Fintype` instance
on its edge set; that instance is its entire requirement, since no `Prop`-typed hypothesis is
carried anywhere in this module.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d Λ: magnetizationΛ jointly Continuous in `(β, J, h)`**. -/
theorem magnetizationΛ_latticeGraph_continuous_joint
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (i : ↑Λ) :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      Ambient.magnetizationΛ (IsingModel.latticeGraph d) Λ ⟨p.2.1, p.2.2, p.1⟩ i) :=
  Ambient.magnetizationΛ_continuous_joint (IsingModel.latticeGraph d) Λ i

/-- **ℤ^d Λ: magnetizationΛ jointly Differentiable ℝ in `(β, J, h)`**. -/
theorem magnetizationΛ_latticeGraph_differentiable_joint
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (i : ↑Λ) :
    Differentiable ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.magnetizationΛ (IsingModel.latticeGraph d) Λ ⟨p.2.1, p.2.2, p.1⟩ i) :=
  Ambient.magnetizationΛ_differentiable_joint (IsingModel.latticeGraph d) Λ i

/-- **ℤ^d Λ: susceptibilityΛ jointly Continuous in `(β, J, h)`**. -/
theorem susceptibilityΛ_latticeGraph_continuous_joint
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (i : ↑Λ) :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      Ambient.susceptibilityΛ (IsingModel.latticeGraph d) Λ ⟨p.2.1, p.2.2, p.1⟩ i) :=
  Ambient.susceptibilityΛ_continuous_joint (IsingModel.latticeGraph d) Λ i

/-- **ℤ^d Λ: susceptibilityΛ jointly Differentiable ℝ in `(β, J, h)`**. -/
theorem susceptibilityΛ_latticeGraph_differentiable_joint
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (i : ↑Λ) :
    Differentiable ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.susceptibilityΛ (IsingModel.latticeGraph d) Λ ⟨p.2.1, p.2.2, p.1⟩ i) :=
  Ambient.susceptibilityΛ_differentiable_joint (IsingModel.latticeGraph d) Λ i

end Ambient
end IsingModel

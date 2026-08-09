import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaJoint

/-!
# ℤ^d joint regularity of the finite-volume correlation

Concrete `latticeGraph d` statements that the correlation of a fixed finite set of vertices
of a fixed finite volume, read as a function of the triple `(β, J, h)`, is continuous and is
differentiable over `ℝ` on the whole parameter space. Each is stated over the subgraph
induced by that volume and requires a `Fintype` instance on its edge set; that instance is
its entire requirement, since no `Prop`-typed hypothesis is carried here.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d Λ: correlationΛ jointly Continuous in `(β, J, h)`**. -/
theorem correlationΛ_latticeGraph_continuous_joint
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (A : Finset (↑Λ : Type _)) :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      Ambient.correlationΛ (IsingModel.latticeGraph d) Λ ⟨p.2.1, p.2.2, p.1⟩ A) :=
  Ambient.correlationΛ_continuous_joint (IsingModel.latticeGraph d) Λ A

/-- **ℤ^d Λ: correlationΛ jointly Differentiable ℝ in `(β, J, h)`**. -/
theorem correlationΛ_latticeGraph_differentiable_joint
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (A : Finset (↑Λ : Type _)) :
    Differentiable ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.correlationΛ (IsingModel.latticeGraph d) Λ ⟨p.2.1, p.2.2, p.1⟩ A) :=
  Ambient.correlationΛ_differentiable_joint (IsingModel.latticeGraph d) Λ A

end Ambient
end IsingModel

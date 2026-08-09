import IsingModel.AmbientLattice.AnalyticityLambdaMayer
import IsingModel.Lattice

/-!
# ℤ^d regularity of the Mayer partial sum in the activity, on a fixed volume

Instantiates at `IsingModel.latticeGraph d`, on a fixed finite volume `Λ`, the regularity of
the Mayer partial sum of the induced subgraph in its activity argument: `Continuous` and
`Differentiable ℝ` on the whole line, and `ContinuousOn` and `DifferentiableOn ℝ` on an
arbitrary set. No condition on the activity, on the truncation order or on the set is imposed.
-/

namespace IsingModel
namespace Ambient

open Finset Real

/-- **ℤ^d Λ: mayerPartialSum Continuous**. -/
theorem mayerPartialSum_Λ_latticeGraph_continuous
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (N : ℕ) :
    Continuous (fun t : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N t) :=
  Ambient.mayerPartialSum_Λ_continuous (IsingModel.latticeGraph d) Λ N

/-- **ℤ^d Λ: mayerPartialSum Differentiable ℝ**. -/
theorem mayerPartialSum_Λ_latticeGraph_differentiable
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (N : ℕ) :
    Differentiable ℝ (fun t : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N t) :=
  Ambient.mayerPartialSum_Λ_differentiable
    (IsingModel.latticeGraph d) Λ N

/-- **ℤ^d Λ: mayerPartialSum ContinuousOn**. -/
theorem mayerPartialSum_Λ_latticeGraph_continuousOn
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (N : ℕ) (s : Set ℝ) :
    ContinuousOn (fun t : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N t) s :=
  Ambient.mayerPartialSum_Λ_continuousOn
    (IsingModel.latticeGraph d) Λ N s

/-- **ℤ^d Λ: mayerPartialSum DifferentiableOn ℝ**. -/
theorem mayerPartialSum_Λ_latticeGraph_differentiableOn
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (N : ℕ) (s : Set ℝ) :
    DifferentiableOn ℝ (fun t : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N t) s :=
  Ambient.mayerPartialSum_Λ_differentiableOn
    (IsingModel.latticeGraph d) Λ N s

end Ambient
end IsingModel

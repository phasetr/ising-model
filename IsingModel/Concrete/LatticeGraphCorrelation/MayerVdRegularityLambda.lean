import IsingModel.AmbientLattice.AnalyticityLambdaMayer
import IsingModel.Lattice

/-!
# ℤ^d Λ-direct mayerPartialSum regularity wrappers

Narrow child module for four ℤ^d Λ-direct
`mayerPartialSum_Λ_latticeGraph_*` continuous/differentiable wrappers
extracted from `MayerVdRegularity.lean`:

* `mayerPartialSum_Λ_latticeGraph_continuous`,
* `mayerPartialSum_Λ_latticeGraph_differentiable`,
* `mayerPartialSum_Λ_latticeGraph_continuousOn`,
* `mayerPartialSum_Λ_latticeGraph_differentiableOn`.
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

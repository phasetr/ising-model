import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaMayerPfeEdgeBounds

/-!
# ℤ^d Λ-layer `mayerPartialSum_Λ_latticeGraph_*` edge-case wrappers

Narrow child module for three ℤ^d Λ-layer
`mayerPartialSum_Λ_latticeGraph_*` edge-case wrappers extracted from
`MayerExpansionEdgeCases.lean`:

* `mayerPartialSum_Λ_latticeGraph_two`,
* `mayerPartialSum_Λ_latticeGraph_eq_zero_of_no_polymers`,
* `mayerPartialSum_Λ_latticeGraph_eq_zero_of_edgeFinset_empty`.

Each result is a thin pass-through of the ambient
`Ambient.mayerPartialSum_Λ_*` lemma at `G := IsingModel.latticeGraph d`.
The theorem names are unchanged from the former
`MayerExpansionEdgeCases` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real

/-- **ℤ^d Λ: mayerPartialSum at `N = 2`**. -/
theorem mayerPartialSum_Λ_latticeGraph_two
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (t : ℝ) :
    IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) 2 t =
      (∑ P ∈ IsingModel.allPolymers
              (inducedGraph (IsingModel.latticeGraph d) Λ),
            t ^ P.card) +
        (-1/2 : ℝ) *
          ∑ pq ∈ ((IsingModel.allPolymers
                    (inducedGraph (IsingModel.latticeGraph d) Λ)) ×ˢ
                  (IsingModel.allPolymers
                    (inducedGraph (IsingModel.latticeGraph d) Λ))).filter
              (fun pq => IsingModel.PolymersIncompatible pq.1 pq.2),
            (t ^ pq.1.card * t ^ pq.2.card) :=
  Ambient.mayerPartialSum_Λ_two (IsingModel.latticeGraph d) Λ t

/-- **ℤ^d Λ: mayerPartialSum = 0 on no-polymer induced graphs**. -/
theorem mayerPartialSum_Λ_latticeGraph_eq_zero_of_no_polymers
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (h_no : IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d) Λ) = ∅)
    (t : ℝ) (N : ℕ) :
    IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N t = 0 :=
  Ambient.mayerPartialSum_Λ_eq_zero_of_no_polymers
    (IsingModel.latticeGraph d) Λ h_no t N

/-- **ℤ^d Λ: mayerPartialSum = 0 on edgeless induced graphs**. -/
theorem mayerPartialSum_Λ_latticeGraph_eq_zero_of_edgeFinset_empty
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (h_empty : (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset
      = ∅) (t : ℝ) (N : ℕ) :
    IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N t = 0 :=
  Ambient.mayerPartialSum_Λ_eq_zero_of_edgeFinset_empty
    (IsingModel.latticeGraph d) Λ h_empty t N

end Ambient
end IsingModel

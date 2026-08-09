import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaMayerPfeEdgeBounds

/-!
# ℤ^d Mayer partial sum at truncation order two and on polymer-free volumes

Instantiates at `IsingModel.latticeGraph d`, on a fixed finite volume `Λ`, the closed form of
the Mayer partial sum at truncation order `2` — the polymer activity sum `∑_P t ^ |P|` plus
`-1/2` times the sum over the incompatible ordered pairs of polymers — and its vanishing at
every truncation order and activity when the induced subgraph has no polymer, and when that
subgraph has no edge. The order-`2` closed form assumes nothing about the activity; the
vanishing statements assume only the stated emptiness.
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

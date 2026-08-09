import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaMayerPfeEdgeBounds

/-!
# ℤ^d order-two Mayer term and the absolute bound on a Mayer term

Instantiates at `IsingModel.latticeGraph d`, on a fixed finite volume `Λ`, the closed form of
the order-`2` Mayer expansion term of the induced subgraph as a sum over ordered pairs of
polymers weighted by `-1/2` on the incompatible pairs — given as a weighted sum over all
pairs, and as `-1/2` times the sum restricted to the incompatible pairs — together with the
absolute bound on a Mayer expansion term of arbitrary order by the sum of
`|ursellCoefficient ω| * |clusterSeqActivity t ω|` over polymer sequences. No condition on the
activity or on the order is imposed.
-/

namespace IsingModel
namespace Ambient

open Finset Real

/-- **ℤ^d Λ: mayerExpansionTerm at `n = 2`**. -/
theorem mayerExpansionTerm_Λ_latticeGraph_two
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (t : ℝ) :
    IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) Λ) 2 t =
      ∑ pq ∈ (IsingModel.allPolymers
              (inducedGraph (IsingModel.latticeGraph d) Λ)) ×ˢ
              (IsingModel.allPolymers
                (inducedGraph (IsingModel.latticeGraph d) Λ)),
        (if IsingModel.PolymersIncompatible pq.1 pq.2 then (-1/2 : ℝ)
          else 0) *
          (t ^ pq.1.card * t ^ pq.2.card) :=
  Ambient.mayerExpansionTerm_Λ_two (IsingModel.latticeGraph d) Λ t

/-- **ℤ^d Λ: mayerExpansionTerm at `n = 2`, filter form**. -/
theorem mayerExpansionTerm_Λ_latticeGraph_two_filter
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (t : ℝ) :
    IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) Λ) 2 t =
      (-1/2 : ℝ) *
        ∑ pq ∈ ((IsingModel.allPolymers
                  (inducedGraph (IsingModel.latticeGraph d) Λ)) ×ˢ
                (IsingModel.allPolymers
                  (inducedGraph (IsingModel.latticeGraph d) Λ))).filter
            (fun pq => IsingModel.PolymersIncompatible pq.1 pq.2),
          (t ^ pq.1.card * t ^ pq.2.card) :=
  Ambient.mayerExpansionTerm_Λ_two_filter
    (IsingModel.latticeGraph d) Λ t

/-- **ℤ^d Λ: mayerExpansionTerm absolute bound**. -/
theorem mayerExpansionTerm_Λ_latticeGraph_abs_le
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (n : ℕ) (t : ℝ) :
    |IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) Λ) n t| ≤
      ∑ ω ∈ Fintype.piFinset
              (fun _ : Fin n => IsingModel.allPolymers
                (inducedGraph (IsingModel.latticeGraph d) Λ)),
        |IsingModel.ursellCoefficient ω| *
          |IsingModel.clusterSeqActivity t ω| :=
  Ambient.mayerExpansionTerm_Λ_abs_le
    (IsingModel.latticeGraph d) Λ n t

end Ambient
end IsingModel

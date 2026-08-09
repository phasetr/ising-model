import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaBasicIdentities

/-!
# ℤ^d polymer activity sum and Mayer partial sum at their trivial arguments

Instantiates at `IsingModel.latticeGraph d`, on a fixed finite volume `Λ`, the values taken at
trivial arguments by the activity sum `∑_Γ ∏_{P ∈ Γ} t ^ |P|` over the vertex-disjoint
compatible polymer families of the induced subgraph and by the Mayer partial sum: the activity
sum is `1` at activity `0` and, at activity `1`, the cardinality of that family set; the Mayer
partial sum vanishes at truncation order `0` and at activity `0`, and at truncation order `1`
it is `∑_P t ^ |P|` over the polymers of the induced subgraph. No condition on the activity or
on the truncation order is imposed anywhere here.
-/

namespace IsingModel
namespace Ambient

open Finset Real

/-- **ℤ^d Λ: vdPolymerFamilies_sum at t = 0 = 1**. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_at_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet] :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ),
        ∏ P ∈ Γ, (0 : ℝ) ^ P.card) = 1 :=
  Ambient.vdPolymerFamilies_sum_Λ_at_zero (IsingModel.latticeGraph d) Λ

/-- **ℤ^d Λ: vdPolymerFamilies_sum at t = 1**. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_at_one
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet] :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ),
        ∏ P ∈ Γ, (1 : ℝ) ^ P.card) =
      (IsingModel.vdCompatiblePolymerFamilies
        (inducedGraph (IsingModel.latticeGraph d) Λ)).card :=
  Ambient.vdPolymerFamilies_sum_Λ_at_one (IsingModel.latticeGraph d) Λ

/-- **ℤ^d Λ: mayerPartialSum at N = 0 = 0**. -/
theorem mayerPartialSum_Λ_latticeGraph_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (t : ℝ) :
    IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) 0 t = 0 :=
  Ambient.mayerPartialSum_Λ_zero (IsingModel.latticeGraph d) Λ t

/-- **ℤ^d Λ: mayerPartialSum at N = 1**. -/
theorem mayerPartialSum_Λ_latticeGraph_one
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (t : ℝ) :
    IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) 1 t =
      ∑ P ∈ IsingModel.allPolymers
            (inducedGraph (IsingModel.latticeGraph d) Λ), t ^ P.card :=
  Ambient.mayerPartialSum_Λ_one (IsingModel.latticeGraph d) Λ t

/-- **ℤ^d Λ: mayerPartialSum at t = 0 = 0**. -/
theorem mayerPartialSum_Λ_latticeGraph_at_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (N : ℕ) :
    IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N 0 = 0 :=
  Ambient.mayerPartialSum_Λ_at_zero (IsingModel.latticeGraph d) Λ N

end Ambient
end IsingModel

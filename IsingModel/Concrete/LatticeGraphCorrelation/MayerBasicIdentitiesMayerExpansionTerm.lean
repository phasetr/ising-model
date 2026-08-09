import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaBasicIdentities

/-!
# ℤ^d Mayer expansion term at its trivial orders and at zero activity

Instantiates at `IsingModel.latticeGraph d`, on a fixed finite volume `Λ`, the values of a
single Mayer expansion term of the induced subgraph: it vanishes at order `0` and at activity
`0`, and at order `1` it is the activity sum `∑_P t ^ |P|` over the polymers of that subgraph.
No condition on the activity or on the order is imposed.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d Λ: mayerExpansionTerm at n = 0 = 0**. -/
theorem mayerExpansionTerm_Λ_latticeGraph_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (t : ℝ) :
    IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) Λ) 0 t = 0 :=
  Ambient.mayerExpansionTerm_Λ_zero (IsingModel.latticeGraph d) Λ t

/-- **ℤ^d Λ: mayerExpansionTerm at n = 1**. -/
theorem mayerExpansionTerm_Λ_latticeGraph_one
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (t : ℝ) :
    IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) Λ) 1 t =
      ∑ P ∈ IsingModel.allPolymers
            (inducedGraph (IsingModel.latticeGraph d) Λ), t ^ P.card :=
  Ambient.mayerExpansionTerm_Λ_one (IsingModel.latticeGraph d) Λ t

/-- **ℤ^d Λ: mayerExpansionTerm at t = 0 = 0**. -/
theorem mayerExpansionTerm_Λ_latticeGraph_at_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (n : ℕ) :
    IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) Λ) n 0 = 0 :=
  Ambient.mayerExpansionTerm_Λ_at_zero (IsingModel.latticeGraph d) Λ n

end Ambient
end IsingModel

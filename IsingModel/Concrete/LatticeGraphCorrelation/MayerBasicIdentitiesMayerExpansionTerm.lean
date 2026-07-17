import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaBasicIdentities

/-!
# ℤ^d mayerExpansionTerm_Λ_latticeGraph wrappers

Narrow child module for three ℤ^d
`mayerExpansionTerm_Λ_latticeGraph_*` wrappers extracted from
`MayerBasicIdentities.lean`:

* `mayerExpansionTerm_Λ_latticeGraph_zero`,
* `mayerExpansionTerm_Λ_latticeGraph_one`,
* `mayerExpansionTerm_Λ_latticeGraph_at_zero`.
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

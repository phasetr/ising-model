import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MayerAnalyticity

/-!
# ℤ^d analyticity of a Mayer expansion term in the activity

Instantiates at `IsingModel.latticeGraph d`, on a fixed finite volume `Λ` and at a stage `n`
of an `Ambient.Exhaustion` of `Fin d → ℤ`, the analyticity of a single Mayer expansion term
`mayerExpansionTerm` of the induced subgraph, at a fixed order, in its activity argument:
`AnalyticAt ℝ` at an arbitrary point, and `AnalyticOnNhd ℝ` on `Set.univ`. No condition on the
activity or on the order is imposed.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d Λ: mayerExpansionTerm AnalyticAt ℝ**. -/
theorem mayerExpansionTerm_Λ_latticeGraph_analyticAt
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (n : ℕ) (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ => IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) Λ) n s) t :=
  Ambient.mayerExpansionTerm_Λ_analyticAt
    (IsingModel.latticeGraph d) Λ n t

/-- **ℤ^d Λ: mayerExpansionTerm AnalyticOnNhd Set.univ**. -/
theorem mayerExpansionTerm_Λ_latticeGraph_analyticOnNhd
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (n : ℕ) :
    AnalyticOnNhd ℝ (fun s : ℝ => IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) Λ) n s) Set.univ :=
  Ambient.mayerExpansionTerm_Λ_analyticOnNhd
    (IsingModel.latticeGraph d) Λ n

/-- **ℤ^d along-ex: mayerExpansionTerm AnalyticAt ℝ**. -/
theorem mayerExpansionTermAlongExhaustion_latticeGraph_analyticAt
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (k : ℕ) (n : ℕ) (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ => IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) k s) t :=
  Ambient.mayerExpansionTermAlongExhaustion_analyticAt
    (IsingModel.latticeGraph d) Λ k n t

/-- **ℤ^d along-ex: mayerExpansionTerm AnalyticOnNhd Set.univ**. -/
theorem mayerExpansionTermAlongExhaustion_latticeGraph_analyticOnNhd
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (k : ℕ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun s : ℝ => IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) k s)
      Set.univ :=
  Ambient.mayerExpansionTermAlongExhaustion_analyticOnNhd
    (IsingModel.latticeGraph d) Λ k n

end Ambient
end IsingModel

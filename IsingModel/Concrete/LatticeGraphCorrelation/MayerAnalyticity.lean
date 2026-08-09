import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MayerAnalyticity

/-!
# ℤ^d analyticity of the Mayer partial sum in the activity

Instantiates at `IsingModel.latticeGraph d`, on a fixed finite volume `Λ` and at a stage `n`
of an `Ambient.Exhaustion` of `Fin d → ℤ`, the analyticity of the Mayer partial sum
`mayerPartialSum` of the induced subgraph in its activity argument: `AnalyticAt ℝ` at an
arbitrary point, and `AnalyticOnNhd ℝ` on `Set.univ`. No condition on the activity or on the
truncation order is imposed.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d Λ: mayerPartialSum AnalyticAt ℝ**. -/
theorem mayerPartialSum_Λ_latticeGraph_analyticAt
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (N : ℕ) (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N s) t :=
  Ambient.mayerPartialSum_Λ_analyticAt
    (IsingModel.latticeGraph d) Λ N t

/-- **ℤ^d along-ex: mayerPartialSum AnalyticAt ℝ**. -/
theorem mayerPartialSumAlongExhaustion_latticeGraph_analyticAt
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (N : ℕ) (n : ℕ) (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N s) t :=
  Ambient.mayerPartialSumAlongExhaustion_analyticAt
    (IsingModel.latticeGraph d) Λ N n t

/-- **ℤ^d Λ: mayerPartialSum `AnalyticOnNhd ℝ _ Set.univ`**. -/
theorem mayerPartialSum_Λ_latticeGraph_analyticOnNhd
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (N : ℕ) :
    AnalyticOnNhd ℝ
      (fun s : ℝ => IsingModel.mayerPartialSum
          (inducedGraph (IsingModel.latticeGraph d) Λ) N s) Set.univ :=
  Ambient.mayerPartialSum_Λ_analyticOnNhd
    (IsingModel.latticeGraph d) Λ N

/-- **ℤ^d along-ex: mayerPartialSum `AnalyticOnNhd ℝ _ Set.univ`**. -/
theorem mayerPartialSumAlongExhaustion_latticeGraph_analyticOnNhd
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (N : ℕ) (n : ℕ) :
    AnalyticOnNhd ℝ
      (fun s : ℝ => IsingModel.mayerPartialSum
          (inducedGraph (IsingModel.latticeGraph d)
            (Λ.volume n)) N s) Set.univ :=
  Ambient.mayerPartialSumAlongExhaustion_analyticOnNhd
    (IsingModel.latticeGraph d) Λ N n

end Ambient
end IsingModel

import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MayerAnalyticity

/-!
# Concrete Mayer analyticity wrappers for the lattice graph

Narrow child module for ℤ^d `mayerPartialSum` and `mayerExpansionTerm`
analytic wrappers. The theorem names are the same as the former
declarations, but callers can now import this child module directly.
-/

namespace IsingModel
namespace Ambient

/-! ### `mayerPartialSum` analyticity ℤ^d wraps -/

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

/-! ## Moved: mayerExpansionTerm analyticity wrappers

The four wrappers
`mayerExpansionTerm_Λ_latticeGraph_analyticAt`,
`mayerExpansionTerm_Λ_latticeGraph_analyticOnNhd`,
`mayerExpansionTermAlongExhaustion_latticeGraph_analyticAt`,
`mayerExpansionTermAlongExhaustion_latticeGraph_analyticOnNhd` now
live in `MayerAnalyticityExpansionTerm.lean`. -/

/-! ## Moved: Mayer tanh-composed analyticity wrappers

The eight `*_tanh_analytic*` wrappers at the tanh substitution live in
`MayerAnalyticityTanhAlongEx.lean`
(`mayerPartialSumAlongExhaustion_*`, four wrappers) and
`MayerAnalyticityTanhExpansionTerm.lean`
(`mayerExpansionTerm_Λ_*` / `mayerExpansionTermAlongExhaustion_*`,
four wrappers). -/


end Ambient
end IsingModel

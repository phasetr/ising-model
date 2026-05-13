import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MayerAnalyticity

/-!
# Concrete Mayer tanh-composed analyticity wrappers

Narrow child module for twelve ℤ^d `*_tanh_analytic*` wrappers
(`mayerPartialSum_*` / `mayerPartialSumAlongExhaustion_*` /
`mayerExpansionTerm_*` / `mayerExpansionTermAlongExhaustion_*` at the
tanh substitution). Each wrapper is a thin pass-through to the
corresponding ambient `*_tanh_*` analyticAt / analyticOnNhd lemma at
`IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient


/-! ### `mayerPartialSum` tanh β/J analyticity ℤ^d wraps -/

/-- **ℤ^d Λ: mayerPartialSum ∘ tanh ∘ (·*J) AnalyticAt in β**. -/
theorem mayerPartialSum_Λ_latticeGraph_tanh_analyticAt_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (N : ℕ) (J β : ℝ) :
    AnalyticAt ℝ (fun β' : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N
        (Real.tanh (β' * J))) β :=
  Ambient.mayerPartialSum_Λ_tanh_analyticAt_beta
    (IsingModel.latticeGraph d) Λ N J β

/-- **ℤ^d Λ: mayerPartialSum ∘ tanh ∘ (β*·) AnalyticAt in J**. -/
theorem mayerPartialSum_Λ_latticeGraph_tanh_analyticAt_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (N : ℕ) (β J : ℝ) :
    AnalyticAt ℝ (fun J' : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N
        (Real.tanh (β * J'))) J :=
  Ambient.mayerPartialSum_Λ_tanh_analyticAt_J
    (IsingModel.latticeGraph d) Λ N β J

/-- **ℤ^d Λ: mayerPartialSum ∘ tanh ∘ (·*J) AnalyticOnNhd Set.univ
in β**. -/
theorem mayerPartialSum_Λ_latticeGraph_tanh_analyticOnNhd_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (N : ℕ) (J : ℝ) :
    AnalyticOnNhd ℝ (fun β' : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N
        (Real.tanh (β' * J))) Set.univ :=
  Ambient.mayerPartialSum_Λ_tanh_analyticOnNhd_beta
    (IsingModel.latticeGraph d) Λ N J

/-- **ℤ^d Λ: mayerPartialSum ∘ tanh ∘ (β*·) AnalyticOnNhd Set.univ
in J**. -/
theorem mayerPartialSum_Λ_latticeGraph_tanh_analyticOnNhd_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (N : ℕ) (β : ℝ) :
    AnalyticOnNhd ℝ (fun J' : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N
        (Real.tanh (β * J'))) Set.univ :=
  Ambient.mayerPartialSum_Λ_tanh_analyticOnNhd_J
    (IsingModel.latticeGraph d) Λ N β

/-- **ℤ^d along-ex: mayerPartialSum ∘ tanh ∘ (·*J) AnalyticAt in β**. -/
theorem mayerPartialSumAlongExhaustion_latticeGraph_tanh_analyticAt_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (N : ℕ) (J β : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun β' : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N
        (Real.tanh (β' * J))) β :=
  Ambient.mayerPartialSumAlongExhaustion_tanh_analyticAt_beta
    (IsingModel.latticeGraph d) Λ N J β n

/-- **ℤ^d along-ex: mayerPartialSum ∘ tanh ∘ (β*·) AnalyticAt in J**. -/
theorem mayerPartialSumAlongExhaustion_latticeGraph_tanh_analyticAt_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (N : ℕ) (β J : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun J' : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N
        (Real.tanh (β * J'))) J :=
  Ambient.mayerPartialSumAlongExhaustion_tanh_analyticAt_J
    (IsingModel.latticeGraph d) Λ N β J n

/-- **ℤ^d along-ex: mayerPartialSum ∘ tanh ∘ (·*J) AnalyticOnNhd
Set.univ in β**. -/
theorem
mayerPartialSumAlongExhaustion_latticeGraph_tanh_analyticOnNhd_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (N : ℕ) (J : ℝ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun β' : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N
        (Real.tanh (β' * J))) Set.univ :=
  Ambient.mayerPartialSumAlongExhaustion_tanh_analyticOnNhd_beta
    (IsingModel.latticeGraph d) Λ N J n

/-- **ℤ^d along-ex: mayerPartialSum ∘ tanh ∘ (β*·) AnalyticOnNhd
Set.univ in J**. -/
theorem mayerPartialSumAlongExhaustion_latticeGraph_tanh_analyticOnNhd_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (N : ℕ) (β : ℝ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun J' : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N
        (Real.tanh (β * J'))) Set.univ :=
  Ambient.mayerPartialSumAlongExhaustion_tanh_analyticOnNhd_J
    (IsingModel.latticeGraph d) Λ N β n

/-! ## Moved: mayerExpansionTerm tanh β/J analyticity wrappers

The four `mayerExpansionTerm_{Λ,AlongExhaustion}_latticeGraph_tanh_analyticAt_{beta,J}`
wrappers now live in `MayerAnalyticityTanhExpansionTerm.lean`. -/



end Ambient
end IsingModel

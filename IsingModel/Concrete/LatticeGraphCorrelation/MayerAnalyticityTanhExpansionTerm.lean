import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MayerAnalyticityExpansionTermTanh

/-!
# ℤ^d mayerExpansionTerm tanh β/J analyticity wrappers

Narrow child module for four ℤ^d
`mayerExpansionTerm_{Λ,AlongExhaustion}_latticeGraph_tanh_analyticAt_{beta,J}`
wrappers extracted from `MayerAnalyticityTanh.lean`. Each wrapper is a thin
pass-through to the corresponding ambient
`mayerExpansionTerm_*_tanh_analyticAt_*` lemma at
`IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d Λ: mayerExpansionTerm ∘ tanh ∘ (·*J) AnalyticAt in β**. -/
theorem mayerExpansionTerm_Λ_latticeGraph_tanh_analyticAt_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (n : ℕ) (J β : ℝ) :
    AnalyticAt ℝ (fun β' : ℝ => IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) Λ) n
        (Real.tanh (β' * J))) β :=
  Ambient.mayerExpansionTerm_Λ_tanh_analyticAt_beta
    (IsingModel.latticeGraph d) Λ n J β

/-- **ℤ^d Λ: mayerExpansionTerm ∘ tanh ∘ (β*·) AnalyticAt in J**. -/
theorem mayerExpansionTerm_Λ_latticeGraph_tanh_analyticAt_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (n : ℕ) (β J : ℝ) :
    AnalyticAt ℝ (fun J' : ℝ => IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) Λ) n
        (Real.tanh (β * J'))) J :=
  Ambient.mayerExpansionTerm_Λ_tanh_analyticAt_J
    (IsingModel.latticeGraph d) Λ n β J

/-- **ℤ^d along-ex: mayerExpansionTerm ∘ tanh ∘ (·*J) AnalyticAt in β**. -/
theorem mayerExpansionTermAlongExhaustion_latticeGraph_tanh_analyticAt_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (k : ℕ) (J β : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun β' : ℝ => IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) k
        (Real.tanh (β' * J))) β :=
  Ambient.mayerExpansionTermAlongExhaustion_tanh_analyticAt_beta
    (IsingModel.latticeGraph d) Λ k J β n

/-- **ℤ^d along-ex: mayerExpansionTerm ∘ tanh ∘ (β*·) AnalyticAt in J**. -/
theorem mayerExpansionTermAlongExhaustion_latticeGraph_tanh_analyticAt_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (k : ℕ) (β J : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun J' : ℝ => IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) k
        (Real.tanh (β * J'))) J :=
  Ambient.mayerExpansionTermAlongExhaustion_tanh_analyticAt_J
    (IsingModel.latticeGraph d) Λ k β J n

end Ambient
end IsingModel

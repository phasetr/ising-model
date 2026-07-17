import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaMayer

/-!
# Concrete Mayer tanh-composed analyticity wrappers

Narrow child module for ℤ^d `mayerPartialSum_*_tanh_analytic*` wrappers
(`mayerPartialSum_Λ_*` / `mayerPartialSumAlongExhaustion_*` at the tanh
substitution). Each wrapper is a thin pass-through to the corresponding
ambient `*_tanh_*` analyticAt / analyticOnNhd lemma at
`IsingModel.latticeGraph d`. The `mayerExpansionTerm_*_tanh_analyticAt_*`
wrappers now live in `MayerAnalyticityTanhExpansionTerm.lean`.
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

/-! ## Moved: AlongExhaustion mayerPartialSum tanh analyticity wrappers

The four wrappers
`mayerPartialSumAlongExhaustion_latticeGraph_tanh_analyticAt_beta`,
`mayerPartialSumAlongExhaustion_latticeGraph_tanh_analyticAt_J`,
`mayerPartialSumAlongExhaustion_latticeGraph_tanh_analyticOnNhd_beta`,
`mayerPartialSumAlongExhaustion_latticeGraph_tanh_analyticOnNhd_J` now
live in `MayerAnalyticityTanhAlongEx.lean`. -/


/-! ## Moved: mayerExpansionTerm tanh β/J analyticity wrappers

The four `mayerExpansionTerm_{Λ,AlongExhaustion}_latticeGraph_tanh_analyticAt_{beta,J}`
wrappers now live in `MayerAnalyticityTanhExpansionTerm.lean`. -/



end Ambient
end IsingModel

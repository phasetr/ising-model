import IsingModel.AmbientLattice.AnalyticityLambdaMayer
import IsingModel.Lattice

/-!
# Concrete Mayer tanh-variant regularity wrappers

Narrow child module for the 16 ℤ^d Mayer tanh-variant wrappers
(`mayerPartialSum_Λ_latticeGraph_tanh_*`,
`mayerPartialSumAlongExhaustion_latticeGraph_tanh_*`,
`mayerExpansionTerm_Λ_latticeGraph_tanh_*`,
`mayerExpansionTermAlongExhaustion_latticeGraph_tanh_*` —
`continuous`/`differentiable` in β/J directions) extracted from
`MayerVdRegularity.lean` in PR #2046. Each is a thin pass-through to
the corresponding ambient `*_tanh_*` regularity lemma at
`IsingModel.latticeGraph d`. The theorem names are unchanged from the
former `MayerVdRegularity` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real

/-! ### §18.6 mayerPartialSum tanh β/J ℤ^d wraps -/

/-- **ℤ^d Λ: mayerPartialSum ∘ tanh ∘ (·*J) continuous in β**. -/
theorem mayerPartialSum_Λ_latticeGraph_tanh_continuous_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (N : ℕ) (J : ℝ) :
    Continuous (fun β' : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N
        (Real.tanh (β' * J))) :=
  Ambient.mayerPartialSum_Λ_tanh_continuous_beta
    (IsingModel.latticeGraph d) Λ N J

/-- **ℤ^d Λ: mayerPartialSum ∘ tanh ∘ (β*·) continuous in J**. -/
theorem mayerPartialSum_Λ_latticeGraph_tanh_continuous_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (N : ℕ) (β : ℝ) :
    Continuous (fun J' : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N
        (Real.tanh (β * J'))) :=
  Ambient.mayerPartialSum_Λ_tanh_continuous_J
    (IsingModel.latticeGraph d) Λ N β

/-- **ℤ^d Λ: mayerPartialSum ∘ tanh ∘ (·*J) differentiable in β**. -/
theorem mayerPartialSum_Λ_latticeGraph_tanh_differentiable_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (N : ℕ) (J : ℝ) :
    Differentiable ℝ (fun β' : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N
        (Real.tanh (β' * J))) :=
  Ambient.mayerPartialSum_Λ_tanh_differentiable_beta
    (IsingModel.latticeGraph d) Λ N J

/-- **ℤ^d Λ: mayerPartialSum ∘ tanh ∘ (β*·) differentiable in J**. -/
theorem mayerPartialSum_Λ_latticeGraph_tanh_differentiable_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (N : ℕ) (β : ℝ) :
    Differentiable ℝ (fun J' : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N
        (Real.tanh (β * J'))) :=
  Ambient.mayerPartialSum_Λ_tanh_differentiable_J
    (IsingModel.latticeGraph d) Λ N β

/-! ## Moved: AlongExhaustion Mayer tanh regularity wrappers

The four wrappers
`mayerPartialSumAlongExhaustion_latticeGraph_tanh_continuous_beta`,
`mayerPartialSumAlongExhaustion_latticeGraph_tanh_continuous_J`,
`mayerPartialSumAlongExhaustion_latticeGraph_tanh_differentiable_beta`,
`mayerPartialSumAlongExhaustion_latticeGraph_tanh_differentiable_J` now
live in `MayerVdRegularityTanhAlongEx.lean`. -/


/-! ### §18.5 mayerExpansionTerm tanh β/J ℤ^d wraps -/
/-! ## Moved: mayerExpansionTerm_Λ tanh regularity wrappers

The four wrappers
`mayerExpansionTerm_Λ_latticeGraph_tanh_*` (`continuous_beta`,
`continuous_J`, `differentiable_beta`, `differentiable_J`) now live in
`MayerVdRegularityTanhExpansionTermLambda.lean`. -/


/-! ## Moved: mayerExpansionTermAlongExhaustion tanh regularity wrappers

The four wrappers
`mayerExpansionTermAlongExhaustion_latticeGraph_tanh_*`
(`continuous_beta`, `continuous_J`, `differentiable_beta`,
`differentiable_J`) now live in
`MayerVdRegularityTanhExpansionTermAlongEx.lean`. -/


end Ambient

end IsingModel

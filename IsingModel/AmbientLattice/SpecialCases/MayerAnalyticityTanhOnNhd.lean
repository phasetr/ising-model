import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaMayer

/-!
# `mayerPartialSum` tanh `AnalyticOnNhd` wrappers along an exhaustion

Narrow child module for the two §18.6 along-exhaustion
`mayerPartialSum ∘ tanh ∘ (·)` `AnalyticOnNhd ℝ _ Set.univ`
wrappers extracted from `MayerAnalyticityTanh.lean`:

* `mayerPartialSumAlongExhaustion_tanh_analyticOnNhd_beta`
* `mayerPartialSumAlongExhaustion_tanh_analyticOnNhd_J`

Each wrapper is a thin pass-through to the corresponding
`mayerPartialSum_Λ_tanh_analyticOnNhd_*` ambient lemma. Theorem
names are unchanged from the former `MayerAnalyticity`
declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: mayerPartialSum ∘ tanh ∘ (·*J) AnalyticOnNhd in β
over `Set.univ`**. -/
theorem mayerPartialSumAlongExhaustion_tanh_analyticOnNhd_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (J : ℝ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun β' : ℝ =>
        IsingModel.mayerPartialSum
          (inducedGraph G (Λ.volume n)) N
          (Real.tanh (β' * J))) Set.univ :=
  mayerPartialSum_Λ_tanh_analyticOnNhd_beta G (Λ.volume n) N J

/-- **Along-ex: mayerPartialSum ∘ tanh ∘ (β*·) AnalyticOnNhd in J
over `Set.univ`**. -/
theorem mayerPartialSumAlongExhaustion_tanh_analyticOnNhd_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (β : ℝ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun J' : ℝ =>
        IsingModel.mayerPartialSum
          (inducedGraph G (Λ.volume n)) N
          (Real.tanh (β * J'))) Set.univ :=
  mayerPartialSum_Λ_tanh_analyticOnNhd_J G (Λ.volume n) N β

end Ambient
end IsingModel

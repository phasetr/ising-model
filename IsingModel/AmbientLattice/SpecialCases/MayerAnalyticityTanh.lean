import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion

/-!
# `mayerPartialSum` tanh analyticity wrappers along an exhaustion

Narrow child module for the four §18.6 along-exhaustion
`mayerPartialSum` tanh-composed analyticity wrappers (`AnalyticAt`
in `β` and `J`, `AnalyticOnNhd ℝ _ Set.univ` in `β` and `J`).
Each wrapper is a thin pass-through to the corresponding
`mayerPartialSum_Λ_tanh_analytic*` ambient lemma. Theorem names
are unchanged from the former `MayerAnalyticity` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### `mayerPartialSum` tanh β/J analyticity along an exhaustion -/

/-- **Along-ex: mayerPartialSum ∘ tanh ∘ (·*J) AnalyticAt in β**. -/
theorem mayerPartialSumAlongExhaustion_tanh_analyticAt_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (J β : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun β' : ℝ =>
        IsingModel.mayerPartialSum
          (inducedGraph G (Λ.volume n)) N
          (Real.tanh (β' * J))) β :=
  mayerPartialSum_Λ_tanh_analyticAt_beta G (Λ.volume n) N J β

/-- **Along-ex: mayerPartialSum ∘ tanh ∘ (β*·) AnalyticAt in J**. -/
theorem mayerPartialSumAlongExhaustion_tanh_analyticAt_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (β J : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun J' : ℝ =>
        IsingModel.mayerPartialSum
          (inducedGraph G (Λ.volume n)) N
          (Real.tanh (β * J'))) J :=
  mayerPartialSum_Λ_tanh_analyticAt_J G (Λ.volume n) N β J

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

import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.MayerAnalyticityExpansionTerm

/-!
# Mayer analyticity wrappers along an exhaustion

Narrow child module for along-exhaustion `mayerPartialSum` and
`mayerExpansionTerm` analytic wrappers. This keeps callers that only need
these analytic forwarders out of the monolithic legacy special-cases module.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### `mayerPartialSum` analyticity along an exhaustion -/

/-- **Along-ex: `mayerPartialSum` is `AnalyticAt ℝ`**. -/
theorem mayerPartialSumAlongExhaustion_analyticAt
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (n : ℕ) (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ =>
        IsingModel.mayerPartialSum
          (inducedGraph G (Λ.volume n)) N s) t :=
  mayerPartialSum_Λ_analyticAt G (Λ.volume n) N t

/-- **Along-ex: mayerPartialSum `AnalyticOnNhd ℝ _ Set.univ`**. -/
theorem mayerPartialSumAlongExhaustion_analyticOnNhd
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (n : ℕ) :
    AnalyticOnNhd ℝ
      (fun s : ℝ => IsingModel.mayerPartialSum
          (inducedGraph G (Λ.volume n)) N s) Set.univ :=
  mayerPartialSum_Λ_analyticOnNhd G (Λ.volume n) N

/-! ## Moved: mayerExpansionTermAlongExhaustion analyticity wrappers

The two `mayerExpansionTermAlongExhaustion_analytic{At,OnNhd}` wrappers
now live in `MayerAnalyticityExpansionTerm.lean`. They are re-imported
here so downstream consumers continue to see the symbols. -/


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

/-! ## Moved: mayerExpansionTermAlongExhaustion tanh analyticity wrappers

The two `mayerExpansionTermAlongExhaustion_tanh_analyticAt_{beta,J}`
wrappers now live in `MayerAnalyticityExpansionTerm.lean`. -/


end Ambient
end IsingModel

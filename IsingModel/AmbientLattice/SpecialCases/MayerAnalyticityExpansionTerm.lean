import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion

/-!
# Ambient mayerExpansionTermAlongExhaustion analyticity wrappers

Narrow child module for 4 ambient `mayerExpansionTermAlongExhaustion_*`
analyticity wrappers extracted from `MayerAnalyticity.lean`:

* `mayerExpansionTermAlongExhaustion_analyticAt`,
* `mayerExpansionTermAlongExhaustion_analyticOnNhd`,
* `mayerExpansionTermAlongExhaustion_tanh_analyticAt_beta`,
* `mayerExpansionTermAlongExhaustion_tanh_analyticAt_J`.

Each result is a thin pass-through of the corresponding Λ-level
`mayerExpansionTerm_Λ_*` analyticity lemma. The theorem names are
unchanged from the former `MayerAnalyticity` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]


/-! ### `mayerExpansionTerm` analyticity along an exhaustion -/

/-- **Along-ex: `mayerExpansionTerm` is `AnalyticAt ℝ`**. -/
theorem mayerExpansionTermAlongExhaustion_analyticAt
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (k : ℕ) (n : ℕ) (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ =>
        IsingModel.mayerExpansionTerm
          (inducedGraph G (Λ.volume n)) k s) t :=
  mayerExpansionTerm_Λ_analyticAt G (Λ.volume n) k t

/-- **Along-ex: `mayerExpansionTerm` is
`AnalyticOnNhd ℝ _ Set.univ`**. -/
theorem mayerExpansionTermAlongExhaustion_analyticOnNhd
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (k : ℕ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun s : ℝ =>
        IsingModel.mayerExpansionTerm
          (inducedGraph G (Λ.volume n)) k s) Set.univ :=
  mayerExpansionTerm_Λ_analyticOnNhd G (Λ.volume n) k

/-! ### `mayerExpansionTerm` tanh β/J analyticity along an exhaustion -/

/-- **Along-ex: mayerExpansionTerm ∘ tanh ∘ (·*J) AnalyticAt in β**. -/
theorem mayerExpansionTermAlongExhaustion_tanh_analyticAt_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (k : ℕ) (J β : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun β' : ℝ =>
        IsingModel.mayerExpansionTerm
          (inducedGraph G (Λ.volume n)) k
          (Real.tanh (β' * J))) β :=
  mayerExpansionTerm_Λ_tanh_analyticAt_beta G (Λ.volume n) k J β

/-- **Along-ex: mayerExpansionTerm ∘ tanh ∘ (β*·) AnalyticAt in J**. -/
theorem mayerExpansionTermAlongExhaustion_tanh_analyticAt_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (k : ℕ) (β J : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun J' : ℝ =>
        IsingModel.mayerExpansionTerm
          (inducedGraph G (Λ.volume n)) k
          (Real.tanh (β * J'))) J :=
  mayerExpansionTerm_Λ_tanh_analyticAt_J G (Λ.volume n) k β J


end Ambient
end IsingModel

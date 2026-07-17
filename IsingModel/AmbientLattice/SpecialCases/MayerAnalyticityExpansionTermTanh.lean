import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaMayer

/-!
# `mayerExpansionTerm` tanh `AnalyticAt` wrappers along an exhaustion

Narrow child module for the two §18.6 along-exhaustion
`mayerExpansionTerm ∘ tanh ∘ (·)` `AnalyticAt` wrappers extracted
from `MayerAnalyticityExpansionTerm.lean`:

* `mayerExpansionTermAlongExhaustion_tanh_analyticAt_beta`
* `mayerExpansionTermAlongExhaustion_tanh_analyticAt_J`

Each wrapper is a thin pass-through to the corresponding
`mayerExpansionTerm_Λ_tanh_analyticAt_*` ambient lemma. Theorem
names are unchanged from the former `MayerAnalyticity`
declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

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

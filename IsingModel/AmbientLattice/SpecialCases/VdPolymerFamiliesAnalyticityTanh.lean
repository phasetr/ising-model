import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaVdPolymer

/-!
# Polymer-family `tanh ∘ (·)` analyticity wrappers along an exhaustion

Narrow child module for the two along-exhaustion
`vdPolymerFamilies_sumAlongExhaustion_tanh_analyticAt_{beta,J}`
wrappers extracted from `VdPolymerFamiliesAnalyticity.lean`:

* `vdPolymerFamilies_sumAlongExhaustion_tanh_analyticAt_beta`
* `vdPolymerFamilies_sumAlongExhaustion_tanh_analyticAt_J`

Each wrapper is a thin pass-through to the corresponding ambient
`vdPolymerFamilies_sum_Λ_tanh_analyticAt_*` lemma. Theorem names
are unchanged from the former `VdPolymerFamiliesAnalyticity`
declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: vdPolymerFamilies_sum ∘ tanh ∘ (·*J) AnalyticAt in β**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_tanh_analyticAt_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun β' : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, Real.tanh (β' * J) ^ P.card) β :=
  vdPolymerFamilies_sum_Λ_tanh_analyticAt_beta G (Λ.volume n) J β

/-- **Along-ex: vdPolymerFamilies_sum ∘ tanh ∘ (β*·) AnalyticAt in J**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_tanh_analyticAt_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β J : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun J' : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, Real.tanh (β * J') ^ P.card) J :=
  vdPolymerFamilies_sum_Λ_tanh_analyticAt_J G (Λ.volume n) β J

end Ambient
end IsingModel

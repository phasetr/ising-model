import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaVdPolymer

/-!
# Ambient log_vdPolymerFamilies_sumAlongExhaustion `tanh` analyticity wrappers

Narrow child module for the two ambient
`log_vdPolymerFamilies_sumAlongExhaustion_tanh_analyticAt_*` wrappers
extracted from `VdPolymerFamiliesAnalyticityLog.lean`:

* `log_vdPolymerFamilies_sumAlongExhaustion_tanh_analyticAt_beta`
* `log_vdPolymerFamilies_sumAlongExhaustion_tanh_analyticAt_J`

Each result is a thin pass-through of the corresponding Λ-level
`log_vdPolymerFamilies_sum_Λ_tanh_analyticAt_*` lemma. Theorem
names are unchanged from the former `VdPolymerFamiliesAnalyticity`
declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: log_vdPolymerFamilies_sum ∘ tanh AnalyticAt in β under
`0 ≤ β·J`**. -/
theorem log_vdPolymerFamilies_sumAlongExhaustion_tanh_analyticAt_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    AnalyticAt ℝ (fun β' : ℝ =>
        Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, Real.tanh (β' * J) ^ P.card)) β :=
  log_vdPolymerFamilies_sum_Λ_tanh_analyticAt_beta
    G (Λ.volume n) J β hβJ

/-- **Along-ex: log_vdPolymerFamilies_sum ∘ tanh AnalyticAt in J under
`0 ≤ β·J`**. -/
theorem log_vdPolymerFamilies_sumAlongExhaustion_tanh_analyticAt_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β J : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    AnalyticAt ℝ (fun J' : ℝ =>
        Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, Real.tanh (β * J') ^ P.card)) J :=
  log_vdPolymerFamilies_sum_Λ_tanh_analyticAt_J
    G (Λ.volume n) β J hβJ

end Ambient
end IsingModel

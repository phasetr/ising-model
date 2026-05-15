import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.VdPolymerFamiliesAnalyticityLog

/-!
# Polymer-family analyticity wrappers along an exhaustion

Narrow child module for along-exhaustion `vdPolymerFamilies_sum`,
`log_vdPolymerFamilies_sum`, and epsilon analyticity wrappers. This keeps
callers that only need these analytic forwarders out of the monolithic legacy
special-cases module.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### `vdPolymerFamilies_sum` analyticity along an exhaustion -/

/-- **Along-ex: `vdPolymerFamilies_sum` is `AnalyticAt ℝ` in `t`**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_analyticAt
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (n : ℕ) (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, s ^ P.card) t :=
  vdPolymerFamilies_sum_Λ_analyticAt G (Λ.volume n) t

/-! ### `vdPolymerFamilies_sum` tanh β/J analyticity along an exhaustion -/

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

/-! ## Moved: log_vdPolymerFamilies_sumAlongExhaustion analyticity wrappers

The four `log_vdPolymerFamilies_sumAlongExhaustion_*` analyticity
wrappers (`analyticAt`, `analyticOnNhd_Ici_zero`,
`tanh_analyticAt_beta`, `tanh_analyticAt_J`) now live in
`VdPolymerFamiliesAnalyticityLog.lean`. They are re-imported here so
downstream consumers continue to see the symbols. -/



/-! ### Epsilon analyticity along an exhaustion -/

/-- **Along-ex: ε(t) is `AnalyticAt ℝ` at every `t`**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_minus_one_analyticAt
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (t : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun s : ℝ =>
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
        ∏ P ∈ Γ, s ^ P.card) t :=
  vdPolymerFamilies_sum_Λ_minus_one_analyticAt G (Λ.volume n) t

end Ambient
end IsingModel

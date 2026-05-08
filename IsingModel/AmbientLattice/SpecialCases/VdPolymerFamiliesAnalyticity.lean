import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion

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

/-! ### `log_vdPolymerFamilies_sum` analyticity along an exhaustion -/

/-- **Along-ex: log_vdPolymerFamilies_sum AnalyticAt for `t ≥ 0`**. -/
theorem log_vdPolymerFamilies_sumAlongExhaustion_analyticAt
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    AnalyticAt ℝ (fun s : ℝ =>
        Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, s ^ P.card)) t :=
  log_vdPolymerFamilies_sum_Λ_analyticAt G (Λ.volume n) ht

/-- **Along-ex: log_vdPolymerFamilies_sum AnalyticOnNhd over `[0, ∞)`**. -/
theorem log_vdPolymerFamilies_sumAlongExhaustion_analyticOnNhd_Ici_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    AnalyticOnNhd ℝ (fun s : ℝ =>
        Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, s ^ P.card)) (Set.Ici 0) :=
  log_vdPolymerFamilies_sum_Λ_analyticOnNhd_Ici_zero
    G (Λ.volume n)

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

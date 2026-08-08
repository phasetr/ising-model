import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.VdPolymerFamiliesAnalyticityLogTanh

/-!
# Ambient log_vdPolymerFamilies_sumAlongExhaustion analyticity wrappers

Carries analyticity of the logarithm of the van-den-Berg polymer-family sum to the
along-exhaustion layer (GJ §18.5), where it feeds the analyticity of the infinite-volume
free energy. Each result passes through the corresponding Λ-level
`log_vdPolymerFamilies_sum_Λ_*` lemma.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]


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

end Ambient
end IsingModel

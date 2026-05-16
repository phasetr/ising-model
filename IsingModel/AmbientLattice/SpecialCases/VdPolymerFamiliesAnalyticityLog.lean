import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.VdPolymerFamiliesAnalyticityLogTanh

/-!
# Ambient log_vdPolymerFamilies_sumAlongExhaustion analyticity wrappers

Narrow child module for 4 ambient
`log_vdPolymerFamilies_sumAlongExhaustion_*` analyticity wrappers
extracted from `VdPolymerFamiliesAnalyticity.lean`:

* `log_vdPolymerFamilies_sumAlongExhaustion_analyticAt`,
* `log_vdPolymerFamilies_sumAlongExhaustion_analyticOnNhd_Ici_zero`,
* `log_vdPolymerFamilies_sumAlongExhaustion_tanh_analyticAt_beta`,
* `log_vdPolymerFamilies_sumAlongExhaustion_tanh_analyticAt_J`.

Each result is a thin pass-through of the corresponding Λ-level
`log_vdPolymerFamilies_sum_Λ_*` lemma. The theorem names are unchanged
from the former `VdPolymerFamiliesAnalyticity` declarations.
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

/-! ## Moved: 2 log_vdPolymerFamilies_sum tanh wrappers

The two `log_vdPolymerFamilies_sumAlongExhaustion_tanh_analyticAt_*`
wrappers (`_tanh_analyticAt_beta`, `_tanh_analyticAt_J`) now live in
`IsingModel.AmbientLattice.SpecialCases.VdPolymerFamiliesAnalyticityLogTanh`.
The legacy import path is preserved by re-exporting the new child
from this parent module and from the umbrella.
-/

end Ambient
end IsingModel

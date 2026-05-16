import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.MayerStrictPositivityVdSumPointwiseTanh

/-!
# `vdPolymerFamilies_sum` pointwise positivity wrappers along an exhaustion

Narrow child module for four §18.5 along-exhaustion
`vdPolymerFamilies_sum` pointwise positivity wrappers under
`allPolymers` nonempty hypotheses (general `0 < t` and tanh-form
`0 < tanh(β·J)`). Each wrapper is a thin pass-through to the
corresponding `vdPolymerFamilies_sum_Λ_*_of_*_pos_of_polymers_nonempty`
ambient lemma. Theorem names are unchanged from the former
`MayerStrictPositivityVdSum` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: 1 < vdSum under `0 < t` and polymers exist**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_gt_one_of_t_pos_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (h_t_pos : 0 < t) (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph G (Λ.volume n))).Nonempty) :
    1 < (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n)),
            ∏ P ∈ Γ, t ^ P.card) :=
  vdPolymerFamilies_sum_Λ_gt_one_of_t_pos_of_polymers_nonempty
    G (Λ.volume n) h_t_pos h_poly

/-- **Along-ex: 0 < ε(t) under `0 < t` and polymers exist**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_minus_one_pos_of_t_pos_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (h_t_pos : 0 < t) (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph G (Λ.volume n))).Nonempty) :
    0 < (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, t ^ P.card) :=
  vdPolymerFamilies_sum_Λ_minus_one_pos_of_t_pos_of_polymers_nonempty
    G (Λ.volume n) h_t_pos h_poly

/-! ## Moved: 2 vd_sum tanh-positivity wrappers

The two along-ex tanh-positivity wrappers
(`vdPolymerFamilies_sumAlongExhaustion_tanh_gt_one_of_tanh_pos_of_polymers_nonempty`,
`vdPolymerFamilies_sumAlongExhaustion_minus_one_tanh_pos_of_tanh_pos_of_polymers_nonempty`)
now live in
`IsingModel.AmbientLattice.SpecialCases.MayerStrictPositivityVdSumPointwiseTanh`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella.
-/

end Ambient
end IsingModel

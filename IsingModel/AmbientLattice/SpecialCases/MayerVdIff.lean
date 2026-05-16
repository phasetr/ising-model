import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.MayerVdIffTanh

/-!
# Mayer vd iff characterization wrappers along an exhaustion

Narrow child module for along-exhaustion iff characterizations of
`vdPolymerFamilies_sum`. This keeps callers that only need the equivalence
wrappers out of the monolithic legacy special-cases module.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-! ### §18.5 vdPolymerFamilies_sum iff characterizations along-ex wraps -/

/-- **Along-ex: vdSum = 1 ↔ ε = 0**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_eq_one_iff_eps_eq_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (t : ℝ) (n : ℕ) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
        ∏ P ∈ Γ, t ^ P.card) = 1 ↔
      (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n))).erase ∅,
        ∏ P ∈ Γ, t ^ P.card) = 0 :=
  vdPolymerFamilies_sum_Λ_eq_one_iff_eps_zero G (Λ.volume n) t

/-- **Along-ex: vdSum > 1 ↔ ε > 0 under `0 ≤ t`**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_gt_one_iff_eps_pos
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    1 < (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card) ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, t ^ P.card :=
  vdPolymerFamilies_sum_Λ_gt_one_iff_eps_pos G (Λ.volume n) ht

/-! ## Moved: 2 vd tanh iff wrappers

The two `vdPolymerFamilies_sumAlongExhaustion_tanh_*_iff`
characterization wrappers (`_tanh_gt_one_iff`, `_tanh_eq_one_iff`)
now live in
`IsingModel.AmbientLattice.SpecialCases.MayerVdIffTanh`.
The legacy import path is preserved by re-exporting the new child
from this parent module and from the umbrella.
-/

end Ambient
end IsingModel

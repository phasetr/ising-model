import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.MayerVdBoundsGeneric

/-!
# Mayer vd bound wrappers along an exhaustion

Narrow child module for along-exhaustion `vdPolymerFamilies_sum` bound
wrappers. This keeps callers that only need these forwarders out of the
monolithic legacy special-cases module.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-! ### §18.5 vdPolymerFamilies_sum bound family along-ex wraps -/

/-- **Along-ex: vdSum_tanh ≤ 2^|E|**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_le_two_pow
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (2 : ℝ) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card :=
  vdPolymerFamilies_sum_Λ_le_two_pow G (Λ.volume n) hβJ

/-- **Along-ex: vdSum_tanh ≤ (1+tanh)^|E|**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_le_one_plus_tanh_pow
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (1 + Real.tanh (β * J)) ^
          (inducedGraph G (Λ.volume n)).edgeFinset.card :=
  vdPolymerFamilies_sum_Λ_le_one_plus_tanh_pow G (Λ.volume n) hβJ

/-- **Along-ex: 1 ≤ vdSum_tanh**. -/
theorem one_le_vdPolymerFamilies_sumAlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    1 ≤ ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n)),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card :=
  one_le_vdPolymerFamilies_sum_Λ G (Λ.volume n) hβJ

/-! ## Moved: vdPolymerFamilies_sum generic-t bound wrappers

The four `vdPolymerFamilies_sumAlongExhaustion_*` generic-`t`
wrappers (`_ge_one_of_nonneg`, `_le_one_plus_pow_of_nonneg`,
`_pos_of_nonneg`, `_eq_one_add`) now live in
`IsingModel.AmbientLattice.SpecialCases.MayerVdBoundsGeneric`.
The legacy import path is preserved by re-exporting the new child
from this parent module and from `Legacy.lean`.
-/

end Ambient
end IsingModel

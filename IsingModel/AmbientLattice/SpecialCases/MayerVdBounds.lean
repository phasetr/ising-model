import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion

/-!
# Mayer vd bound wrappers along an exhaustion

Narrow child module for along-exhaustion `vdPolymerFamilies_sum` bound
wrappers. This keeps callers that only need these forwarders out of the
monolithic original special-cases module. It collects both the
tanh-form bounds (`_le_two_pow`, `_le_one_plus_tanh_pow`,
`one_le_*`) and the generic-`t` bound / decomposition / sandwich
forwarders (`_pos_of_nonneg`, `_eq_one_add`, `_ge_one_of_nonneg`,
`_le_one_plus_pow_of_nonneg`). Each theorem is a thin pass-through to
the corresponding `vdPolymerFamilies_sum_Λ_*` ambient lemma.
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

/-! ### §18.5 vdPolymerFamilies_sum generic-t bounds along-ex -/

/-- **Along-ex: 0 < vdSum** under `0 ≤ t`. -/
theorem vdPolymerFamilies_sumAlongExhaustion_pos_of_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    0 < ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card :=
  vdPolymerFamilies_sum_Λ_pos_of_nonneg G (Λ.volume n) ht

/-- **Along-ex: vdSum = 1 + ε(t)** decomposition. -/
theorem vdPolymerFamilies_sumAlongExhaustion_eq_one_add
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (t : ℝ) (n : ℕ) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card) =
      1 + ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
              ∏ P ∈ Γ, t ^ P.card :=
  vdPolymerFamilies_sum_Λ_eq_one_add G (Λ.volume n) t

/-- **Along-ex: 1 ≤ vdSum** under `0 ≤ t`. -/
theorem vdPolymerFamilies_sumAlongExhaustion_ge_one_of_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    1 ≤ ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card :=
  vdPolymerFamilies_sum_Λ_ge_one_of_nonneg G (Λ.volume n) ht

/-- **Along-ex: vdSum ≤ (1+t)^|E|** under `0 ≤ t`. -/
theorem vdPolymerFamilies_sumAlongExhaustion_le_one_plus_pow_of_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card)
      ≤ (1 + t) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card :=
  vdPolymerFamilies_sum_Λ_le_one_plus_pow_of_nonneg G (Λ.volume n) ht

end Ambient
end IsingModel

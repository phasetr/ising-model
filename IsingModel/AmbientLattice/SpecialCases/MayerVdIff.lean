import IsingModel.AmbientLattice.AnalyticityLambdaPolymer
import IsingModel.AmbientLattice.AnalyticityLambdaBasicIdentities
import IsingModel.AmbientLattice.Exhaustion

/-!
# Mayer vd iff characterization wrappers along an exhaustion

Narrow child module for along-exhaustion iff characterizations of
`vdPolymerFamilies_sum`. This keeps callers that only need the equivalence
wrappers out of the monolithic original special-cases module.

Merged from the former `MayerVdIffTanh.lean` child (#4563 cycle 15 fixed-cost
consolidation): the two along-exhaustion
`vdPolymerFamilies_sumAlongExhaustion_tanh_*_iff` characterization wrappers
now live directly here. All theorem names/statements are preserved verbatim;
see git history of the deleted `MayerVdIffTanh.lean` for provenance.
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

/-! ### §18.5 vdPolymerFamilies_sum `tanh` iff characterizations along-ex wraps -/

/-- **Along-ex: vdSum_tanh > 1 ↔ 0 < tanh ∧ allPolymers ≠ ∅**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_tanh_gt_one_iff
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    1 < (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ↔
      0 < Real.tanh (β * J) ∧
        (IsingModel.allPolymers
          (inducedGraph G (Λ.volume n))).Nonempty :=
  vdPolymerFamilies_sum_Λ_tanh_gt_one_iff G (Λ.volume n) hβJ

/-- **Along-ex: vdSum_tanh = 1 ↔ tanh = 0 ∨ allPolymers = ∅**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_tanh_eq_one_iff
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 1 ↔
      Real.tanh (β * J) = 0 ∨
        IsingModel.allPolymers
          (inducedGraph G (Λ.volume n)) = ∅ :=
  vdPolymerFamilies_sum_Λ_tanh_eq_one_iff G (Λ.volume n) hβJ

end Ambient
end IsingModel

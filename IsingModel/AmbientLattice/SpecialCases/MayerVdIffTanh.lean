import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaBasicIdentities

/-!
# Mayer vd `tanh` iff characterization wrappers along an exhaustion

Narrow child module for the two along-exhaustion
`vdPolymerFamilies_sumAlongExhaustion_tanh_*_iff` characterization
wrappers extracted from `MayerVdIff.lean`:

* `vdPolymerFamilies_sumAlongExhaustion_tanh_gt_one_iff`
* `vdPolymerFamilies_sumAlongExhaustion_tanh_eq_one_iff`

Each wrapper is a thin pass-through to the corresponding ambient
`vdPolymerFamilies_sum_Λ_tanh_*_iff` lemma characterizing the
`> 1` / `= 1` cases of the vd sum at the tanh argument by joint
behaviour of `tanh(βJ)` and `allPolymers`. Theorem names are
unchanged from the former `MayerVdIff` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

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

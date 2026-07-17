import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaEpsilonIff

/-!
# `vdPolymerFamilies_sum` pointwise tanh-positivity wrappers along an exhaustion

Narrow child module for the two §18.5 along-exhaustion
`vdPolymerFamilies_sum_*_tanh_*_of_polymers_nonempty` pointwise
positivity wrappers extracted from
`MayerStrictPositivityVdSumPointwise.lean`:

* `vdPolymerFamilies_sumAlongExhaustion_tanh_gt_one_of_tanh_pos_of_polymers_nonempty`
* `vdPolymerFamilies_sumAlongExhaustion_minus_one_tanh_pos_of_tanh_pos_of_polymers_nonempty`

Each wrapper is a thin pass-through to the corresponding ambient
`vdPolymerFamilies_sum_Λ_*_tanh_*_of_polymers_nonempty` lemma.
Theorem names are unchanged from the former
`MayerStrictPositivityVdSum` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: 1 < vdSum(tanh) under `0 < tanh` and polymers
exist**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_tanh_gt_one_of_tanh_pos_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (h_tanh_pos : 0 < Real.tanh (β * J)) (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph G (Λ.volume n))).Nonempty) :
    1 < (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n)),
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :=
  vdPolymerFamilies_sum_Λ_tanh_gt_one_of_tanh_pos_of_polymers_nonempty
    G (Λ.volume n) h_tanh_pos h_poly

/-- **Along-ex: 0 < ε(tanh) under `0 < tanh` and polymers exist**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_minus_one_tanh_pos_of_tanh_pos_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (h_tanh_pos : 0 < Real.tanh (β * J)) (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph G (Λ.volume n))).Nonempty) :
    0 < (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :=
  vdPolymerFamilies_sum_Λ_minus_one_tanh_pos_of_tanh_pos_of_polymers_nonempty
    G (Λ.volume n) h_tanh_pos h_poly

end Ambient
end IsingModel

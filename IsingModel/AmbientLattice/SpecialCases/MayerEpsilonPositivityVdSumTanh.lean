import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaEpsilonIff

/-!
# `vdPolymerFamilies_sum` ε(tanh) positivity-iff wrappers along an exhaustion

Narrow child module for the two §18.5 along-exhaustion
`vdPolymerFamilies_sumAlongExhaustion_minus_one_tanh_*_iff`
positivity / zero iff wrappers (tanh-form) extracted from
`MayerEpsilonPositivityVdSum.lean`:

* `vdPolymerFamilies_sumAlongExhaustion_minus_one_tanh_pos_iff`
* `vdPolymerFamilies_sumAlongExhaustion_minus_one_tanh_eq_zero_iff`

Each wrapper is a thin pass-through to the corresponding
`vdPolymerFamilies_sum_Λ_minus_one_tanh_*_iff` ambient lemma.
Theorem names are unchanged from the former
`MayerEpsilonPositivity` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: 0 < ε(tanh) ↔ 0 < tanh ∧ allPolymers ≠ ∅**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_minus_one_tanh_pos_iff
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    0 < (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ↔
      0 < Real.tanh (β * J) ∧
        (IsingModel.allPolymers
          (inducedGraph G (Λ.volume n))).Nonempty :=
  vdPolymerFamilies_sum_Λ_minus_one_tanh_pos_iff G (Λ.volume n) hβJ

/-- **Along-ex: ε(tanh) = 0 ↔ tanh = 0 ∨ allPolymers = ∅**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_minus_one_tanh_eq_zero_iff
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 0 ↔
      Real.tanh (β * J) = 0 ∨
        IsingModel.allPolymers
          (inducedGraph G (Λ.volume n)) = ∅ :=
  vdPolymerFamilies_sum_Λ_minus_one_tanh_eq_zero_iff
    G (Λ.volume n) hβJ

end Ambient
end IsingModel

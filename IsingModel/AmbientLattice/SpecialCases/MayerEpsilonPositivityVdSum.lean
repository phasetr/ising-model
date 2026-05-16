import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.MayerEpsilonPositivityVdSumTanh

/-!
# `vdPolymerFamilies_sum` ε(t) positivity-iff wrappers along an exhaustion

Narrow child module for the two general-`t` §18.5 along-exhaustion
`vdPolymerFamilies_sumAlongExhaustion_minus_one_*_iff` positivity /
zero iff wrappers. The two tanh-form variants now live in
`IsingModel.AmbientLattice.SpecialCases.MayerEpsilonPositivityVdSumTanh`
and are re-imported through this parent module. Each wrapper is a
thin pass-through to the corresponding
`vdPolymerFamilies_sum_Λ_minus_one_*_iff` ambient lemma. Theorem
names are unchanged from the former `MayerEpsilonPositivity`
declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: 0 < ε(t) ↔ 0 < t ∧ allPolymers ≠ ∅** under `0 ≤ t`. -/
theorem vdPolymerFamilies_sumAlongExhaustion_minus_one_pos_iff
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    0 < (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, t ^ P.card) ↔
      0 < t ∧
        (IsingModel.allPolymers
          (inducedGraph G (Λ.volume n))).Nonempty :=
  vdPolymerFamilies_sum_Λ_minus_one_pos_iff G (Λ.volume n) ht

/-- **Along-ex: ε(t) = 0 ↔ t = 0 ∨ allPolymers = ∅**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_minus_one_eq_zero_iff
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
          ∏ P ∈ Γ, t ^ P.card) = 0 ↔
      t = 0 ∨
        IsingModel.allPolymers
          (inducedGraph G (Λ.volume n)) = ∅ :=
  vdPolymerFamilies_sum_Λ_minus_one_eq_zero_iff G (Λ.volume n) ht

/-! ## Moved: 2 ε(tanh) positivity-iff wrappers

The two tanh-form
`vdPolymerFamilies_sumAlongExhaustion_minus_one_tanh_*_iff`
positivity / zero iff wrappers now live in
`IsingModel.AmbientLattice.SpecialCases.MayerEpsilonPositivityVdSumTanh`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

end Ambient
end IsingModel

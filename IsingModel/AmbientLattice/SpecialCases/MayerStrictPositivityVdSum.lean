import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.MayerStrictPositivityVdSumPointwise

/-!
# `vdPolymerFamilies_sum` strict-positivity wrappers along an exhaustion

Narrow child module for the seven §18.5 along-exhaustion
`vdPolymerFamilies_sum` strict-monotonicity / strict-positivity
wrappers under `allPolymers` nonempty hypotheses (general,
tanh-composed, and `StrictMonoOn` on `Ici 0` / `Ioi 0`). Each
wrapper is a thin pass-through to the corresponding
`vdPolymerFamilies_sum_Λ_*` ambient lemma. Theorem names are
unchanged from the former `MayerStrictPositivity` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: vdSum(s) < vdSum(t) under polymers exist**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_lt_of_lt_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph G (Λ.volume n))).Nonempty)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n)),
        ∏ P ∈ Γ, s ^ P.card) <
      ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card :=
  vdPolymerFamilies_sum_Λ_lt_of_lt_of_polymers_nonempty
    G (Λ.volume n) h_poly hs hst

/-- **Along-ex: vdSum is `StrictMonoOn (Set.Ici 0)`**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_strictMonoOn_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph G (Λ.volume n))).Nonempty) :
    StrictMonoOn
      (fun t : ℝ => ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card) (Set.Ici 0) :=
  vdPolymerFamilies_sum_Λ_strictMonoOn_of_polymers_nonempty
    G (Λ.volume n) h_poly

/-! ## Moved: vdPolymerFamilies_sum pointwise positivity wrappers

The four pointwise wrappers
(`_gt_one_of_t_pos_of_polymers_nonempty`,
`_minus_one_pos_of_t_pos_of_polymers_nonempty`,
`_tanh_gt_one_of_tanh_pos_of_polymers_nonempty`,
`_minus_one_tanh_pos_of_tanh_pos_of_polymers_nonempty`) now live in
`IsingModel.AmbientLattice.SpecialCases.MayerStrictPositivityVdSumPointwise`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

/-- **Along-ex: vdSum is `StrictMonoOn (Set.Ioi 0)`**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_strictMonoOn_Ioi_zero_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph G (Λ.volume n))).Nonempty) :
    StrictMonoOn
      (fun t : ℝ => ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card) (Set.Ioi 0) :=
  vdPolymerFamilies_sum_Λ_strictMonoOn_Ioi_zero_of_polymers_nonempty
    G (Λ.volume n) h_poly

end Ambient
end IsingModel

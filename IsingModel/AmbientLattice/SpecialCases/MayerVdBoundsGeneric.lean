import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.MayerVdBoundsGenericSandwich

/-!
# Mayer vd generic-t bound wrappers along an exhaustion

Narrow child module for four §18.5 along-exhaustion
`vdPolymerFamilies_sum` generic-`t` bound and decomposition
wrappers (separating from the tanh-form bounds that remain in the
parent). Each wrapper is a thin pass-through to the corresponding
`vdPolymerFamilies_sum_Λ_*` ambient lemma. Theorem names are
unchanged from the former `MayerVdBounds` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-! ### §18.5 vdPolymerFamilies_sum generic-t bounds along-ex -/

/-! ## Moved: 2 sandwich bound wrappers

The two sandwich bound wrappers
(`vdPolymerFamilies_sumAlongExhaustion_ge_one_of_nonneg`,
`vdPolymerFamilies_sumAlongExhaustion_le_one_plus_pow_of_nonneg`)
now live in
`IsingModel.AmbientLattice.SpecialCases.MayerVdBoundsGenericSandwich`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella.
-/

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

end Ambient
end IsingModel

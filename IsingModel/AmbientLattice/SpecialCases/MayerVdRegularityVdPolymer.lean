import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.MayerVdRegularityVdPolymerTanh

/-!
# `vdPolymerFamilies_sum` regularity wrappers along an exhaustion

Narrow child module for the seven §18.5 `vdPolymerFamilies_sum`
along-exhaustion regularity and tanh wrappers (`Continuous`,
`Differentiable`, `HasDerivAt`, and the four tanh-composed
continuity / differentiability wrappers in `β` and `J`). Theorem
names are unchanged from the former `MayerVdRegularity` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### §18.5 vdPolymerFamilies_sum regularity along-ex wraps -/

/-- **Along-ex: `vdPolymerFamilies_sum` is `Continuous` in `t`**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_continuous
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    Continuous (fun t : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card) :=
  vdPolymerFamilies_sum_Λ_continuous G (Λ.volume n)

/-- **Along-ex: `vdPolymerFamilies_sum` is `Differentiable ℝ`
in `t`**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_differentiable
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    Differentiable ℝ (fun t : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card) :=
  vdPolymerFamilies_sum_Λ_differentiable G (Λ.volume n)

/-- **Along-ex: `vdPolymerFamilies_sum` `HasDerivAt`**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_hasDerivAt
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (n : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, s ^ P.card)
      (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
        ∑ Q ∈ Γ, (∏ P ∈ Γ.erase Q, t ^ P.card) *
          ((Q.card : ℝ) * t ^ (Q.card - 1))) t :=
  vdPolymerFamilies_sum_Λ_hasDerivAt G (Λ.volume n) t

/-! ## Moved: vdPolymerFamilies_sum tanh β/J along-ex wraps

The four `vdPolymerFamilies_sumAlongExhaustion_tanh_*` wrappers
(`_continuous_beta`, `_continuous_J`, `_differentiable_beta`,
`_differentiable_J`) now live in
`IsingModel.AmbientLattice.SpecialCases.MayerVdRegularityVdPolymerTanh`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

end Ambient
end IsingModel

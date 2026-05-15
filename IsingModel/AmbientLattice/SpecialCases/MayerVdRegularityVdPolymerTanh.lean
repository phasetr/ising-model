import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion

/-!
# `vdPolymerFamilies_sum` tanh regularity wrappers along an exhaustion

Narrow child module for four §18.5 `vdPolymerFamilies_sum`
along-exhaustion tanh-composed continuity / differentiability
wrappers in `β` and `J`. Each wrapper is a thin pass-through to the
corresponding `vdPolymerFamilies_sum_Λ_tanh_*` ambient lemma.
Theorem names are unchanged from the former `MayerVdRegularityVdPolymer`
declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### §18.5 vdPolymerFamilies_sum tanh β/J along-ex wraps -/

/-- **Along-ex: vdPolymerFamilies_sum ∘ tanh ∘ (·*J) continuous in β**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_tanh_continuous_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) (n : ℕ) :
    Continuous (fun β' : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, Real.tanh (β' * J) ^ P.card) :=
  vdPolymerFamilies_sum_Λ_tanh_continuous_beta G (Λ.volume n) J

/-- **Along-ex: vdPolymerFamilies_sum ∘ tanh ∘ (β*·) continuous in J**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_tanh_continuous_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (n : ℕ) :
    Continuous (fun J' : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, Real.tanh (β * J') ^ P.card) :=
  vdPolymerFamilies_sum_Λ_tanh_continuous_J G (Λ.volume n) β

/-- **Along-ex: vdPolymerFamilies_sum ∘ tanh ∘ (·*J) differentiable in β**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_tanh_differentiable_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) (n : ℕ) :
    Differentiable ℝ (fun β' : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, Real.tanh (β' * J) ^ P.card) :=
  vdPolymerFamilies_sum_Λ_tanh_differentiable_beta G (Λ.volume n) J

/-- **Along-ex: vdPolymerFamilies_sum ∘ tanh ∘ (β*·) differentiable in J**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_tanh_differentiable_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (n : ℕ) :
    Differentiable ℝ (fun J' : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, Real.tanh (β * J') ^ P.card) :=
  vdPolymerFamilies_sum_Λ_tanh_differentiable_J G (Λ.volume n) β

end Ambient
end IsingModel

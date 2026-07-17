import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaVdPolymer

/-!
# `vdPolymerFamilies_sum` tanh `Differentiable` along-ex wrappers

Narrow child module for the two §18.5 along-exhaustion
`vdPolymerFamilies_sum ∘ tanh ∘ (·)` `Differentiable` wrappers
extracted from `MayerVdRegularityVdPolymerTanh.lean`:

* `vdPolymerFamilies_sumAlongExhaustion_tanh_differentiable_beta`
* `vdPolymerFamilies_sumAlongExhaustion_tanh_differentiable_J`

Each wrapper is a thin pass-through to the corresponding
`vdPolymerFamilies_sum_Λ_tanh_differentiable_*` ambient lemma.
Theorem names are unchanged from the former
`MayerVdRegularityVdPolymer` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

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

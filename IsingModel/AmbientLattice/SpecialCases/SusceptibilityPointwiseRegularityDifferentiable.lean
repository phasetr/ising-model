import IsingModel.AmbientLattice.MagnetizationAlongExhaustion

/-!
# Susceptibility `Differentiable` in `h` / `J` along-ex wrappers

Narrow child module for the two along-exhaustion susceptibility
`Differentiable` wrappers in the field and coupling directions:

* `susceptibilityAlongExhaustion_differentiable_field_gen`
* `susceptibilityAlongExhaustion_differentiable_J_gen`

The corresponding `β`-direction wrapper now lives in
`IsingModel.AmbientLattice.SpecialCases.SusceptibilityPointwiseRegularityDifferentiableBeta`
and is re-imported through this parent module. Each wrapper is a
thin pass-through to the corresponding
`susceptibilityΛ_differentiable_*` ambient lemma via `unfold`
+ `by_cases`. Theorem names are unchanged from the former
`SusceptibilityPointwiseRegularity` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ## Moved: 1 Differentiable in `β` wrapper

The `susceptibilityAlongExhaustion_differentiable_beta_gen` wrapper
now lives in
`IsingModel.AmbientLattice.SpecialCases.SusceptibilityPointwiseRegularityDifferentiableBeta`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

/-- **Along-ex: susceptibility Differentiable in `h`** (general G). -/
theorem susceptibilityAlongExhaustion_differentiable_field_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (i : V) (n : ℕ) :
    Differentiable ℝ (fun h' =>
      susceptibilityAlongExhaustion G Λ
        (⟨J, h', β⟩ : IsingParams ℝ) i n) := by
  unfold susceptibilityAlongExhaustion
  by_cases hi : i ∈ Λ.volume n
  · simp only [hi, dif_pos]
    exact susceptibilityΛ_differentiable_field G (Λ.volume n) J β _
  · simp only [hi, dif_neg, not_false_iff]
    exact differentiable_const _

/-- **Along-ex: susceptibility Differentiable in `J`** (general G). -/
theorem susceptibilityAlongExhaustion_differentiable_J_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ) (i : V) (n : ℕ) :
    Differentiable ℝ (fun J' =>
      susceptibilityAlongExhaustion G Λ
        (⟨J', h, β⟩ : IsingParams ℝ) i n) := by
  unfold susceptibilityAlongExhaustion
  by_cases hi : i ∈ Λ.volume n
  · simp only [hi, dif_pos]
    exact susceptibilityΛ_differentiable_J G (Λ.volume n) h β _
  · simp only [hi, dif_neg, not_false_iff]
    exact differentiable_const _

end Ambient
end IsingModel

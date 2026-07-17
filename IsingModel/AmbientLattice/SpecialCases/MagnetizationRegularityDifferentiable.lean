import IsingModel.AmbientLattice.Defs
import IsingModel.AmbientLattice.Exhaustion

/-!
# Magnetization `Differentiable` in `h` / `J` along-ex wrappers

Narrow child module for the two along-exhaustion magnetization
`Differentiable` wrappers in the field and coupling directions:

* `magnetizationAlongExhaustion_differentiable_field`
* `magnetizationAlongExhaustion_differentiable_J`

The corresponding `β`-direction wrapper now lives in
`IsingModel.AmbientLattice.SpecialCases.MagnetizationRegularityDifferentiableBeta`
and is re-imported through this parent module. Each wrapper is a
thin pass-through to the corresponding
`magnetizationΛ_differentiable_*` ambient lemma via
`unfold`/`by_cases`. Theorem names are unchanged from the former
`MagnetizationRegularity` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: magnetization Differentiable in `h`**. -/
theorem magnetizationAlongExhaustion_differentiable_field
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (i : V) (n : ℕ) :
    Differentiable ℝ (fun h' =>
      magnetizationAlongExhaustion G Λ
        (⟨J, h', β⟩ : IsingParams ℝ) i n) := by
  unfold magnetizationAlongExhaustion correlationAlongExhaustion
  by_cases hi : ({i} : Finset V) ⊆ Λ.volume n
  · simp only [hi, dif_pos]
    exact magnetizationΛ_differentiable_field G (Λ.volume n) J β _
  · simp only [hi, dif_neg, not_false_iff]
    exact differentiable_const _

/-- **Along-ex: magnetization Differentiable in `J`**. -/
theorem magnetizationAlongExhaustion_differentiable_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ) (i : V) (n : ℕ) :
    Differentiable ℝ (fun J' =>
      magnetizationAlongExhaustion G Λ
        (⟨J', h, β⟩ : IsingParams ℝ) i n) := by
  unfold magnetizationAlongExhaustion correlationAlongExhaustion
  by_cases hi : ({i} : Finset V) ⊆ Λ.volume n
  · simp only [hi, dif_pos]
    exact magnetizationΛ_differentiable_J G (Λ.volume n) h β _
  · simp only [hi, dif_neg, not_false_iff]
    exact differentiable_const _

/-! ## Moved: 1 Differentiable in `β` wrapper

The `magnetizationAlongExhaustion_differentiable_beta` wrapper now
lives in
`IsingModel.AmbientLattice.SpecialCases.MagnetizationRegularityDifferentiableBeta`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

end Ambient
end IsingModel

import IsingModel.AmbientLattice.SpecialCases.SusceptibilityPointwiseRegularityDifferentiable

/-!
# Susceptibility `DifferentiableAt` along-ex wrappers

Narrow child module for the three pointwise `DifferentiableAt`
susceptibility wrappers along an exhaustion extracted from
`SusceptibilityPointwiseRegularityAt.lean`:

* `susceptibilityAlongExhaustion_differentiableAt_beta_gen`
* `susceptibilityAlongExhaustion_differentiableAt_field_gen`
* `susceptibilityAlongExhaustion_differentiableAt_J_gen`

Each wrapper is a thin pass-through to the corresponding
`susceptibilityAlongExhaustion_differentiable_*_gen` parent lemma
via the `.differentiableAt` projection. Theorem names are unchanged
from the former `SusceptibilityPointwiseRegularity` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ## Moved: 1 DifferentiableAt β wrapper

The `susceptibilityAlongExhaustion_differentiableAt_beta_gen`
wrapper now lives in
`IsingModel.AmbientLattice.SpecialCases.SusceptibilityPointwiseRegularityAtDifferentiableAtBeta`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

/-- **Along-ex: susceptibility DifferentiableAt h** (general G). -/
theorem susceptibilityAlongExhaustion_differentiableAt_field_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    DifferentiableAt ℝ
      (fun h' => susceptibilityAlongExhaustion G Λ
          (⟨J, h', β⟩ : IsingParams ℝ) i n) h :=
  (susceptibilityAlongExhaustion_differentiable_field_gen G Λ J β i n).differentiableAt

/-- **Along-ex: susceptibility DifferentiableAt J** (general G). -/
theorem susceptibilityAlongExhaustion_differentiableAt_J_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    DifferentiableAt ℝ
      (fun J' => susceptibilityAlongExhaustion G Λ
          (⟨J', h, β⟩ : IsingParams ℝ) i n) J :=
  (susceptibilityAlongExhaustion_differentiable_J_gen G Λ h β i n).differentiableAt

end Ambient
end IsingModel

import IsingModel.AmbientLattice.SpecialCases.SusceptibilityPointwiseRegularity
import IsingModel.AmbientLattice.SpecialCases.SusceptibilityPointwiseRegularityAtDifferentiableAt
import IsingModel.AmbientLattice.SpecialCases.SusceptibilityPointwiseRegularityAtContinuousAtBeta

/-!
# Susceptibility `ContinuousAt` along-ex wrappers

Narrow child module for the three pointwise `ContinuousAt`
susceptibility wrappers along an exhaustion, obtained from the
corresponding `_continuous_*_gen` wrappers in the parent
`SusceptibilityPointwiseRegularity` module via the `.continuousAt`
projection. Theorem names are unchanged from the former
`SusceptibilityPointwiseRegularity` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ## Moved: 1 ContinuousAt β wrapper

The `susceptibilityAlongExhaustion_continuousAt_beta_gen` wrapper
now lives in
`IsingModel.AmbientLattice.SpecialCases.SusceptibilityPointwiseRegularityAtContinuousAtBeta`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

/-! ## Moved: 3 susceptibilityAlongExhaustion_differentiableAt_*_gen wrappers

The three `DifferentiableAt ℝ` pointwise wrappers
(`susceptibilityAlongExhaustion_differentiableAt_beta_gen`,
`susceptibilityAlongExhaustion_differentiableAt_field_gen`,
`susceptibilityAlongExhaustion_differentiableAt_J_gen`) now live in
`IsingModel.AmbientLattice.SpecialCases.`
`SusceptibilityPointwiseRegularityAtDifferentiableAt`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

/-- **Along-ex: susceptibility ContinuousAt h** (general G). -/
theorem susceptibilityAlongExhaustion_continuousAt_field_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    ContinuousAt
      (fun h' => susceptibilityAlongExhaustion G Λ
          (⟨J, h', β⟩ : IsingParams ℝ) i n) h :=
  (susceptibilityAlongExhaustion_continuous_field_gen G Λ J β i n).continuousAt

/-- **Along-ex: susceptibility ContinuousAt J** (general G). -/
theorem susceptibilityAlongExhaustion_continuousAt_J_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    ContinuousAt
      (fun J' => susceptibilityAlongExhaustion G Λ
          (⟨J', h, β⟩ : IsingParams ℝ) i n) J :=
  (susceptibilityAlongExhaustion_continuous_J_gen G Λ h β i n).continuousAt

end Ambient
end IsingModel

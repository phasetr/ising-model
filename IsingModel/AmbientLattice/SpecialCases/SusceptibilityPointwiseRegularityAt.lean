import IsingModel.AmbientLattice.SpecialCases.SusceptibilityPointwiseRegularity
import IsingModel.AmbientLattice.SpecialCases.SusceptibilityPointwiseRegularityAtDifferentiableAt
import IsingModel.AmbientLattice.SpecialCases.SusceptibilityPointwiseRegularityAtContinuousAtBeta

/-!
# Susceptibility `ContinuousAt` along-ex wrappers

Turns the parametrized continuity of the along-exhaustion susceptibility into pointwise
`ContinuousAt` form via the `.continuousAt` projection, the shape used by the GJ §17.6
derivative arguments.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

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

import IsingModel.AmbientLattice.SpecialCases.SusceptibilityPointwiseRegularityContinuousBeta

/-!
# Susceptibility `ContinuousAt` in `β` along-ex wrapper

Narrow child module for the pointwise
`susceptibilityAlongExhaustion_continuousAt_beta_gen` wrapper
extracted from `SusceptibilityPointwiseRegularityAt.lean`. The
wrapper is a thin pass-through to
`susceptibilityAlongExhaustion_continuous_beta_gen` via the
`.continuousAt` projection. The theorem name is unchanged from
the former `SusceptibilityPointwiseRegularity` declaration.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: susceptibility ContinuousAt β** (general G, general h). -/
theorem susceptibilityAlongExhaustion_continuousAt_beta_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    ContinuousAt
      (fun β' => susceptibilityAlongExhaustion G Λ
          (⟨J, h, β'⟩ : IsingParams ℝ) i n) β :=
  (susceptibilityAlongExhaustion_continuous_beta_gen G Λ J h i n).continuousAt

end Ambient
end IsingModel

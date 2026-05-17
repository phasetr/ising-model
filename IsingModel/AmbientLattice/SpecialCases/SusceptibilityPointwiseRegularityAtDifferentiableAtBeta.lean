import IsingModel.AmbientLattice.SpecialCases.SusceptibilityPointwiseRegularityDifferentiableBeta

/-!
# Susceptibility `DifferentiableAt` in `β` along-ex wrapper

Narrow child module for the pointwise
`susceptibilityAlongExhaustion_differentiableAt_beta_gen` wrapper
extracted from
`SusceptibilityPointwiseRegularityAtDifferentiableAt.lean`. The
wrapper is a thin pass-through to
`susceptibilityAlongExhaustion_differentiable_beta_gen` via the
`.differentiableAt` projection. The theorem name is unchanged from
the former `SusceptibilityPointwiseRegularity` declaration.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: susceptibility DifferentiableAt β** (general G, general h). -/
theorem susceptibilityAlongExhaustion_differentiableAt_beta_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    DifferentiableAt ℝ
      (fun β' => susceptibilityAlongExhaustion G Λ
          (⟨J, h, β'⟩ : IsingParams ℝ) i n) β :=
  (susceptibilityAlongExhaustion_differentiable_beta_gen G Λ J h i n).differentiableAt

end Ambient
end IsingModel

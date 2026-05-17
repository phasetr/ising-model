import IsingModel.AmbientLattice.SpecialCases.MagnetizationRegularityDifferentiableBeta

/-!
# Magnetization `DifferentiableAt` in `β` along-ex wrapper

Narrow child module for the pointwise
`magnetizationAlongExhaustion_differentiableAt_beta` wrapper
extracted from `MagnetizationRegularityAtDifferentiableAt.lean`.
The wrapper is a thin pass-through to
`magnetizationAlongExhaustion_differentiable_beta` via the
`.differentiableAt` projection. The theorem name is unchanged from
the former `MagnetizationRegularity` declaration.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: magnetization DifferentiableAt β** (general h). -/
theorem magnetizationAlongExhaustion_differentiableAt_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    DifferentiableAt ℝ
      (fun β' => magnetizationAlongExhaustion G Λ
          (⟨J, h, β'⟩ : IsingParams ℝ) i n) β :=
  (magnetizationAlongExhaustion_differentiable_beta G Λ J h i n).differentiableAt

end Ambient
end IsingModel

import IsingModel.AmbientLattice.SpecialCases.MagnetizationRegularityContinuousBeta

/-!
# Magnetization `ContinuousAt` in `β` along-ex wrapper

Narrow child module for the pointwise
`magnetizationAlongExhaustion_continuousAt_beta` wrapper extracted
from `MagnetizationRegularityAt.lean`. The wrapper is a thin
pass-through to `magnetizationAlongExhaustion_continuous_beta` via
the `.continuousAt` projection. The theorem name is unchanged from
the former `MagnetizationRegularity` declaration.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: magnetization ContinuousAt β** (general h). -/
theorem magnetizationAlongExhaustion_continuousAt_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    ContinuousAt
      (fun β' => magnetizationAlongExhaustion G Λ
          (⟨J, h, β'⟩ : IsingParams ℝ) i n) β :=
  (magnetizationAlongExhaustion_continuous_beta G Λ J h i n).continuousAt

end Ambient
end IsingModel

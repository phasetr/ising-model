import IsingModel.AmbientLattice.SpecialCases.MagnetizationRegularity

/-!
# Magnetization `ContinuousAt` along-ex wrappers

Narrow child module for the three pointwise `ContinuousAt`
wrappers along an exhaustion, obtained from the corresponding
`Continuous` wrappers in the parent `MagnetizationRegularity`
module via the `.continuousAt` projection. Theorem names are
unchanged from the former `MagnetizationRegularity` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-! ### ContinuousAt / DifferentiableAt along-ex wrappers -/

/-! ## Moved: 1 ContinuousAt β wrapper

The `magnetizationAlongExhaustion_continuousAt_beta` wrapper now
lives in
`IsingModel.AmbientLattice.SpecialCases.MagnetizationRegularityAtContinuousAtBeta`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

/-! ## Moved: 3 magnetizationAlongExhaustion_differentiableAt_* wrappers

The three `DifferentiableAt ℝ` pointwise wrappers
(`magnetizationAlongExhaustion_differentiableAt_beta`,
`magnetizationAlongExhaustion_differentiableAt_field`,
`magnetizationAlongExhaustion_differentiableAt_J`) now live in
`IsingModel.AmbientLattice.SpecialCases.MagnetizationRegularityAtDifferentiableAt`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

/-- **Along-ex: magnetization ContinuousAt h**. -/
theorem magnetizationAlongExhaustion_continuousAt_field
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    ContinuousAt
      (fun h' => magnetizationAlongExhaustion G Λ
          (⟨J, h', β⟩ : IsingParams ℝ) i n) h :=
  (magnetizationAlongExhaustion_continuous_field G Λ J β i n).continuousAt

/-- **Along-ex: magnetization ContinuousAt J**. -/
theorem magnetizationAlongExhaustion_continuousAt_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    ContinuousAt
      (fun J' => magnetizationAlongExhaustion G Λ
          (⟨J', h, β⟩ : IsingParams ℝ) i n) J :=
  (magnetizationAlongExhaustion_continuous_J G Λ h β i n).continuousAt

end Ambient
end IsingModel

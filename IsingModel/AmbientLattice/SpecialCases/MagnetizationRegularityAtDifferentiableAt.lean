import IsingModel.AmbientLattice.SpecialCases.MagnetizationRegularity
import IsingModel.AmbientLattice.SpecialCases.MagnetizationRegularityAtDifferentiableAtBeta

/-!
# Magnetization `DifferentiableAt` in `h` / `J` along-ex wrappers

Narrow child module for the two pointwise field / coupling
`DifferentiableAt` wrappers along an exhaustion extracted from
`MagnetizationRegularityAt.lean`:

* `magnetizationAlongExhaustion_differentiableAt_field`
* `magnetizationAlongExhaustion_differentiableAt_J`

The corresponding `β`-direction wrapper now lives in
`IsingModel.AmbientLattice.SpecialCases.MagnetizationRegularityAtDifferentiableAtBeta`
and is re-imported through this parent module. Each wrapper is a
thin pass-through to the corresponding
`magnetizationAlongExhaustion_differentiable_*` parent lemma via
the `.differentiableAt` projection. Theorem names are unchanged
from the former `MagnetizationRegularity` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-! ## Moved: 1 DifferentiableAt β wrapper

The `magnetizationAlongExhaustion_differentiableAt_beta` wrapper
now lives in
`IsingModel.AmbientLattice.SpecialCases.MagnetizationRegularityAtDifferentiableAtBeta`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

/-- **Along-ex: magnetization DifferentiableAt h**. -/
theorem magnetizationAlongExhaustion_differentiableAt_field
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    DifferentiableAt ℝ
      (fun h' => magnetizationAlongExhaustion G Λ
          (⟨J, h', β⟩ : IsingParams ℝ) i n) h :=
  (magnetizationAlongExhaustion_differentiable_field G Λ J β i n).differentiableAt

/-- **Along-ex: magnetization DifferentiableAt J**. -/
theorem magnetizationAlongExhaustion_differentiableAt_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    DifferentiableAt ℝ
      (fun J' => magnetizationAlongExhaustion G Λ
          (⟨J', h, β⟩ : IsingParams ℝ) i n) J :=
  (magnetizationAlongExhaustion_differentiable_J G Λ h β i n).differentiableAt

end Ambient
end IsingModel

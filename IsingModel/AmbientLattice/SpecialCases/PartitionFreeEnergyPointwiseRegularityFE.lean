import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyPointwiseRegularityFENonJoint

/-!
# Ambient freeEnergyAlongExhaustion pointwise wrappers

Narrow child module for 8 ambient `freeEnergyAlongExhaustion_*`
ContinuousAt / DifferentiableAt pointwise wrappers extracted from
`PartitionFreeEnergyPointwiseRegularity.lean`:

* `freeEnergyAlongExhaustion_continuousAt_beta`,
* `freeEnergyAlongExhaustion_differentiableAt_beta`,
* `freeEnergyAlongExhaustion_continuousAt_field`,
* `freeEnergyAlongExhaustion_differentiableAt_field`,
* `freeEnergyAlongExhaustion_continuousAt_J`,
* `freeEnergyAlongExhaustion_differentiableAt_J`,
* `freeEnergyAlongExhaustion_continuousAt_joint`,
* `freeEnergyAlongExhaustion_differentiableAt_joint`.

Each result is a thin pass-through lifting the corresponding Λ-level
`freeEnergyΛ_{continuous,differentiable}_*` lemma to AlongExhaustion
via `.continuousAt` / `.differentiableAt`. The theorem names are
unchanged from the former `PartitionFreeEnergyPointwiseRegularity`
declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]


/-! ### Along-exhaustion free-energy pointwise wrappers -/

/-! ## Moved: non-joint ContinuousAt / DifferentiableAt wrappers

The six `freeEnergyAlongExhaustion_{continuousAt,differentiableAt}_{beta,field,J}`
non-joint pointwise wrappers now live in
`IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyPointwiseRegularityFENonJoint`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

/-- **freeEnergyAlongExhaustion jointly ContinuousAt**. -/
theorem freeEnergyAlongExhaustion_continuousAt_joint
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (n : ℕ) (p : ℝ × ℝ × ℝ) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨q.2.1, q.2.2, q.1⟩ n) p :=
  (freeEnergyΛ_continuous_joint G (Λ.volume n)).continuousAt

/-- **freeEnergyAlongExhaustion jointly DifferentiableAt**. -/
theorem freeEnergyAlongExhaustion_differentiableAt_joint
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (n : ℕ) (p : ℝ × ℝ × ℝ) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ × ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨q.2.1, q.2.2, q.1⟩ n) p :=
  (freeEnergyΛ_differentiable_joint G (Λ.volume n)).differentiableAt


end Ambient
end IsingModel

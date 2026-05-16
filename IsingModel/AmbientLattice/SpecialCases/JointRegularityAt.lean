import IsingModel.AmbientLattice.SpecialCases.JointRegularity
import IsingModel.AmbientLattice.SpecialCases.JointRegularityAtDifferentiableAt

/-!
# Joint `ContinuousAt` along-ex wrappers

Narrow child module for the three pointwise joint `ContinuousAt`
wrappers along an exhaustion (correlation, magnetization,
susceptibility), obtained from the corresponding
`_continuous_joint*` wrappers in the parent `JointRegularity`
module via the `.continuousAt` projection. Theorem names are
unchanged from the former `JointRegularity` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: correlation jointly ContinuousAt** (general G). -/
theorem correlationAlongExhaustion_continuousAt_joint_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (A : Finset V) (n : ℕ) (p : ℝ × ℝ × ℝ) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ =>
      correlationAlongExhaustion G Λ ⟨q.2.1, q.2.2, q.1⟩ A n) p :=
  (correlationAlongExhaustion_continuous_joint_gen G Λ A n).continuousAt

/-! ## Moved: 3 joint DifferentiableAt wrappers

The three `DifferentiableAt ℝ` joint wrappers
(`correlationAlongExhaustion_differentiableAt_joint_gen`,
`magnetizationAlongExhaustion_differentiableAt_joint`,
`susceptibilityAlongExhaustion_differentiableAt_joint_gen`) now
live in
`IsingModel.AmbientLattice.SpecialCases.JointRegularityAtDifferentiableAt`.
The legacy import path is preserved by re-exporting the new child
from this parent module and from `Legacy.lean`.
-/

/-- **Along-ex: magnetization jointly ContinuousAt** (general G). -/
theorem magnetizationAlongExhaustion_continuousAt_joint
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (i : V) (n : ℕ) (p : ℝ × ℝ × ℝ) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ =>
      magnetizationAlongExhaustion G Λ ⟨q.2.1, q.2.2, q.1⟩ i n) p :=
  (magnetizationAlongExhaustion_continuous_joint G Λ i n).continuousAt

/-- **Along-ex: susceptibility jointly ContinuousAt** (general G). -/
theorem susceptibilityAlongExhaustion_continuousAt_joint_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (i : V) (n : ℕ) (p : ℝ × ℝ × ℝ) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ =>
      susceptibilityAlongExhaustion G Λ ⟨q.2.1, q.2.2, q.1⟩ i n) p :=
  (susceptibilityAlongExhaustion_continuous_joint_gen G Λ i n).continuousAt

end Ambient
end IsingModel

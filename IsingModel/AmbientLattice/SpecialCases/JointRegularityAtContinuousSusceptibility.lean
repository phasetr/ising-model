import IsingModel.AmbientLattice.SpecialCases.JointRegularityContinuousSusceptibility

/-!
# Joint `ContinuousAt` susceptibility along-ex wrapper

Narrow child module for the pointwise susceptibility joint
`ContinuousAt` wrapper along an exhaustion extracted from
`JointRegularityAt.lean`:

* `susceptibilityAlongExhaustion_continuousAt_joint_gen`

The wrapper is a thin pass-through to
`susceptibilityAlongExhaustion_continuous_joint_gen` via the
`.continuousAt` projection. The theorem name is unchanged from the
former `JointRegularity` declaration.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

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

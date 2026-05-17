import IsingModel.AmbientLattice.SpecialCases.JointRegularityDifferentiableSusceptibility

/-!
# Joint `DifferentiableAt` susceptibility along-ex wrapper

Narrow child module for the pointwise susceptibility joint
`DifferentiableAt` wrapper along an exhaustion extracted from
`JointRegularityAtDifferentiableAt.lean`:

* `susceptibilityAlongExhaustion_differentiableAt_joint_gen`

The wrapper is a thin pass-through to
`susceptibilityAlongExhaustion_differentiable_joint_gen` via the
`.differentiableAt` projection. The theorem name is unchanged from
the former `JointRegularity` declaration.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: susceptibility jointly DifferentiableAt** (general G). -/
theorem susceptibilityAlongExhaustion_differentiableAt_joint_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (i : V) (n : ℕ) (p : ℝ × ℝ × ℝ) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ × ℝ =>
      susceptibilityAlongExhaustion G Λ ⟨q.2.1, q.2.2, q.1⟩ i n) p :=
  (susceptibilityAlongExhaustion_differentiable_joint_gen G Λ i n).differentiableAt

end Ambient
end IsingModel

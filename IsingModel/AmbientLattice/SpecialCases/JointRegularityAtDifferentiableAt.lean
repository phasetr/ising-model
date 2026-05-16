import IsingModel.AmbientLattice.SpecialCases.JointRegularity

/-!
# Joint `DifferentiableAt` along-ex wrappers

Narrow child module for the three pointwise joint `DifferentiableAt`
wrappers along an exhaustion (correlation, magnetization,
susceptibility) extracted from `JointRegularityAt.lean`:

* `correlationAlongExhaustion_differentiableAt_joint_gen`
* `magnetizationAlongExhaustion_differentiableAt_joint`
* `susceptibilityAlongExhaustion_differentiableAt_joint_gen`

Each wrapper is a thin pass-through to the corresponding
`*_differentiable_joint*` parent lemma via the `.differentiableAt`
projection. Theorem names are unchanged from the former
`JointRegularity` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: correlation jointly DifferentiableAt** (general G). -/
theorem correlationAlongExhaustion_differentiableAt_joint_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (A : Finset V) (n : ℕ) (p : ℝ × ℝ × ℝ) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ × ℝ =>
      correlationAlongExhaustion G Λ ⟨q.2.1, q.2.2, q.1⟩ A n) p :=
  (correlationAlongExhaustion_differentiable_joint_gen G Λ A n).differentiableAt

/-- **Along-ex: magnetization jointly DifferentiableAt** (general G). -/
theorem magnetizationAlongExhaustion_differentiableAt_joint
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (i : V) (n : ℕ) (p : ℝ × ℝ × ℝ) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ × ℝ =>
      magnetizationAlongExhaustion G Λ ⟨q.2.1, q.2.2, q.1⟩ i n) p :=
  (magnetizationAlongExhaustion_differentiable_joint G Λ i n).differentiableAt

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

import IsingModel.AmbientLattice.SpecialCases.JointRegularity

/-!
# Joint `ContinuousAt` / `DifferentiableAt` along-ex wrappers

Narrow child module for the six pointwise joint `ContinuousAt` /
`DifferentiableAt` wrappers along an exhaustion (correlation,
magnetization, susceptibility), obtained from the corresponding
`_continuous_joint*` / `_differentiable_joint*` wrappers in the
parent `JointRegularity` module via the `.continuousAt` /
`.differentiableAt` projections. Theorem names are unchanged from
the former `JointRegularity` declarations.
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

/-- **Along-ex: correlation jointly DifferentiableAt** (general G). -/
theorem correlationAlongExhaustion_differentiableAt_joint_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (A : Finset V) (n : ℕ) (p : ℝ × ℝ × ℝ) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ × ℝ =>
      correlationAlongExhaustion G Λ ⟨q.2.1, q.2.2, q.1⟩ A n) p :=
  (correlationAlongExhaustion_differentiable_joint_gen G Λ A n).differentiableAt

/-- **Along-ex: magnetization jointly ContinuousAt** (general G). -/
theorem magnetizationAlongExhaustion_continuousAt_joint
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (i : V) (n : ℕ) (p : ℝ × ℝ × ℝ) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ =>
      magnetizationAlongExhaustion G Λ ⟨q.2.1, q.2.2, q.1⟩ i n) p :=
  (magnetizationAlongExhaustion_continuous_joint G Λ i n).continuousAt

/-- **Along-ex: magnetization jointly DifferentiableAt** (general G). -/
theorem magnetizationAlongExhaustion_differentiableAt_joint
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (i : V) (n : ℕ) (p : ℝ × ℝ × ℝ) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ × ℝ =>
      magnetizationAlongExhaustion G Λ ⟨q.2.1, q.2.2, q.1⟩ i n) p :=
  (magnetizationAlongExhaustion_differentiable_joint G Λ i n).differentiableAt

/-- **Along-ex: susceptibility jointly ContinuousAt** (general G). -/
theorem susceptibilityAlongExhaustion_continuousAt_joint_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (i : V) (n : ℕ) (p : ℝ × ℝ × ℝ) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ =>
      susceptibilityAlongExhaustion G Λ ⟨q.2.1, q.2.2, q.1⟩ i n) p :=
  (susceptibilityAlongExhaustion_continuous_joint_gen G Λ i n).continuousAt

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

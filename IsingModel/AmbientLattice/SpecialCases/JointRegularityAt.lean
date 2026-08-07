import IsingModel.AmbientLattice.SpecialCases.JointRegularity
import IsingModel.AmbientLattice.SpecialCases.JointRegularityAtDifferentiableAt
import IsingModel.AmbientLattice.SpecialCases.JointRegularityAtContinuousSusceptibility

/-!
# Joint `ContinuousAt` along-ex wrappers

Turns the joint (all-parameter) continuity of the along-exhaustion observables into pointwise
`ContinuousAt` form via the `.continuousAt` projection, which is what the differentiability
and analyticity arguments of GJ §17.5–§17.6 take as input.
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

/-- **Along-ex: magnetization jointly ContinuousAt** (general G). -/
theorem magnetizationAlongExhaustion_continuousAt_joint
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (i : V) (n : ℕ) (p : ℝ × ℝ × ℝ) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ =>
      magnetizationAlongExhaustion G Λ ⟨q.2.1, q.2.2, q.1⟩ i n) p :=
  (magnetizationAlongExhaustion_continuous_joint G Λ i n).continuousAt

end Ambient
end IsingModel

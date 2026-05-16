import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.MagnetizationAlongExhaustion
import IsingModel.AmbientLattice.SpecialCases.JointRegularityDifferentiable

/-!
# Ambient joint regularity wrappers

This module contains general-graph joint `Continuous`, `Differentiable`,
`ContinuousAt`, and `DifferentiableAt` APIs for along-exhaustion correlation,
magnetization, and susceptibility. It is split out of the legacy ambient
special-cases module so concrete joint wrappers can depend on a narrower child
path.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### Along-exhaustion joint regularity wrappers -/

/-- **Along-ex: correlation jointly Continuous in `(β, J, h)`** (general G). -/
theorem correlationAlongExhaustion_continuous_joint_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (A : Finset V) (n : ℕ) :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      correlationAlongExhaustion G Λ ⟨p.2.1, p.2.2, p.1⟩ A n) := by
  unfold correlationAlongExhaustion
  by_cases hA : A ⊆ Λ.volume n
  · simp only [hA, dif_pos]
    exact correlationΛ_continuous_joint G (Λ.volume n) (liftFinset A hA)
  · simp only [hA, dif_neg, not_false_iff]
    exact continuous_const

/-- **Along-ex: magnetization jointly Continuous in `(β, J, h)`** (general G). -/
theorem magnetizationAlongExhaustion_continuous_joint
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (i : V) (n : ℕ) :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      magnetizationAlongExhaustion G Λ ⟨p.2.1, p.2.2, p.1⟩ i n) := by
  unfold magnetizationAlongExhaustion correlationAlongExhaustion
  by_cases hi : ({i} : Finset V) ⊆ Λ.volume n
  · simp only [hi, dif_pos]
    exact correlationΛ_continuous_joint G (Λ.volume n) (liftFinset {i} hi)
  · simp only [hi, dif_neg, not_false_iff]
    exact continuous_const

/-- **Along-ex: susceptibility jointly Continuous in `(β, J, h)`** (general G). -/
theorem susceptibilityAlongExhaustion_continuous_joint_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (i : V) (n : ℕ) :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      susceptibilityAlongExhaustion G Λ ⟨p.2.1, p.2.2, p.1⟩ i n) := by
  unfold susceptibilityAlongExhaustion
  by_cases hi : i ∈ Λ.volume n
  · simp only [hi, dif_pos]
    exact susceptibilityΛ_continuous_joint G (Λ.volume n) ⟨i, hi⟩
  · simp only [hi, dif_neg, not_false_iff]
    exact continuous_const

/-! ## Moved: joint Differentiable along-ex wrappers

The three joint `_differentiable_joint*` wrappers (correlation,
magnetization, susceptibility) now live in
`IsingModel.AmbientLattice.SpecialCases.JointRegularityDifferentiable`.
The legacy import path is preserved by re-exporting the new child
from this parent module and from `Legacy.lean`.
-/

/-! ## Moved: joint ContinuousAt / DifferentiableAt along-ex wrappers

The six joint `_continuousAt_joint*` / `_differentiableAt_joint*`
wrappers for correlation, magnetization, and susceptibility now live
in `IsingModel.AmbientLattice.SpecialCases.JointRegularityAt`. The
legacy import path is preserved by re-exporting the new child from
`Legacy.lean` and from each downstream consumer that previously
imported only this parent.
-/

end Ambient
end IsingModel

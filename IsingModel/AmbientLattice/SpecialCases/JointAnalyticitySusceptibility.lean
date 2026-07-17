import IsingModel.AmbientLattice.MagnetizationAlongExhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaMagSuscep

/-!
# Joint analyticity wrappers along an exhaustion (susceptibility)

Narrow child module for the two ambient
`susceptibilityAlongExhaustion_*_joint_gen` general-graph
joint-`(β, J, h)` analyticity wrappers extracted from
`JointAnalyticity.lean`:

* `susceptibilityAlongExhaustion_analyticAt_joint_gen`
* `susceptibilityAlongExhaustion_analyticOnNhd_joint_gen`

The pointwise `AnalyticAt` wrapper unfolds
`susceptibilityAlongExhaustion` and dispatches on `i ∈ Λ.volume n`,
falling back to the constant analytic case when the index is
outside the exhaustion. The `AnalyticOnNhd` wrapper is a thin
specialization to `Set.univ`. Theorem names are unchanged from the
former `JointAnalyticity` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: susceptibility jointly AnalyticAt** (general G). -/
theorem susceptibilityAlongExhaustion_analyticAt_joint_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (i : V) (n : ℕ) (β J h : ℝ) :
    AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ =>
      susceptibilityAlongExhaustion G Λ ⟨p.2.1, p.2.2, p.1⟩ i n) (β, J, h) := by
  unfold susceptibilityAlongExhaustion
  by_cases hi : i ∈ Λ.volume n
  · simp only [hi, dif_pos]
    exact susceptibilityΛ_analyticAt_joint G (Λ.volume n) ⟨i, hi⟩ β J h
  · simp only [hi, dif_neg, not_false_iff]
    exact analyticAt_const

/-- **Along-ex: susceptibility jointly AnalyticOnNhd over Set.univ** (general G). -/
theorem susceptibilityAlongExhaustion_analyticOnNhd_joint_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (i : V) (n : ℕ) :
    AnalyticOnNhd ℝ (fun p : ℝ × ℝ × ℝ =>
      susceptibilityAlongExhaustion G Λ ⟨p.2.1, p.2.2, p.1⟩ i n) Set.univ :=
  fun ⟨β, J, h⟩ _ => susceptibilityAlongExhaustion_analyticAt_joint_gen G Λ i n β J h

end Ambient
end IsingModel

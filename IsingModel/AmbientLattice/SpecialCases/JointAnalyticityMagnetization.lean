import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaJoint

/-!
# Joint analyticity wrappers along an exhaustion (magnetization)

Narrow child module for the two ambient
`magnetizationAlongExhaustion_*_joint` general-graph joint-`(β, J, h)`
analyticity wrappers extracted from `JointAnalyticity.lean`:

* `magnetizationAlongExhaustion_analyticAt_joint`
* `magnetizationAlongExhaustion_analyticOnNhd_joint`

The pointwise `AnalyticAt` wrapper unfolds
`magnetizationAlongExhaustion` (which factors through
`correlationAlongExhaustion` at the singleton `{i}`) and dispatches
on `{i} ⊆ Λ.volume n`, falling back to the constant analytic case
when the singleton lies outside the exhaustion. The `AnalyticOnNhd`
wrapper is a thin specialization to `Set.univ`. Theorem names are
unchanged from the former `JointAnalyticity` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: magnetization jointly AnalyticAt** (general G). -/
theorem magnetizationAlongExhaustion_analyticAt_joint
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (i : V) (n : ℕ) (β J h : ℝ) :
    AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ =>
      magnetizationAlongExhaustion G Λ ⟨p.2.1, p.2.2, p.1⟩ i n) (β, J, h) := by
  unfold magnetizationAlongExhaustion correlationAlongExhaustion
  by_cases hi : ({i} : Finset V) ⊆ Λ.volume n
  · simp only [hi, dif_pos]
    exact correlationΛ_analyticAt_joint G (Λ.volume n) (liftFinset {i} hi) β J h
  · simp only [hi, dif_neg, not_false_iff]
    exact analyticAt_const

/-- **Along-ex: magnetization jointly AnalyticOnNhd over Set.univ** (general G). -/
theorem magnetizationAlongExhaustion_analyticOnNhd_joint
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (i : V) (n : ℕ) :
    AnalyticOnNhd ℝ (fun p : ℝ × ℝ × ℝ =>
      magnetizationAlongExhaustion G Λ ⟨p.2.1, p.2.2, p.1⟩ i n) Set.univ :=
  fun ⟨β, J, h⟩ _ => magnetizationAlongExhaustion_analyticAt_joint G Λ i n β J h

end Ambient
end IsingModel

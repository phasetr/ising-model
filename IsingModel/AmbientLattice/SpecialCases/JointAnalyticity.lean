import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.MagnetizationAlongExhaustion
import IsingModel.AmbientLattice.SpecialCases.JointAnalyticityMagnetization
import IsingModel.AmbientLattice.SpecialCases.JointAnalyticityPartitionFreeEnergy
import IsingModel.AmbientLattice.SpecialCases.JointAnalyticitySusceptibility

/-!
# Joint analyticity wrappers along an exhaustion

Narrow child module for general-graph `AnalyticAt` / `AnalyticOnNhd` wrappers
in the joint `(β, J, h)` parameters. This keeps callers that only need these
along-exhaustion forwarders out of the monolithic original special-cases module.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### Joint AnalyticAt + AnalyticOnNhd along-ex wrappers
(general G), for correlation, magnetization, susceptibility -/

/-- **Along-ex: correlation jointly AnalyticAt in `(β, J, h)`** (general G). -/
theorem correlationAlongExhaustion_analyticAt_joint_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (A : Finset V) (n : ℕ) (β J h : ℝ) :
    AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ =>
      correlationAlongExhaustion G Λ ⟨p.2.1, p.2.2, p.1⟩ A n) (β, J, h) := by
  unfold correlationAlongExhaustion
  by_cases hA : A ⊆ Λ.volume n
  · simp only [hA, dif_pos]
    exact correlationΛ_analyticAt_joint G (Λ.volume n) (liftFinset A hA) β J h
  · simp only [hA, dif_neg, not_false_iff]
    exact analyticAt_const

/-- **Along-ex: correlation jointly AnalyticOnNhd over Set.univ** (general G). -/
theorem correlationAlongExhaustion_analyticOnNhd_joint_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (A : Finset V) (n : ℕ) :
    AnalyticOnNhd ℝ (fun p : ℝ × ℝ × ℝ =>
      correlationAlongExhaustion G Λ ⟨p.2.1, p.2.2, p.1⟩ A n) Set.univ :=
  fun ⟨β, J, h⟩ _ => correlationAlongExhaustion_analyticAt_joint_gen G Λ A n β J h

/-! ## Moved: 2 magnetizationAlongExhaustion joint analyticity wrappers

The two `magnetizationAlongExhaustion_*_joint` general-graph
joint-`(β, J, h)` analyticity wrappers
(`magnetizationAlongExhaustion_analyticAt_joint`,
`magnetizationAlongExhaustion_analyticOnNhd_joint`) now live in
`IsingModel.AmbientLattice.SpecialCases.JointAnalyticityMagnetization`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

/-! ## Moved: 2 susceptibilityAlongExhaustion joint analyticity wrappers

The two `susceptibilityAlongExhaustion_*_joint_gen` general-graph
joint-`(β, J, h)` analyticity wrappers
(`susceptibilityAlongExhaustion_analyticAt_joint_gen`,
`susceptibilityAlongExhaustion_analyticOnNhd_joint_gen`) now live in
`IsingModel.AmbientLattice.SpecialCases.JointAnalyticitySusceptibility`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

/-! ## Moved: partitionFunction + freeEnergy joint analyticity wrappers

The four `{partitionFunction,freeEnergy}AlongExhaustion_analytic{At,OnNhd}_joint`
wrappers now live in `JointAnalyticityPartitionFreeEnergy.lean`. They
are re-imported here so downstream consumers continue to see the symbols. -/



end Ambient
end IsingModel

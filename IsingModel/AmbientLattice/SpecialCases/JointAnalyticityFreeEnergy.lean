import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaJoint

/-!
# Ambient joint analyticity freeEnergy wrappers

Narrow child module for the two ambient
`freeEnergyAlongExhaustion_analytic{At,OnNhd}_joint` wrappers
extracted from `JointAnalyticityPartitionFreeEnergy.lean`:

* `freeEnergyAlongExhaustion_analyticAt_joint`
* `freeEnergyAlongExhaustion_analyticOnNhd_joint`

Each result is a thin pass-through of the corresponding Λ-level
`freeEnergyΛ_analytic*_joint` lemma. The theorem names are
unchanged from the former `JointAnalyticity` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: freeEnergy jointly AnalyticAt**. -/
theorem freeEnergyAlongExhaustion_analyticAt_joint
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (n : ℕ) (β J h : ℝ) :
    AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨p.2.1, p.2.2, p.1⟩ n) (β, J, h) :=
  freeEnergyΛ_analyticAt_joint G (Λ.volume n) β J h

/-- **Along-ex: freeEnergy jointly AnalyticOnNhd over Set.univ**. -/
theorem freeEnergyAlongExhaustion_analyticOnNhd_joint
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (n : ℕ) :
    AnalyticOnNhd ℝ (fun p : ℝ × ℝ × ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨p.2.1, p.2.2, p.1⟩ n) Set.univ :=
  freeEnergyΛ_analyticOnNhd_joint G (Λ.volume n)

end Ambient
end IsingModel

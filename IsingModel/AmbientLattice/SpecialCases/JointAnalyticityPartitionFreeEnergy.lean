import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.MagnetizationAlongExhaustion
import IsingModel.AmbientLattice.SpecialCases.JointAnalyticityFreeEnergy

/-!
# Ambient joint analyticity partitionFunction wrappers

Narrow child module for the two ambient
`partitionFunctionAlongExhaustion_analytic{At,OnNhd}_joint`
wrappers extracted from `JointAnalyticity.lean`:

* `partitionFunctionAlongExhaustion_analyticAt_joint`,
* `partitionFunctionAlongExhaustion_analyticOnNhd_joint`.

The corresponding two freeEnergy joint-analyticity wrappers now
live in
`IsingModel.AmbientLattice.SpecialCases.JointAnalyticityFreeEnergy`
and are re-imported through this parent module. Each result is a
thin pass-through of the corresponding Λ-level
`{partitionFunction,freeEnergy}Λ_analytic*_joint` lemma. The
theorem names are unchanged from the former `JointAnalyticity`
declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]


/-- **Along-ex: partitionFunction jointly AnalyticAt**. -/
theorem partitionFunctionAlongExhaustion_analyticAt_joint
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (n : ℕ) (β J h : ℝ) :
    AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨p.2.1, p.2.2, p.1⟩ n) (β, J, h) :=
  partitionFunctionΛ_analyticAt_joint G (Λ.volume n) β J h

/-- **Along-ex: partitionFunction jointly AnalyticOnNhd over Set.univ**. -/
theorem partitionFunctionAlongExhaustion_analyticOnNhd_joint
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (n : ℕ) :
    AnalyticOnNhd ℝ (fun p : ℝ × ℝ × ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨p.2.1, p.2.2, p.1⟩ n) Set.univ :=
  partitionFunctionΛ_analyticOnNhd_joint G (Λ.volume n)

/-! ## Moved: 2 freeEnergy joint-analyticity wrappers

The two `freeEnergyAlongExhaustion_analytic{At,OnNhd}_joint`
wrappers now live in
`IsingModel.AmbientLattice.SpecialCases.JointAnalyticityFreeEnergy`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

end Ambient
end IsingModel

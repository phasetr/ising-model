import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.MagnetizationAlongExhaustion

/-!
# Ambient joint analyticity partitionFunction + freeEnergy wrappers

Narrow child module for 4 ambient
`{partitionFunction,freeEnergy}AlongExhaustion_analytic{At,OnNhd}_joint`
wrappers extracted from `JointAnalyticity.lean`:

* `partitionFunctionAlongExhaustion_analyticAt_joint`,
* `partitionFunctionAlongExhaustion_analyticOnNhd_joint`,
* `freeEnergyAlongExhaustion_analyticAt_joint`,
* `freeEnergyAlongExhaustion_analyticOnNhd_joint`.

Each result is a thin pass-through of the corresponding Λ-level
`{partitionFunction,freeEnergy}Λ_analytic*_joint` lemma. The theorem
names are unchanged from the former `JointAnalyticity` declarations.
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

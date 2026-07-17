import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaSection186

/-!
# Ambient partitionFunctionAlongExhaustion h=0 `AnalyticOnNhd` wrappers

Narrow child module for the two ambient
`partitionFunctionAlongExhaustion_analyticOnNhd_*_h_zero` wrappers
extracted from `PartitionFunctionRegularityAnalytic.lean`:

* `partitionFunctionAlongExhaustion_analyticOnNhd_beta_h_zero`
* `partitionFunctionAlongExhaustion_analyticOnNhd_J_h_zero`

Each result is a thin pass-through of the corresponding Λ-level
`partitionFunctionΛ_analyticOnNhd_*_h_zero` lemma. Theorem names
are unchanged from the former `PartitionFunctionRegularity`
declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: partitionFunction `AnalyticOnNhd ℝ _ Set.univ` in `β`
at `h = 0`**. -/
theorem partitionFunctionAlongExhaustion_analyticOnNhd_beta_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun β' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J, 0, β'⟩ n) Set.univ :=
  partitionFunctionΛ_analyticOnNhd_beta_h_zero G (Λ.volume n) J

/-- **Along-ex: partitionFunction `AnalyticOnNhd ℝ _ Set.univ` in `J`
at `h = 0`**. -/
theorem partitionFunctionAlongExhaustion_analyticOnNhd_J_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun J' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J', 0, β⟩ n) Set.univ :=
  partitionFunctionΛ_analyticOnNhd_J_h_zero G (Λ.volume n) β

end Ambient
end IsingModel

import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion

/-!
# Ambient partitionFunctionAlongExhaustion h=0 analyticity wrappers

Narrow child module for 4 ambient
`partitionFunctionAlongExhaustion_analytic*_*_h_zero` wrappers
extracted from `PartitionFunctionRegularity.lean`:

* `partitionFunctionAlongExhaustion_analyticAt_beta_h_zero`,
* `partitionFunctionAlongExhaustion_analyticAt_J_h_zero`,
* `partitionFunctionAlongExhaustion_analyticOnNhd_beta_h_zero`,
* `partitionFunctionAlongExhaustion_analyticOnNhd_J_h_zero`.

Each result is a thin pass-through of the corresponding Λ-level
`partitionFunctionΛ_analytic*_*_h_zero` lemma. The theorem names are
unchanged from the former `PartitionFunctionRegularity` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]


/-- **Along-ex: partitionFunction `AnalyticAt ℝ` in `β` at `h = 0`**. -/
theorem partitionFunctionAlongExhaustion_analyticAt_beta_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun β' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J, 0, β'⟩ n) β :=
  partitionFunctionΛ_analyticAt_beta_h_zero G (Λ.volume n) J β

/-- **Along-ex: partitionFunction `AnalyticAt ℝ` in `J` at `h = 0`**. -/
theorem partitionFunctionAlongExhaustion_analyticAt_J_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β J : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun J' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J', 0, β⟩ n) J :=
  partitionFunctionΛ_analyticAt_J_h_zero G (Λ.volume n) β J

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

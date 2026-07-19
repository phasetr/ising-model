import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion

/-!
# Ambient partition-function regularity wrappers

This module contains general-graph `Continuous`, `Differentiable`,
`AnalyticAt`, and `AnalyticOnNhd` APIs for per-stage
`partitionFunctionAlongExhaustion` at zero external field. It is split out of
the original ambient special-cases module so concrete partition-function
regularity wrappers can depend on a narrower child path.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### Along-exhaustion partition-function regularity at `h = 0` -/

/-- **Along-ex: partitionFunction Continuous in `β` at `h = 0`,
per stage `n`**. -/
theorem partitionFunctionAlongExhaustion_continuous_beta_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) (n : ℕ) :
    Continuous (fun β : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J, 0, β⟩ n) :=
  partitionFunctionΛ_continuous_beta_h_zero G (Λ.volume n) J

/-- **Along-ex: partitionFunction Continuous in `J` at `h = 0`**. -/
theorem partitionFunctionAlongExhaustion_continuous_J_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (n : ℕ) :
    Continuous (fun J : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J, 0, β⟩ n) :=
  partitionFunctionΛ_continuous_J_h_zero G (Λ.volume n) β

/-- **Along-ex: partitionFunction Differentiable in `β` at `h = 0`**. -/
theorem partitionFunctionAlongExhaustion_differentiable_beta_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) (n : ℕ) :
    Differentiable ℝ (fun β : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J, 0, β⟩ n) :=
  partitionFunctionΛ_differentiable_beta_h_zero G (Λ.volume n) J

/-- **Along-ex: partitionFunction Differentiable in `J` at `h = 0`**. -/
theorem partitionFunctionAlongExhaustion_differentiable_J_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (n : ℕ) :
    Differentiable ℝ (fun J : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J, 0, β⟩ n) :=
  partitionFunctionΛ_differentiable_J_h_zero G (Λ.volume n) β

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

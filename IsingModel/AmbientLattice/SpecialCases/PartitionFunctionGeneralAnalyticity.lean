import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion

/-!
# Ambient partition-function joint and general-h analyticity wrappers

This module contains general-graph joint `Continuous` / `Differentiable` APIs
and general-h `AnalyticAt` APIs for per-stage
`partitionFunctionAlongExhaustion`.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### Along-exhaustion partition-function joint and general-h analyticity -/

/-- **Along-ex: partitionFunction jointly `Continuous` in
`(β, J, h)`**. -/
theorem partitionFunctionAlongExhaustion_continuous_joint
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      partitionFunctionAlongExhaustion G Λ
        ⟨p.2.1, p.2.2, p.1⟩ n) :=
  partitionFunctionΛ_continuous_joint G (Λ.volume n)

/-- **Along-ex: partitionFunction jointly `Differentiable ℝ` in
`(β, J, h)`**. -/
theorem partitionFunctionAlongExhaustion_differentiable_joint
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    Differentiable ℝ (fun p : ℝ × ℝ × ℝ =>
      partitionFunctionAlongExhaustion G Λ
        ⟨p.2.1, p.2.2, p.1⟩ n) :=
  partitionFunctionΛ_differentiable_joint G (Λ.volume n)

/-- **Along-ex: partitionFunction `AnalyticAt ℝ` in `β` at general
`h`**. -/
theorem partitionFunctionAlongExhaustion_analyticAt_beta_general_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun β' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J, h, β'⟩ n) β :=
  partitionFunctionΛ_analyticAt_beta_general_h G (Λ.volume n) J h β

/-- **Along-ex: partitionFunction `AnalyticAt ℝ` in `J` at general
`h`**. -/
theorem partitionFunctionAlongExhaustion_analyticAt_J_general_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β h J : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun J' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J', h, β⟩ n) J :=
  partitionFunctionΛ_analyticAt_J_general_h G (Λ.volume n) β h J

/-- **Along-ex: partitionFunction `AnalyticAt ℝ` in `h`**. -/
theorem partitionFunctionAlongExhaustion_analyticAt_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β h : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun h' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J, h', β⟩ n) h :=
  partitionFunctionΛ_analyticAt_h G (Λ.volume n) J β h

end Ambient
end IsingModel

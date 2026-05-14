import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion

/-!
# Ambient partitionFunctionAlongExhaustion general-h pointwise wrappers

Narrow child module for 4 ambient
`partitionFunctionAlongExhaustion_*_general_h` ContinuousAt /
DifferentiableAt pointwise wrappers extracted from
`PartitionFreeEnergyPointwiseRegularity.lean`:

* `partitionFunctionAlongExhaustion_continuousAt_beta_general_h`,
* `partitionFunctionAlongExhaustion_continuousAt_J_general_h`,
* `partitionFunctionAlongExhaustion_differentiableAt_beta_general_h`,
* `partitionFunctionAlongExhaustion_differentiableAt_J_general_h`.

Each result is a thin pass-through lifting the corresponding Λ-level
`partitionFunctionΛ_{continuous,differentiable}_{beta,J}_general_h`
lemma to AlongExhaustion via `.continuousAt` / `.differentiableAt`.
The theorem names are unchanged from the former
`PartitionFreeEnergyPointwiseRegularity` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]


/-- **partitionFunctionAlongExhaustion ContinuousAt β at general h**. -/
theorem partitionFunctionAlongExhaustion_continuousAt_beta_general_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    ContinuousAt (fun β' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J, h, β'⟩ n) β :=
  (partitionFunctionΛ_continuous_beta_general_h G (Λ.volume n) J h).continuousAt

/-- **partitionFunctionAlongExhaustion ContinuousAt J at general h**. -/
theorem partitionFunctionAlongExhaustion_continuousAt_J_general_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    ContinuousAt (fun J' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J', h, β⟩ n) J :=
  (partitionFunctionΛ_continuous_J_general_h G (Λ.volume n) β h).continuousAt

/-- **partitionFunctionAlongExhaustion DifferentiableAt β at general h**. -/
theorem partitionFunctionAlongExhaustion_differentiableAt_beta_general_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    DifferentiableAt ℝ (fun β' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J, h, β'⟩ n) β :=
  (partitionFunctionΛ_differentiable_beta_general_h G (Λ.volume n) J h).differentiableAt

/-- **partitionFunctionAlongExhaustion DifferentiableAt J at general h**. -/
theorem partitionFunctionAlongExhaustion_differentiableAt_J_general_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    DifferentiableAt ℝ (fun J' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J', h, β⟩ n) J :=
  (partitionFunctionΛ_differentiable_J_general_h G (Λ.volume n) β h).differentiableAt

end Ambient
end IsingModel

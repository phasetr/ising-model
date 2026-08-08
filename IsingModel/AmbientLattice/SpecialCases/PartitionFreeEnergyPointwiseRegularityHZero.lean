import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyPointwiseRegularityHZeroDifferentiableAt

/-!
# Ambient partitionFunctionAlongExhaustion h = 0 pointwise `ContinuousAt` wrappers

Gives pointwise continuity of the along-exhaustion partition function on the zero-field
slice, where the §18.3 expansion applies. Each result lifts the matching Λ-level
`partitionFunctionΛ_continuous_*_h_zero` lemma via `.continuousAt`.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]


/-- **partitionFunctionAlongExhaustion ContinuousAt β at h = 0**. -/
theorem partitionFunctionAlongExhaustion_continuousAt_beta_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    ContinuousAt (fun β' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J, 0, β'⟩ n) β :=
  (partitionFunctionΛ_continuous_beta_h_zero G (Λ.volume n) J).continuousAt

/-- **partitionFunctionAlongExhaustion ContinuousAt J at h = 0**. -/
theorem partitionFunctionAlongExhaustion_continuousAt_J_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    ContinuousAt (fun J' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J', 0, β⟩ n) J :=
  (partitionFunctionΛ_continuous_J_h_zero G (Λ.volume n) β).continuousAt

end Ambient
end IsingModel

import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyPointwiseRegularityPartitionGeneralHDifferentiableAt

/-!
# Ambient partitionFunctionAlongExhaustion general-h pointwise wrappers

Gives pointwise regularity of the along-exhaustion partition function at general external
field, the form needed where the zero-field restriction is unavailable. Each result lifts
the matching Λ-level `partitionFunctionΛ_*_general_h` lemma via
`.continuousAt` / `.differentiableAt`.
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

end Ambient
end IsingModel

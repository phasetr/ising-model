import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion

/-!
# Ambient `freeEnergyAlongExhaustion` non-joint pointwise wrappers

Narrow child module for six ambient
`freeEnergyAlongExhaustion_{continuousAt,differentiableAt}_{beta,field,J}`
non-joint pointwise wrappers extracted from
`PartitionFreeEnergyPointwiseRegularityFE.lean`. Each wrapper is a
thin pass-through to the corresponding `freeEnergyΛ_*` ambient
lemma via the `.continuousAt` / `.differentiableAt` projection.
Theorem names are unchanged from the former
`PartitionFreeEnergyPointwiseRegularity` / `PartitionFreeEnergyPointwiseRegularityFE`
declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### Along-exhaustion free-energy pointwise wrappers -/

/-- **freeEnergyAlongExhaustion ContinuousAt β** (general h). -/
theorem freeEnergyAlongExhaustion_continuousAt_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    ContinuousAt (fun β' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J, h, β'⟩ n) β :=
  (freeEnergyΛ_continuous_beta G (Λ.volume n) J h).continuousAt

/-- **freeEnergyAlongExhaustion DifferentiableAt β** (general h). -/
theorem freeEnergyAlongExhaustion_differentiableAt_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    DifferentiableAt ℝ (fun β' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J, h, β'⟩ n) β :=
  (freeEnergyΛ_differentiable_beta G (Λ.volume n) J h).differentiableAt

/-- **freeEnergyAlongExhaustion ContinuousAt h**. -/
theorem freeEnergyAlongExhaustion_continuousAt_field
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    ContinuousAt (fun h' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J, h', β⟩ n) h :=
  (freeEnergyΛ_continuous_field G (Λ.volume n) J β).continuousAt

/-- **freeEnergyAlongExhaustion DifferentiableAt h**. -/
theorem freeEnergyAlongExhaustion_differentiableAt_field
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    DifferentiableAt ℝ (fun h' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J, h', β⟩ n) h :=
  (freeEnergyΛ_differentiable_field G (Λ.volume n) J β).differentiableAt

/-- **freeEnergyAlongExhaustion ContinuousAt J**. -/
theorem freeEnergyAlongExhaustion_continuousAt_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    ContinuousAt (fun J' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J', h, β⟩ n) J :=
  (freeEnergyΛ_continuous_J G (Λ.volume n) h β).continuousAt

/-- **freeEnergyAlongExhaustion DifferentiableAt J**. -/
theorem freeEnergyAlongExhaustion_differentiableAt_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    DifferentiableAt ℝ (fun J' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J', h, β⟩ n) J :=
  (freeEnergyΛ_differentiable_J G (Λ.volume n) h β).differentiableAt

end Ambient
end IsingModel

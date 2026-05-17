import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyRegularityFEDifferentiableJoint

/-!
# Ambient freeEnergyAlongExhaustion `Differentiable` per-direction wrappers

Narrow child module for the three per-direction ambient
`freeEnergyAlongExhaustion_differentiable_*` regularity wrappers
extracted from `PartitionFreeEnergyRegularityFE.lean`:

* `freeEnergyAlongExhaustion_differentiable_beta`
* `freeEnergyAlongExhaustion_differentiable_field`
* `freeEnergyAlongExhaustion_differentiable_J`

The corresponding joint wrapper now lives in
`IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyRegularityFEDifferentiableJoint`
and is re-imported through this parent module. Each wrapper is a
thin pass-through of the corresponding Λ-level
`freeEnergyΛ_differentiable_*` lemma. Theorem names are unchanged
from the former `PartitionFreeEnergyRegularity` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ## Moved: 1 freeEnergyAlongExhaustion_differentiable_joint wrapper

The `freeEnergyAlongExhaustion_differentiable_joint` wrapper now
lives in
`IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyRegularityFEDifferentiableJoint`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

/-- **Along-ex: freeEnergy Differentiable in β** (general h). -/
theorem freeEnergyAlongExhaustion_differentiable_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (n : ℕ) :
    Differentiable ℝ (fun β' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J, h, β'⟩ n) :=
  freeEnergyΛ_differentiable_beta G (Λ.volume n) J h

/-- **Along-ex: freeEnergy Differentiable in h**. -/
theorem freeEnergyAlongExhaustion_differentiable_field
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    Differentiable ℝ (fun h' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J, h', β⟩ n) :=
  freeEnergyΛ_differentiable_field G (Λ.volume n) J β

/-- **Along-ex: freeEnergy Differentiable in J**. -/
theorem freeEnergyAlongExhaustion_differentiable_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ) (n : ℕ) :
    Differentiable ℝ (fun J' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J', h, β⟩ n) :=
  freeEnergyΛ_differentiable_J G (Λ.volume n) h β

end Ambient
end IsingModel

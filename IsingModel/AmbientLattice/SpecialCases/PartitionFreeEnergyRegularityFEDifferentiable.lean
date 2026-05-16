import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion

/-!
# Ambient freeEnergyAlongExhaustion `Differentiable` regularity wrappers

Narrow child module for the four ambient
`freeEnergyAlongExhaustion_differentiable_*` regularity wrappers
extracted from `PartitionFreeEnergyRegularityFE.lean`:

* `freeEnergyAlongExhaustion_differentiable_joint`
* `freeEnergyAlongExhaustion_differentiable_beta`
* `freeEnergyAlongExhaustion_differentiable_field`
* `freeEnergyAlongExhaustion_differentiable_J`

Each result is a thin pass-through of the corresponding Λ-level
`freeEnergyΛ_differentiable_*` lemma. Theorem names are unchanged
from the former `PartitionFreeEnergyRegularity` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: freeEnergy jointly Differentiable ℝ**. -/
theorem freeEnergyAlongExhaustion_differentiable_joint
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    Differentiable ℝ (fun p : ℝ × ℝ × ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨p.2.1, p.2.2, p.1⟩ n) :=
  freeEnergyΛ_differentiable_joint G (Λ.volume n)

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

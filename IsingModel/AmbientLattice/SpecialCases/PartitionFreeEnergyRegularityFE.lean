import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyRegularityFEDifferentiable

/-!
# Ambient freeEnergyAlongExhaustion `Continuous` regularity wrappers

Narrow child module for the four ambient
`freeEnergyAlongExhaustion_continuous_*` regularity wrappers
extracted from `PartitionFreeEnergyRegularity.lean`:

* `freeEnergyAlongExhaustion_continuous_joint`
* `freeEnergyAlongExhaustion_continuous_beta`
* `freeEnergyAlongExhaustion_continuous_field`
* `freeEnergyAlongExhaustion_continuous_J`

Each result is a thin pass-through of the corresponding Λ-level
`freeEnergyΛ_continuous_*` lemma. The theorem names are unchanged
from the former `PartitionFreeEnergyRegularity` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]


/-- **Along-ex: freeEnergy jointly Continuous**. -/
theorem freeEnergyAlongExhaustion_continuous_joint
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨p.2.1, p.2.2, p.1⟩ n) :=
  freeEnergyΛ_continuous_joint G (Λ.volume n)

/-! ## Moved: 4 freeEnergyAlongExhaustion_differentiable_* wrappers

The four `Differentiable ℝ` wrappers
(`freeEnergyAlongExhaustion_differentiable_joint`,
`freeEnergyAlongExhaustion_differentiable_beta`,
`freeEnergyAlongExhaustion_differentiable_field`,
`freeEnergyAlongExhaustion_differentiable_J`) now live in
`IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyRegularityFEDifferentiable`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

/-- **Along-ex: freeEnergy Continuous in β** (general h). -/
theorem freeEnergyAlongExhaustion_continuous_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (n : ℕ) :
    Continuous (fun β' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J, h, β'⟩ n) :=
  freeEnergyΛ_continuous_beta G (Λ.volume n) J h

/-- **Along-ex: freeEnergy Continuous in h**. -/
theorem freeEnergyAlongExhaustion_continuous_field
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    Continuous (fun h' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J, h', β⟩ n) :=
  freeEnergyΛ_continuous_field G (Λ.volume n) J β

/-- **Along-ex: freeEnergy Continuous in J**. -/
theorem freeEnergyAlongExhaustion_continuous_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ) (n : ℕ) :
    Continuous (fun J' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J', h, β⟩ n) :=
  freeEnergyΛ_continuous_J G (Λ.volume n) h β

end Ambient
end IsingModel

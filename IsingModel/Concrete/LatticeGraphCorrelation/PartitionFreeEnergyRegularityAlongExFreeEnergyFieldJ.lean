import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyRegularityFE

/-!
# ℤ^d along-ex freeEnergyAlongEx field/J regularity wrappers

Narrow child module for four ℤ^d
`freeEnergyAlongExhaustion_latticeGraph_*` field/J `Continuous` /
`Differentiable` regularity wrappers extracted from
`PartitionFreeEnergyRegularityAlongExFreeEnergy.lean`:

* `freeEnergyAlongExhaustion_latticeGraph_continuous_field`,
* `freeEnergyAlongExhaustion_latticeGraph_differentiable_field`,
* `freeEnergyAlongExhaustion_latticeGraph_continuous_J`,
* `freeEnergyAlongExhaustion_latticeGraph_differentiable_J`.

Each result is a thin pass-through of the ambient
`Ambient.freeEnergyAlongExhaustion_*` lemma at
`G := IsingModel.latticeGraph d`. The theorem names are unchanged
from the former `PartitionFreeEnergyRegularityAlongExFreeEnergy`
declarations.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: `freeEnergyAlongExhaustion` Continuous in h**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_continuous_field
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    Continuous (fun h' : ℝ =>
      Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        Λ (⟨J, h', β⟩ : IsingParams ℝ) n) :=
  Ambient.freeEnergyAlongExhaustion_continuous_field
    (IsingModel.latticeGraph d) Λ J β n

/-- **ℤ^d along-ex: `freeEnergyAlongExhaustion` Differentiable in h**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_differentiable_field
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    Differentiable ℝ (fun h' : ℝ =>
      Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        Λ (⟨J, h', β⟩ : IsingParams ℝ) n) :=
  Ambient.freeEnergyAlongExhaustion_differentiable_field
    (IsingModel.latticeGraph d) Λ J β n

/-- **ℤ^d along-ex: `freeEnergyAlongExhaustion` Continuous in J**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_continuous_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (h β : ℝ) (n : ℕ) :
    Continuous (fun J' : ℝ =>
      Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        Λ (⟨J', h, β⟩ : IsingParams ℝ) n) :=
  Ambient.freeEnergyAlongExhaustion_continuous_J
    (IsingModel.latticeGraph d) Λ h β n

/-- **ℤ^d along-ex: `freeEnergyAlongExhaustion` Differentiable in J**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_differentiable_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (h β : ℝ) (n : ℕ) :
    Differentiable ℝ (fun J' : ℝ =>
      Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        Λ (⟨J', h, β⟩ : IsingParams ℝ) n) :=
  Ambient.freeEnergyAlongExhaustion_differentiable_J
    (IsingModel.latticeGraph d) Λ h β n

end Ambient
end IsingModel

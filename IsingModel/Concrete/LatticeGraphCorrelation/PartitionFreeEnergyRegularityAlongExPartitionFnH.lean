import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyRegularityDifferentiableH
import IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyRegularityH

/-!
# Concrete along-ex partitionFunction h-direction regularity wrappers

Narrow child module for 2 ℤ^d along-exhaustion
`partitionFunctionAlongExhaustion_latticeGraph_*_h` regularity
wrappers extracted from `PartitionFreeEnergyRegularityAlongExPartitionFn.lean`:

* `partitionFunctionAlongExhaustion_latticeGraph_continuous_h`,
* `partitionFunctionAlongExhaustion_latticeGraph_differentiable_h`.

Each result is a thin pass-through of the corresponding ambient
`Ambient.partitionFunctionAlongExhaustion_{continuous,differentiable}_h`
lemma at `G := IsingModel.latticeGraph d`. The theorem names are
unchanged from the former `PartitionFreeEnergyRegularityAlongExPartitionFn`
declarations.
-/

namespace IsingModel
namespace Ambient


/-- **ℤ^d along-ex: partitionFunction Continuous in `h`**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_continuous_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (J β : ℝ) (n : ℕ) :
    Continuous (fun h' : ℝ =>
      Ambient.partitionFunctionAlongExhaustion
        (IsingModel.latticeGraph d) Λ ⟨J, h', β⟩ n) :=
  Ambient.partitionFunctionAlongExhaustion_continuous_h
    (IsingModel.latticeGraph d) Λ J β n

/-- **ℤ^d along-ex: partitionFunction Differentiable in `h`**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_differentiable_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (J β : ℝ) (n : ℕ) :
    Differentiable ℝ (fun h' : ℝ =>
      Ambient.partitionFunctionAlongExhaustion
        (IsingModel.latticeGraph d) Λ ⟨J, h', β⟩ n) :=
  Ambient.partitionFunctionAlongExhaustion_differentiable_h
    (IsingModel.latticeGraph d) Λ J β n

end Ambient
end IsingModel

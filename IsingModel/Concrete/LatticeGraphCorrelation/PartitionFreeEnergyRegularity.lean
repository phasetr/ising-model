import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaJoint
import IsingModel.AmbientLattice.AnalyticityLambdaPerDirection

/-!
# Concrete partition/free-energy regularity wrappers

This module contains concrete `latticeGraph` specializations of `Continuous`
and `Differentiable` APIs for partition functions and free energies. It is
split out of the original concrete correlation module so downstream users can
depend on a narrower child path.
-/

namespace IsingModel
namespace Ambient

/-! ### ℤ^d partition/free-energy Continuous and Differentiable -/

/-! ## Moved: partitionFunctionΛ continuous/differentiable general-h

The four wrappers
`partitionFunctionΛ_latticeGraph_continuous_beta_general_h`,
`partitionFunctionΛ_latticeGraph_continuous_J_general_h`,
`partitionFunctionΛ_latticeGraph_differentiable_beta_general_h`,
`partitionFunctionΛ_latticeGraph_differentiable_J_general_h` now
live in `PartitionFreeEnergyRegularityGeneralH.lean`. -/


/-- **ℤ^d Λ: partitionFunction Continuous in `h`**. -/
theorem partitionFunctionΛ_latticeGraph_continuous_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J β : ℝ) :
    Continuous (fun h' : ℝ =>
      Ambient.partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        ⟨J, h', β⟩) :=
  Ambient.partitionFunctionΛ_continuous_h
    (IsingModel.latticeGraph d) Λ J β

/-- **ℤ^d Λ: partitionFunction Differentiable in `h`**. -/
theorem partitionFunctionΛ_latticeGraph_differentiable_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J β : ℝ) :
    Differentiable ℝ (fun h' : ℝ =>
      Ambient.partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        ⟨J, h', β⟩) :=
  Ambient.partitionFunctionΛ_differentiable_h
    (IsingModel.latticeGraph d) Λ J β

/-- **ℤ^d Λ: freeEnergy jointly Continuous**. -/
theorem freeEnergyΛ_latticeGraph_continuous_joint
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet] :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      Ambient.freeEnergyΛ (IsingModel.latticeGraph d) Λ
        ⟨p.2.1, p.2.2, p.1⟩) :=
  Ambient.freeEnergyΛ_continuous_joint
    (IsingModel.latticeGraph d) Λ

/-- **ℤ^d Λ: freeEnergy jointly Differentiable ℝ**. -/
theorem freeEnergyΛ_latticeGraph_differentiable_joint
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet] :
    Differentiable ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.freeEnergyΛ (IsingModel.latticeGraph d) Λ
        ⟨p.2.1, p.2.2, p.1⟩) :=
  Ambient.freeEnergyΛ_differentiable_joint
    (IsingModel.latticeGraph d) Λ

/-! ## Moved: partitionFunctionAlongExhaustion regularity wrappers

The six `partitionFunctionAlongExhaustion_latticeGraph_*`
`Continuous`/`Differentiable` regularity wrappers (in β, J, h at
general h) now live in
`PartitionFreeEnergyRegularityAlongExPartitionFn.lean`. -/


/-! ## Moved: freeEnergyAlongExhaustion regularity wrappers

The eight `freeEnergyAlongExhaustion_latticeGraph_*`
`Continuous`/`Differentiable` regularity wrappers (joint, beta, field,
J) now live in
`PartitionFreeEnergyRegularityAlongExFreeEnergy.lean`. -/

end Ambient
end IsingModel

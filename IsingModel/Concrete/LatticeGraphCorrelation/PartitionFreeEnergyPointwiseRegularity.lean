import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyPointwiseRegularityHZero

/-!
# Concrete partition/free-energy pointwise regularity wrappers

This module contains concrete `latticeGraph` specializations of ambient
`ContinuousAt` and `DifferentiableAt` APIs for along-exhaustion partition
function and free energy. It is split out of the original concrete correlation
module so downstream users can depend on a narrower child path.
-/

namespace IsingModel
namespace Ambient

/-! ### ℤ^d along-ex `partitionFunctionAlongExhaustion` /
`freeEnergyAlongExhaustion` pointwise wrappers -/

/-- **ℤ^d along-ex: `partitionFunctionAlongExhaustion` ContinuousAt β at h = 0**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_continuousAt_beta_h_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    ContinuousAt (fun β' : ℝ =>
      Ambient.partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J, 0, β'⟩ n) β :=
  Ambient.partitionFunctionAlongExhaustion_continuousAt_beta_h_zero
    (IsingModel.latticeGraph d) Λ J β n

/-- **ℤ^d along-ex: `partitionFunctionAlongExhaustion` ContinuousAt J at h = 0**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_continuousAt_J_h_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    ContinuousAt (fun J' : ℝ =>
      Ambient.partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J', 0, β⟩ n) J :=
  Ambient.partitionFunctionAlongExhaustion_continuousAt_J_h_zero
    (IsingModel.latticeGraph d) Λ J β n

/-- **ℤ^d along-ex: `partitionFunctionAlongExhaustion` DifferentiableAt β at h = 0**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_differentiableAt_beta_h_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    DifferentiableAt ℝ (fun β' : ℝ =>
      Ambient.partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J, 0, β'⟩ n) β :=
  Ambient.partitionFunctionAlongExhaustion_differentiableAt_beta_h_zero
    (IsingModel.latticeGraph d) Λ J β n

/-- **ℤ^d along-ex: `partitionFunctionAlongExhaustion` DifferentiableAt J at h = 0**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_differentiableAt_J_h_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    DifferentiableAt ℝ (fun J' : ℝ =>
      Ambient.partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J', 0, β⟩ n) J :=
  Ambient.partitionFunctionAlongExhaustion_differentiableAt_J_h_zero
    (IsingModel.latticeGraph d) Λ J β n

/-! ## Moved: partitionFunctionAlongEx continuousAt/diffAt general-h

The four wrappers
`partitionFunctionAlongExhaustion_latticeGraph_continuousAt_beta_general_h`,
`partitionFunctionAlongExhaustion_latticeGraph_continuousAt_J_general_h`,
`partitionFunctionAlongExhaustion_latticeGraph_differentiableAt_beta_general_h`,
`partitionFunctionAlongExhaustion_latticeGraph_differentiableAt_J_general_h`
now live in
`PartitionFreeEnergyPointwiseRegularityGeneralH.lean`. -/


/-! ## Moved: partitionFunctionAlongExhaustion h / joint wrappers

The four `partitionFunctionAlongExhaustion_latticeGraph_*` wrappers
(`continuousAt_h`, `differentiableAt_h`, `continuousAt_joint`,
`differentiableAt_joint`) now live in
`PartitionFreeEnergyPointwiseRegularityHAndJoint.lean`. -/



/-! ## Moved: freeEnergyAlongExhaustion pointwise regularity wrappers

The eight wrappers
`freeEnergyAlongExhaustion_latticeGraph_{continuousAt,differentiableAt}_*`
now live in `PartitionFreeEnergyPointwiseRegularityFreeEnergy.lean`. -/


end Ambient
end IsingModel

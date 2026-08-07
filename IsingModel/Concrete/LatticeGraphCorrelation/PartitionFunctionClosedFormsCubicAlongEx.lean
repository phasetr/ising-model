import IsingModel.AmbientLattice.SpecialCases.PartitionFunctionClosedForms
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete partition-function cubicExhaustion-alongEx closed-form wrappers

Instantiates the along-exhaustion partition-function closed forms on the degenerate parameter
slices at `IsingModel.latticeGraph d` along `Ambient.cubicExhaustion d`, the exhaustion the
ℤ^d infinite-volume statements are phrased on.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d partitionFunctionAlongExhaustion β=0 per-stage**: `= 2^|Λ_n|`. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_beta_zero
    (d : ℕ) (J h : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h, 0⟩ : IsingParams ℝ) n
      = (2 : ℝ) ^ ((Ambient.cubicExhaustion d).volume n).card :=
  partitionFunctionAlongExhaustion_beta_zero (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J h n

/-- **ℤ^d log_partitionFunctionAlongExhaustion β=0**: `= |Λ_n|·log 2`. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_beta_zero
    (d : ℕ) (J h : ℝ) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h, 0⟩ : IsingParams ℝ) n)
      = (((Ambient.cubicExhaustion d).volume n).card : ℝ) * Real.log 2 :=
  log_partitionFunctionAlongExhaustion_beta_zero (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J h n

end Ambient
end IsingModel

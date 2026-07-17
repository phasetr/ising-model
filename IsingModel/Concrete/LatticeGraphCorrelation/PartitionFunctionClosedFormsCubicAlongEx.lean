import IsingModel.AmbientLattice.SpecialCases.PartitionFunctionClosedForms
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete partition-function cubicExhaustion-alongEx closed-form wrappers

Narrow child module for six ℤ^d cubicExhaustion-alongExhaustion
closed-form wrappers (Z and log Z, at `J = 0`, `β = 0`, and
`zero_params` trivial slices). Each wrapper is a thin pass-through to
the corresponding ambient `partitionFunctionAlongExhaustion_*` lemma at
the `cubicExhaustion` exhaustion.
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

/-! ## Moved: cubicAlongEx zero_params + J_zero closed-form wrappers

The four wrappers
`partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_zero_params`,
`log_partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_zero_params`,
`partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_J_zero`,
`log_partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_J_zero` now
live in `PartitionFunctionClosedFormsCubicAlongExZeroPJ.lean`. -/


end Ambient
end IsingModel

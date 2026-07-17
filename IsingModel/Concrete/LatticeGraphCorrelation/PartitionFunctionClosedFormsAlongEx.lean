import IsingModel.AmbientLattice.SpecialCases.PartitionFunctionClosedForms
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d partitionFunctionAlongExhaustion closed-form wrappers

Narrow child module for six ℤ^d
`{partitionFunction,log_partitionFunction}AlongExhaustion_latticeGraph_*`
trivial-slice wrappers (`beta_zero`, `zero_params`, `J_zero`) extracted from
`PartitionFunctionClosedForms.lean`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d partitionFunctionAlongExhaustion β=0 per-stage** (any-Exhaustion):
`= 2^|Λ_n|`. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_beta_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J h : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ) n
      = (2 : ℝ) ^ (Λ.volume n).card :=
  partitionFunctionAlongExhaustion_beta_zero
    (IsingModel.latticeGraph d) Λ J h n

/-- **ℤ^d log_partitionFunctionAlongExhaustion β=0** (any-Exhaustion):
`= |Λ_n|·log 2`. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_beta_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J h : ℝ) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ) n)
      = ((Λ.volume n).card : ℝ) * Real.log 2 :=
  log_partitionFunctionAlongExhaustion_beta_zero
    (IsingModel.latticeGraph d) Λ J h n

/-! ## Moved: alongEx zero_params + J_zero closed-form wrappers

The four wrappers
`partitionFunctionAlongExhaustion_latticeGraph_zero_params`,
`log_partitionFunctionAlongExhaustion_latticeGraph_zero_params`,
`partitionFunctionAlongExhaustion_latticeGraph_J_zero`,
`log_partitionFunctionAlongExhaustion_latticeGraph_J_zero` now live
in `PartitionFunctionClosedFormsAlongExZeroPJ.lean`. -/


end Ambient
end IsingModel

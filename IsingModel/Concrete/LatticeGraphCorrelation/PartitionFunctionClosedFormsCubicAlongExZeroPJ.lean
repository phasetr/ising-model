import IsingModel.AmbientLattice.SpecialCases.PartitionFunctionClosedForms
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d cubicExhaustion-alongEx zero_params + J_zero closed-form wrappers

Narrow child module for four ℤ^d cubicExhaustion-alongExhaustion
closed-form wrappers extracted from
`PartitionFunctionClosedFormsCubicAlongEx.lean`:

* `partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_zero_params`,
* `log_partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_zero_params`,
* `partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_J_zero`,
* `log_partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_J_zero`.

Each result is a thin pass-through of the corresponding ambient
`Ambient.{partition,log_partition}FunctionAlongExhaustion_*` lemma
at the `cubicExhaustion` exhaustion. The theorem names are unchanged
from the former `PartitionFunctionClosedFormsCubicAlongEx`
declarations.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d partitionFunctionAlongExhaustion J=h=0 per-stage**: `= 2^|Λ_n|`. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_zero_params
    (d : ℕ) (β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ) n
      = (2 : ℝ) ^ ((Ambient.cubicExhaustion d).volume n).card :=
  partitionFunctionAlongExhaustion_zero_params (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) β n

/-- **ℤ^d log_partitionFunctionAlongExhaustion J=h=0**: `= |Λ_n|·log 2`. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_zero_params
    (d : ℕ) (β : ℝ) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ) n)
      = (((Ambient.cubicExhaustion d).volume n).card : ℝ) * Real.log 2 :=
  log_partitionFunctionAlongExhaustion_zero_params (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) β n

/-- **ℤ^d partitionFunctionAlongExhaustion J=0 per-stage**:
`= (2·cosh(β·h))^|Λ_n|`. Concrete specialization of
`partitionFunctionAlongExhaustion_J_zero`. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_J_zero
    (d : ℕ) (h β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨0, h, β⟩ : IsingParams ℝ) n
      = (2 * Real.cosh (β * h)) ^
          ((Ambient.cubicExhaustion d).volume n).card :=
  partitionFunctionAlongExhaustion_J_zero (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) h β n

/-- **ℤ^d log_partitionFunctionAlongExhaustion J=0**:
`= |Λ_n|·log(2·cosh(β·h))`. Concrete specialization of
`log_partitionFunctionAlongExhaustion_J_zero`. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_J_zero
    (d : ℕ) (h β : ℝ) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨0, h, β⟩ : IsingParams ℝ) n)
      = (((Ambient.cubicExhaustion d).volume n).card : ℝ)
          * Real.log (2 * Real.cosh (β * h)) :=
  log_partitionFunctionAlongExhaustion_J_zero (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) h β n

end Ambient
end IsingModel

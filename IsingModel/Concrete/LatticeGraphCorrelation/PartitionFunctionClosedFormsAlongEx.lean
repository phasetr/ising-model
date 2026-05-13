import IsingModel.Concrete.LatticeGraphBED
import IsingModel.AmbientLattice.SpecialCases.PartitionFunctionClosedForms

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

/-- **ℤ^d partitionFunctionAlongExhaustion J=h=0 per-stage** (any-Exhaustion):
`= 2^|Λ_n|`. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_zero_params
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) n
      = (2 : ℝ) ^ (Λ.volume n).card :=
  partitionFunctionAlongExhaustion_zero_params
    (IsingModel.latticeGraph d) Λ β n

/-- **ℤ^d log_partitionFunctionAlongExhaustion J=h=0** (any-Exhaustion):
`= |Λ_n|·log 2`. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_zero_params
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (β : ℝ) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) n)
      = ((Λ.volume n).card : ℝ) * Real.log 2 :=
  log_partitionFunctionAlongExhaustion_zero_params
    (IsingModel.latticeGraph d) Λ β n

/-- **ℤ^d partitionFunctionAlongExhaustion J=0 per-stage** (any-Exhaustion):
`= (2·cosh(β·h))^|Λ_n|`. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) n
      = (2 * Real.cosh (β * h)) ^ (Λ.volume n).card :=
  partitionFunctionAlongExhaustion_J_zero
    (IsingModel.latticeGraph d) Λ h β n

/-- **ℤ^d log_partitionFunctionAlongExhaustion J=0** (any-Exhaustion):
`= |Λ_n|·log(2·cosh(β·h))`. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) n)
      = ((Λ.volume n).card : ℝ) * Real.log (2 * Real.cosh (β * h)) :=
  log_partitionFunctionAlongExhaustion_J_zero
    (IsingModel.latticeGraph d) Λ h β n

end Ambient
end IsingModel

import IsingModel.Concrete.LatticeGraphBED
import IsingModel.AmbientLattice.SpecialCases.PartitionFunctionClosedForms

/-!
# Concrete partition-function closed-form wrappers

Narrow child module for concrete `latticeGraph` partition-function closed-form
wrappers at trivial parameter slices. The theorem names are the same as the
former legacy declarations, but callers can now avoid importing the monolithic
concrete legacy module.
-/

namespace IsingModel
namespace Ambient

/-! ### ℤ^d partition-function closed forms -/

/-- **ℤ^d partitionFunctionΛ closed form at `J = 0`** (any Finset):
`Z_Λ(⟨0, h, β⟩) = (2·cosh(β·h))^|Λ|`. -/
theorem partitionFunctionΛ_latticeGraph_J_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ)
      = (2 * Real.cosh (β * h)) ^ Λ.card :=
  partitionFunctionΛ_J_zero (IsingModel.latticeGraph d) Λ h β

/-- **ℤ^d partitionFunctionΛ closed form at `β = 0`** (any Finset):
`Z_Λ(⟨J, h, 0⟩) = 2^|Λ|`. -/
theorem partitionFunctionΛ_latticeGraph_beta_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h : ℝ) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Λ.card :=
  partitionFunctionΛ_beta_zero (IsingModel.latticeGraph d) Λ J h

/-- **ℤ^d partitionFunctionΛ closed form at `J = 0, h = 0`** (any Finset):
`Z_Λ(⟨0, 0, β⟩) = 2^|Λ|`. -/
theorem partitionFunctionΛ_latticeGraph_zero_params
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (β : ℝ) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Λ.card :=
  partitionFunctionΛ_zero_params (IsingModel.latticeGraph d) Λ β

/-- **ℤ^d log partitionFunctionΛ closed form at `J = 0`** (any Finset):
`log Z_Λ(⟨0, h, β⟩) = |Λ| · log(2·cosh(β·h))`. -/
theorem log_partitionFunctionΛ_latticeGraph_J_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ))
      = (Λ.card : ℝ) * Real.log (2 * Real.cosh (β * h)) :=
  by rw [partitionFunctionΛ_latticeGraph_J_zero, Real.log_pow]

/-- **ℤ^d log partitionFunctionΛ closed form at `β = 0`** (any Finset):
`log Z_Λ(⟨J, h, 0⟩) = |Λ| · log 2`. -/
theorem log_partitionFunctionΛ_latticeGraph_beta_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h : ℝ) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ))
      = (Λ.card : ℝ) * Real.log 2 :=
  by rw [partitionFunctionΛ_latticeGraph_beta_zero, Real.log_pow]

/-- **ℤ^d log partitionFunctionΛ closed form at `J = 0, h = 0`** (any Finset):
`log Z_Λ(⟨0, 0, β⟩) = |Λ| · log 2`. -/
theorem log_partitionFunctionΛ_latticeGraph_zero_params
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (β : ℝ) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ))
      = (Λ.card : ℝ) * Real.log 2 :=
  by rw [partitionFunctionΛ_latticeGraph_zero_params, Real.log_pow]

/-! ## Moved: cubicExhaustion-Λ closed-form wrappers

The six wrappers
`partitionFunctionΛ_latticeGraph_cubicExhaustion_{J_zero,beta_zero,zero_params}`
and `log_partitionFunctionΛ_latticeGraph_cubicExhaustion_{J_zero,beta_zero,zero_params}`
now live in `PartitionFunctionClosedFormsCubicLambda.lean`. -/


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

/-! ## Moved: cubicExhaustion-alongEx closed-form wrappers

The six wrappers
`partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_{J_zero,beta_zero,zero_params}`
and `log_partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_{J_zero,beta_zero,zero_params}`
now live in `PartitionFunctionClosedFormsCubicAlongEx.lean`. -/


end Ambient
end IsingModel

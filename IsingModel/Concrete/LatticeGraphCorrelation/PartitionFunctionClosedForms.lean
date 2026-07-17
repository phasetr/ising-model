import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete partition-function closed-form wrappers

Narrow child module for concrete `latticeGraph` partition-function closed-form
wrappers at trivial parameter slices. The theorem names are the same as the
former declarations, but callers can now avoid importing the monolithic
concrete original module.
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

/-! ## Moved: log_partitionFunctionΛ closed-form wrappers

The three wrappers
`log_partitionFunctionΛ_latticeGraph_J_zero`,
`log_partitionFunctionΛ_latticeGraph_beta_zero`,
`log_partitionFunctionΛ_latticeGraph_zero_params` now live in
`PartitionFunctionClosedFormsLog.lean`. -/


/-! ## Moved: cubicExhaustion-Λ closed-form wrappers

The six wrappers
`partitionFunctionΛ_latticeGraph_cubicExhaustion_{J_zero,beta_zero,zero_params}`
and `log_partitionFunctionΛ_latticeGraph_cubicExhaustion_{J_zero,beta_zero,zero_params}`
now live in `PartitionFunctionClosedFormsCubicLambda.lean`. -/


/-! ## Moved: along-ex closed-form trivial-slice wrappers

The six wrappers
`{partitionFunction,log_partitionFunction}AlongExhaustion_latticeGraph_*`
(`{_beta_zero, _zero_params, _J_zero}`) now live in
`PartitionFunctionClosedFormsAlongEx.lean`. -/



/-! ## Moved: cubicExhaustion-alongEx closed-form wrappers

The six wrappers
`partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_*`
and
`log_partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_*`
(`{_J_zero, _beta_zero, _zero_params}` each) now live in
`PartitionFunctionClosedFormsCubicAlongEx.lean`. -/


end Ambient
end IsingModel

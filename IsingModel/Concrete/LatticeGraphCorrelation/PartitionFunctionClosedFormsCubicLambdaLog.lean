import IsingModel.Concrete.LatticeGraphCorrelation.PartitionFunctionClosedFormsCubicLambda

/-!
# ℤ^d cubicExhaustion-Λ `log_partitionFunctionΛ` closed-form wrappers

Narrow child module for three ℤ^d cubicExhaustion-Λ
`log_partitionFunctionΛ_*` closed-form wrappers extracted from
`PartitionFunctionClosedFormsCubicLambda.lean`:

* `log_partitionFunctionΛ_latticeGraph_cubicExhaustion_J_zero`,
* `log_partitionFunctionΛ_latticeGraph_cubicExhaustion_beta_zero`,
* `log_partitionFunctionΛ_latticeGraph_cubicExhaustion_zero_params`.

Each result is derived from the corresponding
`partitionFunctionΛ_latticeGraph_cubicExhaustion_*` closed form via
`Real.log_pow`. The theorem names are unchanged from the former
`PartitionFunctionClosedFormsCubicLambda` declarations.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d log_partitionFunctionΛ closed form at `J = 0`**:
`log Z_{Λ_n}(⟨0, h, β⟩) = |Λ_n| · log(2·cosh(β·h))` on the ℤ^d cubic box.
Concrete specialization of `log_partitionFunctionΛ_J_zero`. -/
theorem log_partitionFunctionΛ_latticeGraph_cubicExhaustion_J_zero
    (d : ℕ) (h β : ℝ) (n : ℕ) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d)
        ((Ambient.cubicExhaustion d).volume n) (⟨0, h, β⟩ : IsingParams ℝ))
      = (((Ambient.cubicExhaustion d).volume n).card : ℝ)
          * Real.log (2 * Real.cosh (β * h)) :=
  by rw [partitionFunctionΛ_latticeGraph_cubicExhaustion_J_zero, Real.log_pow]

/-- **ℤ^d log_partitionFunctionΛ closed form at `β = 0`**:
`log Z_{Λ_n}(⟨J, h, 0⟩) = |Λ_n| · log 2` on the ℤ^d cubic box.
Concrete specialization of `log_partitionFunctionΛ_beta_zero`. -/
theorem log_partitionFunctionΛ_latticeGraph_cubicExhaustion_beta_zero
    (d : ℕ) (J h : ℝ) (n : ℕ) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d)
        ((Ambient.cubicExhaustion d).volume n) (⟨J, h, 0⟩ : IsingParams ℝ))
      = (((Ambient.cubicExhaustion d).volume n).card : ℝ) * Real.log 2 :=
  by rw [partitionFunctionΛ_latticeGraph_cubicExhaustion_beta_zero, Real.log_pow]

/-- **ℤ^d log_partitionFunctionΛ closed form at `J = 0, h = 0`**:
`log Z_{Λ_n}(⟨0, 0, β⟩) = |Λ_n| · log 2` on the ℤ^d cubic box.
Concrete specialization of `log_partitionFunctionΛ_zero_params`. -/
theorem log_partitionFunctionΛ_latticeGraph_cubicExhaustion_zero_params
    (d : ℕ) (β : ℝ) (n : ℕ) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d)
        ((Ambient.cubicExhaustion d).volume n) (⟨0, 0, β⟩ : IsingParams ℝ))
      = (((Ambient.cubicExhaustion d).volume n).card : ℝ) * Real.log 2 :=
  by rw [partitionFunctionΛ_latticeGraph_cubicExhaustion_zero_params, Real.log_pow]

end Ambient
end IsingModel

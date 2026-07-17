import IsingModel.Concrete.LatticeGraphCorrelation.PartitionFunctionClosedForms

/-!
# ℤ^d `log_partitionFunctionΛ_latticeGraph_*` closed-form wrappers

Narrow child module for three ℤ^d
`log_partitionFunctionΛ_latticeGraph_*` closed-form wrappers
extracted from `PartitionFunctionClosedForms.lean`:

* `log_partitionFunctionΛ_latticeGraph_J_zero`,
* `log_partitionFunctionΛ_latticeGraph_beta_zero`,
* `log_partitionFunctionΛ_latticeGraph_zero_params`.

Each result is derived from the corresponding
`partitionFunctionΛ_latticeGraph_*` closed form via `Real.log_pow`.
The theorem names are unchanged from the former
`PartitionFunctionClosedForms` declarations.
-/

namespace IsingModel
namespace Ambient

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

end Ambient
end IsingModel

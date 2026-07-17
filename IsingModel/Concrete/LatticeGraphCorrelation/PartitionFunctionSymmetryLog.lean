import IsingModel.AmbientLatticeSum
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete log partition-function h-symmetry wrappers

Narrow child module for nine ℤ^d `log_partitionFunction*_latticeGraph_*`
h-symmetry (`_neg_h`, `_eq_abs_h`, `_monotone_abs_h`) wrappers at the
Λ-direct and along-exhaustion (including cubicExhaustion) variants.
Each wrapper is a thin pass-through to the corresponding ambient
`log_partitionFunction*_*` lemma at `IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient

/-! ### ℤ^d log partition-function h-symmetry and absolute-field wrappers -/

/-- **ℤ^d log_partitionFunctionΛ h-evenness**:
`log Z_Λ(J,-h,β) = log Z_Λ(J,h,β)`. -/
theorem log_partitionFunctionΛ_latticeGraph_neg_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, -h, β⟩ : IsingParams ℝ))
      = Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ)) :=
  log_partitionFunctionΛ_neg_h (IsingModel.latticeGraph d) Λ J h β

/-- **ℤ^d log_partitionFunctionΛ `|h|`-rewrite**:
`log Z_Λ(J,h,β) = log Z_Λ(J,|h|,β)`. -/
theorem log_partitionFunctionΛ_latticeGraph_eq_abs_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ))
      = Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, |h|, β⟩ : IsingParams ℝ)) :=
  log_partitionFunctionΛ_eq_abs_h (IsingModel.latticeGraph d) Λ J h β

/-- **ℤ^d log_partitionFunctionΛ `|h|`-monotonicity** (ferromagnetic). -/
theorem log_partitionFunctionΛ_latticeGraph_monotone_abs_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h₁, β⟩ : IsingParams ℝ))
      ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h₂, β⟩ : IsingParams ℝ)) :=
  log_partitionFunctionΛ_monotone_abs_h (IsingModel.latticeGraph d) Λ J β hJ hβ hh

/-! ## Moved: log_partitionFunctionAlongExhaustion h-symmetry wrappers

The three wrappers
`log_partitionFunctionAlongExhaustion_latticeGraph_neg_h`,
`log_partitionFunctionAlongExhaustion_latticeGraph_eq_abs_h`,
`log_partitionFunctionAlongExhaustion_latticeGraph_monotone_abs_h` now
live in `PartitionFunctionSymmetryLogAlongEx.lean`. -/


/-! ## Moved: log_partitionFunctionAlongEx cubicExhaustion |h| wrappers

The three wrappers
`log_partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_neg_h`,
`log_partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_eq_abs_h`,
`log_partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_monotone_abs_h`
now live in `PartitionFunctionSymmetryLogCubic.lean`. -/


end Ambient
end IsingModel

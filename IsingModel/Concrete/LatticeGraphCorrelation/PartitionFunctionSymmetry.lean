import IsingModel.AmbientLatticeSum
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete partition-function symmetry wrappers

Narrow child module for concrete `latticeGraph` partition-function h-symmetry,
absolute-field rewrite, and absolute-field monotonicity wrappers. The theorem
names are the same as the former declarations, but callers can now avoid
importing the monolithic concrete module.
-/

namespace IsingModel
namespace Ambient

/-! ### ℤ^d partition-function h-symmetry and absolute-field wrappers -/

/-- **ℤ^d partitionFunctionΛ h-evenness** (any Finset):
`Z_Λ(J, -h, β) = Z_Λ(J, h, β)`. -/
theorem partitionFunctionΛ_latticeGraph_neg_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, -h, β⟩ : IsingParams ℝ)
      = partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ) :=
  partitionFunctionΛ_neg_h (IsingModel.latticeGraph d) Λ J h β

/-- **ℤ^d partitionFunctionΛ h-evenness**:
`Z_{Λ_n}(J, -h, β) = Z_{Λ_n}(J, h, β)` on the ℤ^d cubic box.
Concrete specialization of `partitionFunctionΛ_neg_h`. -/
theorem partitionFunctionΛ_latticeGraph_cubicExhaustion_neg_h
    (d : ℕ) (J h β : ℝ) (n : ℕ) :
    partitionFunctionΛ (IsingModel.latticeGraph d)
        ((Ambient.cubicExhaustion d).volume n) (⟨J, -h, β⟩ : IsingParams ℝ)
      = partitionFunctionΛ (IsingModel.latticeGraph d)
          ((Ambient.cubicExhaustion d).volume n) (⟨J, h, β⟩ : IsingParams ℝ) :=
  partitionFunctionΛ_neg_h (IsingModel.latticeGraph d)
    ((Ambient.cubicExhaustion d).volume n) J h β

/-- **ℤ^d partitionFunctionΛ `|h|`-rewrite**:
`Z_Λ(J,h,β) = Z_Λ(J,|h|,β)`. Concrete specialization of
`partitionFunctionΛ_eq_abs_h`. -/
theorem partitionFunctionΛ_latticeGraph_eq_abs_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ)
      = partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, |h|, β⟩ : IsingParams ℝ) :=
  partitionFunctionΛ_eq_abs_h (IsingModel.latticeGraph d) Λ J h β

/-- **ℤ^d partitionFunctionΛ ferromagnetic `|h|`-monotonicity**:
for `J ≥ 0`, `β > 0`, `|h₁| ≤ |h₂|`,
`Z_Λ(J,h₁,β) ≤ Z_Λ(J,h₂,β)`. Concrete specialization of
`partitionFunctionΛ_monotone_abs_h`. -/
theorem partitionFunctionΛ_latticeGraph_monotone_abs_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h₁, β⟩ : IsingParams ℝ)
      ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h₂, β⟩ : IsingParams ℝ) :=
  partitionFunctionΛ_monotone_abs_h (IsingModel.latticeGraph d) Λ J β hJ hβ hh

/-! ## Moved: partitionFunctionAlongEx |h|-symmetry wrappers

The four wrappers
`partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_neg_h`,
`partitionFunctionAlongExhaustion_latticeGraph_neg_h`,
`partitionFunctionAlongExhaustion_latticeGraph_eq_abs_h`,
`partitionFunctionAlongExhaustion_latticeGraph_monotone_abs_h`
now live in `PartitionFunctionSymmetryAlongEx.lean`. -/


/-! ## Removed: cubicExhaustion abs-h wrappers

The two ℤ^d cubic-exhaustion `partitionFunctionAlongExhaustion` absolute-field
wrappers of this family had no consumers and were deleted in PR #4754.  The
`log_` variants remain in `PartitionFunctionSymmetryLogCubic.lean`. -/



/-! ## Moved: log partition-function h-symmetry wrappers

The six ℤ^d `log_partitionFunction*` h-symmetry wrappers (`_neg_h`,
`_eq_abs_h`, `_monotone_abs_h`, at the Λ-direct and cubicExhaustion
along-exhaustion variants) now live in
`PartitionFunctionSymmetryLog.lean` and its
`PartitionFunctionSymmetryLogCubic.lean` child. -/


end Ambient
end IsingModel

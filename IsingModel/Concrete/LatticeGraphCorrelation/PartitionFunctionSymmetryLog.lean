import IsingModel.AmbientLatticeSum
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete log partition-function h-symmetry wrappers

Instantiates the ℤ^d form of the spin-flip symmetry argument for the Λ-level log partition
function at `IsingModel.latticeGraph d`: how it behaves under `h ↦ -h`, and
how it depends on `|h|`.
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

end Ambient
end IsingModel

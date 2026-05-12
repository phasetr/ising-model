import IsingModel.Concrete.LatticeGraphBED
import IsingModel.AmbientLattice.SpecialCases.PartitionFunctionSymmetry
import IsingModel.AmbientLatticeSum

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

/-- **ℤ^d log_partitionFunctionAlongExhaustion h-evenness** (any Exhaustion). -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_neg_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h β : ℝ) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, -h, β⟩ : IsingParams ℝ) n)
      = Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ) n) :=
  log_partitionFunctionAlongExhaustion_neg_h
    (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d log_partitionFunctionAlongExhaustion `|h|`-rewrite** (any Exhaustion). -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_eq_abs_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h β : ℝ) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) n)
      = Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, |h|, β⟩ : IsingParams ℝ) n) :=
  log_partitionFunctionAlongExhaustion_eq_abs_h
    (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d log_partitionFunctionAlongExhaustion `|h|`-monotonicity** (any Exhaustion). -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_monotone_abs_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h₁, β⟩ : IsingParams ℝ) n)
      ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h₂, β⟩ : IsingParams ℝ) n) :=
  log_partitionFunctionAlongExhaustion_monotone_abs_h
    (IsingModel.latticeGraph d) Λ J β hJ hβ hh n

/-- **ℤ^d log_partitionFunctionAlongExhaustion h-evenness** per stage. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_neg_h
    (d : ℕ) (J h β : ℝ) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, -h, β⟩ : IsingParams ℝ) n)
      = Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, h, β⟩ : IsingParams ℝ) n) :=
  log_partitionFunctionAlongExhaustion_neg_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J h β n

/-- **ℤ^d log_partitionFunctionAlongExhaustion `|h|`-rewrite** per stage. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_eq_abs_h
    (d : ℕ) (J h β : ℝ) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h, β⟩ : IsingParams ℝ) n)
      = Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, |h|, β⟩ : IsingParams ℝ) n) :=
  log_partitionFunctionAlongExhaustion_eq_abs_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J h β n

/-- **ℤ^d log_partitionFunctionAlongExhaustion `|h|`-monotonicity** per stage. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_monotone_abs_h
    (d : ℕ) (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h₁, β⟩ : IsingParams ℝ) n)
      ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, h₂, β⟩ : IsingParams ℝ) n) :=
  log_partitionFunctionAlongExhaustion_monotone_abs_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J β hJ hβ hh n

end Ambient
end IsingModel

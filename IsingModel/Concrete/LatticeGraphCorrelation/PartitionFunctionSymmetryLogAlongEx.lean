import IsingModel.AmbientLatticeSum
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d `log_partitionFunctionAlongExhaustion_latticeGraph_*` h-symmetry wrappers

Narrow child module for three ℤ^d
`log_partitionFunctionAlongExhaustion_latticeGraph_*` h-symmetry
wrappers extracted from `PartitionFunctionSymmetryLog.lean`:

* `log_partitionFunctionAlongExhaustion_latticeGraph_neg_h`,
* `log_partitionFunctionAlongExhaustion_latticeGraph_eq_abs_h`,
* `log_partitionFunctionAlongExhaustion_latticeGraph_monotone_abs_h`.

Each result is a thin pass-through of the ambient
`Ambient.log_partitionFunctionAlongExhaustion_*` lemma at
`G := IsingModel.latticeGraph d`. The theorem names are unchanged
from the former `PartitionFunctionSymmetryLog` declarations.
-/

namespace IsingModel
namespace Ambient

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

end Ambient
end IsingModel

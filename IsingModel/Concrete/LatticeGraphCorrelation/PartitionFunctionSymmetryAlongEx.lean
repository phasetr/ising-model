import IsingModel.AmbientLattice.SpecialCases.PartitionFunctionSymmetry
import IsingModel.AmbientLatticeSum
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d partitionFunctionAlongEx |h|-symmetry wrappers

Narrow child module for four ℤ^d
`partitionFunctionAlongExhaustion_latticeGraph_*` |h|-related wrappers
extracted from `PartitionFunctionSymmetry.lean`:

* `partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_neg_h`,
* `partitionFunctionAlongExhaustion_latticeGraph_neg_h`,
* `partitionFunctionAlongExhaustion_latticeGraph_eq_abs_h`,
* `partitionFunctionAlongExhaustion_latticeGraph_monotone_abs_h`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d partitionFunctionAlongExhaustion h-evenness** per stage:
`Z(Λ_n; J, -h, β) = Z(Λ_n; J, h, β)`. Concrete specialization of
`partitionFunctionAlongExhaustion_neg_h`. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_neg_h
    (d : ℕ) (J h β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, -h, β⟩ : IsingParams ℝ) n
      = partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, h, β⟩ : IsingParams ℝ) n :=
  partitionFunctionAlongExhaustion_neg_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J h β n

/-- **ℤ^d partitionFunctionAlongExhaustion h-evenness** per stage (any Exhaustion). -/
theorem partitionFunctionAlongExhaustion_latticeGraph_neg_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, -h, β⟩ : IsingParams ℝ) n
      = partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ) n :=
  partitionFunctionAlongExhaustion_neg_h (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d partitionFunctionAlongExhaustion `|h|`-rewrite** per stage (any Exhaustion). -/
theorem partitionFunctionAlongExhaustion_latticeGraph_eq_abs_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) n
      = partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, |h|, β⟩ : IsingParams ℝ) n :=
  partitionFunctionAlongExhaustion_eq_abs_h (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d partitionFunctionAlongExhaustion ferromagnetic `|h|`-monotonicity**
per stage (any Exhaustion). -/
theorem partitionFunctionAlongExhaustion_latticeGraph_monotone_abs_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h₁, β⟩ : IsingParams ℝ) n
      ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h₂, β⟩ : IsingParams ℝ) n :=
  partitionFunctionAlongExhaustion_monotone_abs_h (IsingModel.latticeGraph d) Λ
    J β hJ hβ hh n

end Ambient
end IsingModel

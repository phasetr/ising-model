import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d log_partitionFunctionAlongExhaustion cubic monotone wrappers

Narrow child module for three ℤ^d
`log_partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_monotone_{J,h,beta}`
wrappers extracted from `PartitionFreeEnergyMonotonicity.lean`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d log_partitionFunctionAlongExhaustion J-monotonicity** per stage. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_monotone_J
    (d : ℕ) (h β : ℝ) (hh : 0 ≤ h) (hβ : 0 < β) {J₁ J₂ : ℝ}
    (hJ₁ : 0 ≤ J₁) (hJ : J₁ ≤ J₂) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J₁, h, β⟩ : IsingParams ℝ) n)
      ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J₂, h, β⟩ : IsingParams ℝ) n) :=
  log_partitionFunctionAlongExhaustion_monotone_J (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) h β hh hβ hJ₁ hJ n

/-- **ℤ^d log_partitionFunctionAlongExhaustion h-monotonicity** per stage. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_monotone_h
    (d : ℕ) (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) {h₁ h₂ : ℝ}
    (hh₁ : 0 ≤ h₁) (hh : h₁ ≤ h₂) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h₁, β⟩ : IsingParams ℝ) n)
      ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, h₂, β⟩ : IsingParams ℝ) n) :=
  log_partitionFunctionAlongExhaustion_monotone_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J β hJ hβ hh₁ hh n

/-- **ℤ^d log_partitionFunctionAlongExhaustion β-monotonicity** per stage. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_monotone_beta
    (d : ℕ) (J h : ℝ) (hJ : 0 ≤ J) (hh : 0 ≤ h) {β₁ β₂ : ℝ}
    (hβ₁ : 0 < β₁) (hβ : β₁ ≤ β₂) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h, β₁⟩ : IsingParams ℝ) n)
      ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, h, β₂⟩ : IsingParams ℝ) n) :=
  log_partitionFunctionAlongExhaustion_monotone_beta (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J h hJ hh hβ₁ hβ n

end Ambient
end IsingModel

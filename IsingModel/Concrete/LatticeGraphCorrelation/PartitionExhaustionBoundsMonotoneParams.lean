import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete partitionFunctionAlongExhaustion parameter monotonicity wrappers

Narrow child module for six ℤ^d
`partitionFunctionAlongExhaustion_latticeGraph_(_cubicExhaustion)?_monotone_{J,h,beta}`
wrappers, each a thin pass-through to the corresponding ambient
`partitionFunctionAlongExhaustion_monotone_*` lemma at
`IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient
/-! ## Moved: cubicEx partitionFunctionAlongEx monotone wrappers

The three wrappers
`partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_monotone_J`,
`partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_monotone_h`,
`partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_monotone_beta`
now live in `PartitionExhaustionBoundsMonotoneParamsCubic.lean`. -/


/-- **ℤ^d per-stage J-monotonicity of partitionFunctionAlongExhaustion** (any Exhaustion). -/
theorem partitionFunctionAlongExhaustion_latticeGraph_monotone_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (h β : ℝ) (hh : 0 ≤ h) (hβ : 0 < β) {J₁ J₂ : ℝ}
    (hJ₁ : 0 ≤ J₁) (hJ : J₁ ≤ J₂) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J₁, h, β⟩ : IsingParams ℝ) n
      ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J₂, h, β⟩ : IsingParams ℝ) n :=
  partitionFunctionAlongExhaustion_monotone_J (IsingModel.latticeGraph d) Λ
    h β hh hβ hJ₁ hJ n

/-- **ℤ^d per-stage h-monotonicity of partitionFunctionAlongExhaustion** (any Exhaustion). -/
theorem partitionFunctionAlongExhaustion_latticeGraph_monotone_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) {h₁ h₂ : ℝ}
    (hh₁ : 0 ≤ h₁) (hh : h₁ ≤ h₂) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h₁, β⟩ : IsingParams ℝ) n
      ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h₂, β⟩ : IsingParams ℝ) n :=
  partitionFunctionAlongExhaustion_monotone_h (IsingModel.latticeGraph d) Λ
    J β hJ hβ hh₁ hh n

/-- **ℤ^d per-stage β-monotonicity of partitionFunctionAlongExhaustion** (any Exhaustion). -/
theorem partitionFunctionAlongExhaustion_latticeGraph_monotone_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h : ℝ) (hJ : 0 ≤ J) (hh : 0 ≤ h) {β₁ β₂ : ℝ}
    (hβ₁ : 0 < β₁) (hβ : β₁ ≤ β₂) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β₁⟩ : IsingParams ℝ) n
      ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h, β₂⟩ : IsingParams ℝ) n :=
  partitionFunctionAlongExhaustion_monotone_beta (IsingModel.latticeGraph d) Λ
    J h hJ hh hβ₁ hβ n

end Ambient
end IsingModel

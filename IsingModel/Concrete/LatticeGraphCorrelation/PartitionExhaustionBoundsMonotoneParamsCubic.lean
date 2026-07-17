import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d cubicExhaustion partitionFunctionAlongEx monotone wrappers

Narrow child module for three ℤ^d
`partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_monotone_*`
wrappers extracted from `PartitionExhaustionBoundsMonotoneParams.lean`:

* `partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_monotone_J`,
* `partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_monotone_h`,
* `partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_monotone_beta`.

Each result instantiates the corresponding generic
`partitionFunctionAlongExhaustion_monotone_*` lemma at the concrete
cubic exhaustion. The theorem names are unchanged from the former
`PartitionExhaustionBoundsMonotoneParams` declarations.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d per-stage J-monotonicity of partitionFunctionAlongExhaustion**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_monotone_J
    (d : ℕ) (h β : ℝ) (hh : 0 ≤ h) (hβ : 0 < β) {J₁ J₂ : ℝ}
    (hJ₁ : 0 ≤ J₁) (hJ : J₁ ≤ J₂) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J₁, h, β⟩ n
      ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) ⟨J₂, h, β⟩ n :=
  partitionFunctionAlongExhaustion_monotone_J (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) h β hh hβ hJ₁ hJ n

/-- **ℤ^d per-stage h-monotonicity of partitionFunctionAlongExhaustion**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_monotone_h
    (d : ℕ) (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) {h₁ h₂ : ℝ}
    (hh₁ : 0 ≤ h₁) (hh : h₁ ≤ h₂) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, h₁, β⟩ n
      ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) ⟨J, h₂, β⟩ n :=
  partitionFunctionAlongExhaustion_monotone_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J β hJ hβ hh₁ hh n

/-- **ℤ^d per-stage β-monotonicity of partitionFunctionAlongExhaustion**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_monotone_beta
    (d : ℕ) (J h : ℝ) (hJ : 0 ≤ J) (hh : 0 ≤ h) {β₁ β₂ : ℝ}
    (hβ₁ : 0 < β₁) (hβ : β₁ ≤ β₂) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, h, β₁⟩ n
      ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) ⟨J, h, β₂⟩ n :=
  partitionFunctionAlongExhaustion_monotone_beta (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J h hJ hh hβ₁ hβ n

end Ambient
end IsingModel

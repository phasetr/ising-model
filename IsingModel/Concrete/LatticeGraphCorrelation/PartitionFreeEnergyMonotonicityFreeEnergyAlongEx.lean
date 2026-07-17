import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete freeEnergyAlongExhaustion monotonicity wrappers

Narrow child module for six ℤ^d
`freeEnergyAlongExhaustion_latticeGraph_(_cubicExhaustion)?_monotone_{J,h,beta}`
wrappers. Each wrapper is a thin pass-through to the corresponding
ambient `freeEnergyAlongExhaustion_monotone_*` lemma at
`IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient

/-! ## Moved: cubicExhaustion freeEnergyAlongEx monotone wrappers

The three wrappers
`freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_monotone_J`,
`freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_monotone_h`,
`freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_monotone_beta`
now live in `PartitionFreeEnergyMonotonicityFreeEnergyAlongExCubic.lean`. -/


/-- **ℤ^d per-stage J-monotonicity of freeEnergyAlongExhaustion** (any Exhaustion). -/
theorem freeEnergyAlongExhaustion_latticeGraph_monotone_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β) (n : ℕ) :
    MonotoneOn
      (fun J : ℝ => freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) n)
      (Set.Ici 0) :=
  freeEnergyAlongExhaustion_monotone_J (IsingModel.latticeGraph d) Λ hh hβ n

/-- **ℤ^d per-stage h-monotonicity of freeEnergyAlongExhaustion** (any Exhaustion). -/
theorem freeEnergyAlongExhaustion_latticeGraph_monotone_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (n : ℕ) :
    MonotoneOn
      (fun h : ℝ => freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) n)
      (Set.Ici 0) :=
  freeEnergyAlongExhaustion_monotone_h (IsingModel.latticeGraph d) Λ hJ hβ n

/-- **ℤ^d per-stage β-monotonicity of freeEnergyAlongExhaustion** (any Exhaustion). -/
theorem freeEnergyAlongExhaustion_latticeGraph_monotone_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h) (n : ℕ) :
    MonotoneOn
      (fun β : ℝ => freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) n)
      (Set.Ioi 0) :=
  freeEnergyAlongExhaustion_monotone_beta (IsingModel.latticeGraph d) Λ hJ hh n

end Ambient
end IsingModel

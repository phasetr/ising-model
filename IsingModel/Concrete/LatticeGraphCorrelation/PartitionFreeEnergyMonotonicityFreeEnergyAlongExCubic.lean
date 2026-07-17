import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d cubicExhaustion freeEnergyAlongEx monotone wrappers

Narrow child module for three ℤ^d
`freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_monotone_*`
wrappers extracted from
`PartitionFreeEnergyMonotonicityFreeEnergyAlongEx.lean`:

* `freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_monotone_J`,
* `freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_monotone_h`,
* `freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_monotone_beta`.

Each result instantiates the corresponding generic
`freeEnergyAlongExhaustion_monotone_*` lemma at the concrete cubic
exhaustion. The theorem names are unchanged from the former
`PartitionFreeEnergyMonotonicityFreeEnergyAlongEx` declarations.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d per-stage J-monotonicity of freeEnergyAlongExhaustion**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_monotone_J
    (d : ℕ) {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β) (n : ℕ) :
    MonotoneOn
      (fun J : ℝ => freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, h, β⟩ n)
      (Set.Ici 0) :=
  freeEnergyAlongExhaustion_monotone_J (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hh hβ n

/-- **ℤ^d per-stage h-monotonicity of freeEnergyAlongExhaustion**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_monotone_h
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (n : ℕ) :
    MonotoneOn
      (fun h : ℝ => freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, h, β⟩ n)
      (Set.Ici 0) :=
  freeEnergyAlongExhaustion_monotone_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hβ n

/-- **ℤ^d per-stage β-monotonicity of freeEnergyAlongExhaustion**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_monotone_beta
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h) (n : ℕ) :
    MonotoneOn
      (fun β : ℝ => freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, h, β⟩ n)
      (Set.Ioi 0) :=
  freeEnergyAlongExhaustion_monotone_beta (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hh n

end Ambient
end IsingModel

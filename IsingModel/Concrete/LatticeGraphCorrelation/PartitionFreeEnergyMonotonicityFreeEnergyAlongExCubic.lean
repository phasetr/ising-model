import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d per-stage parameter monotonicity of the free-energy density, cubic exhaustion

Instantiates at `IsingModel.latticeGraph d`, along `Ambient.cubicExhaustion d` and at a fixed
stage `n`, the `MonotoneOn` statements for the free-energy density in each parameter of the
record `⟨J, h, β⟩` separately: in the coupling and in the field on `Set.Ici 0`, and in the
inverse temperature on `Set.Ioi 0`. In each statement the frozen parameters carry their
ferromagnetic signs, and no condition on the stage volume is imposed.
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

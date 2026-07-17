import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d freeEnergyAlongExhaustion cubicExhaustion trivial-slice wrappers

Narrow child module for three ℤ^d
`freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_{beta_zero,zero_params,J_zero}`
trivial-slice wrappers extracted from `FreeEnergySpecialCasesAlongEx.lean`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d freeEnergyAlongExhaustion β=0 per-stage**: `= log 2`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_beta_zero
    (d : ℕ) (J h : ℝ) (n : ℕ)
    (hne : ((Ambient.cubicExhaustion d).volume n).Nonempty) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h, 0⟩ : IsingParams ℝ) n
      = Real.log 2 :=
  freeEnergyAlongExhaustion_beta_zero (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J h n hne

/-- **ℤ^d freeEnergyAlongExhaustion J=h=0 per-stage**: `= log 2`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_zero_params
    (d : ℕ) (β : ℝ) (n : ℕ)
    (hne : ((Ambient.cubicExhaustion d).volume n).Nonempty) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ) n
      = Real.log 2 :=
  freeEnergyAlongExhaustion_zero_params (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) β n hne

/-- **ℤ^d freeEnergyAlongExhaustion J=0 per-stage**: `= log(2·cosh(β·h))`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_J_zero
    (d : ℕ) (h β : ℝ) (n : ℕ)
    (hne : ((Ambient.cubicExhaustion d).volume n).Nonempty) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨0, h, β⟩ : IsingParams ℝ) n
      = Real.log (2 * Real.cosh (β * h)) :=
  freeEnergyAlongExhaustion_J_zero (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) h β n hne

end Ambient
end IsingModel

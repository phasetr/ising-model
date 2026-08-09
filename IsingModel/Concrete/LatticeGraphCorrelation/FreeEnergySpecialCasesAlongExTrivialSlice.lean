import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d per-stage free-energy trivial slices

Concrete `latticeGraph d` closed forms for the free energy at one stage of an arbitrary
`Ambient.Exhaustion` of `Fin d → ℤ`. At vanishing inverse temperature, and at vanishing
coupling and field together, the value is `Real.log 2`; at vanishing coupling and
unrestricted field it is `Real.log (2 * Real.cosh (β * h))`. Nonemptiness of the volume at
that stage is the only hypothesis of each, and no instance argument is taken.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d freeEnergyAlongExhaustion β=0 per-stage** (any-Exhaustion):
`= log 2`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_beta_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J h : ℝ) (n : ℕ)
    (hne : (Λ.volume n).Nonempty) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ) n
      = Real.log 2 :=
  freeEnergyAlongExhaustion_beta_zero (IsingModel.latticeGraph d) Λ J h n hne

/-- **ℤ^d freeEnergyAlongExhaustion J=h=0 per-stage** (any-Exhaustion):
`= log 2`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_zero_params
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (β : ℝ) (n : ℕ)
    (hne : (Λ.volume n).Nonempty) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) n
      = Real.log 2 :=
  freeEnergyAlongExhaustion_zero_params (IsingModel.latticeGraph d) Λ β n hne

/-- **ℤ^d freeEnergyAlongExhaustion J=0 per-stage** (any-Exhaustion):
`= log(2·cosh(β·h))`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ) (n : ℕ)
    (hne : (Λ.volume n).Nonempty) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) n
      = Real.log (2 * Real.cosh (β * h)) :=
  freeEnergyAlongExhaustion_J_zero (IsingModel.latticeGraph d) Λ h β n hne

end Ambient
end IsingModel

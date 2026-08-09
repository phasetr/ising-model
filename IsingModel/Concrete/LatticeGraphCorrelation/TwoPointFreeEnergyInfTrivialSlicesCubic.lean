import IsingModel.AmbientLatticeSum.TrivialSlices
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# The ℤ^d infinite-volume free energy along the cubic exhaustion, at degenerate records

Concrete `IsingModel.latticeGraph d` statements along `Ambient.cubicExhaustion d`, at
parameter records that switch part of the interaction off. At zero inverse temperature, and
separately at vanishing coupling and vanishing external field together, the value is
`Real.log 2`; at vanishing coupling alone it is `Real.log (2 * Real.cosh (β * h))`.

None of these takes a hypothesis, and each takes exactly one instance argument,
`Nonempty (Fin d → ℤ)`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d freeEnergyInfinite at β = 0**: `= log 2`. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_beta_zero
    (d : ℕ) [Nonempty (Fin d → ℤ)] (J h : ℝ) :
    freeEnergyInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h, 0⟩ : IsingParams ℝ)
      = Real.log 2 :=
  freeEnergyInfinite_beta_zero_of_nonempty (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J h

/-- **ℤ^d freeEnergyInfinite at J = h = 0**: `= log 2`. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_zero_params
    (d : ℕ) [Nonempty (Fin d → ℤ)] (β : ℝ) :
    freeEnergyInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      = Real.log 2 :=
  freeEnergyInfinite_zero_params_of_nonempty (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) β

/-- **ℤ^d freeEnergyInfinite at J = 0**: `= log(2 cosh(β·h))`. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_J_zero
    (d : ℕ) [Nonempty (Fin d → ℤ)] (h β : ℝ) :
    freeEnergyInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨0, h, β⟩ : IsingParams ℝ)
      = Real.log (2 * Real.cosh (β * h)) :=
  freeEnergyInfinite_J_zero_of_nonempty (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) h β

end Ambient
end IsingModel

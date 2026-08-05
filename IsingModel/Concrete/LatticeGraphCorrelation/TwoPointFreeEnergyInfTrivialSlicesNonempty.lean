import IsingModel.AmbientLatticeSum.TrivialSlices
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d `freeEnergyInfinite_latticeGraph_*` Nonempty trivial-slice wrappers

Narrow child module for three ℤ^d
`freeEnergyInfinite_latticeGraph_*` unconditional trivial-slice
wrappers:

* `freeEnergyInfinite_latticeGraph_beta_zero` (`= log 2`),
* `freeEnergyInfinite_latticeGraph_zero_params` (`= log 2`),
* `freeEnergyInfinite_latticeGraph_J_zero` (`= log(2 cosh(β·h))`).

Each result is a thin pass-through of the ambient
`Ambient.freeEnergyInfinite_*_of_nonempty` lemma at
`G := IsingModel.latticeGraph d` (under `[Nonempty (Fin d → ℤ)]`).
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d freeEnergyInfinite at β = 0** (any-Exhaustion): `= log 2`. -/
theorem freeEnergyInfinite_latticeGraph_beta_zero
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J h : ℝ) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ)
      = Real.log 2 :=
  freeEnergyInfinite_beta_zero_of_nonempty (IsingModel.latticeGraph d) Λ J h

/-- **ℤ^d freeEnergyInfinite at J = h = 0** (any-Exhaustion): `= log 2`. -/
theorem freeEnergyInfinite_latticeGraph_zero_params
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (Λ : Ambient.Exhaustion (Fin d → ℤ)) (β : ℝ) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ)
      = Real.log 2 :=
  freeEnergyInfinite_zero_params_of_nonempty (IsingModel.latticeGraph d) Λ β

/-- **ℤ^d freeEnergyInfinite at J = 0** (any-Exhaustion): `= log(2 cosh(β·h))`. -/
theorem freeEnergyInfinite_latticeGraph_J_zero
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ)
      = Real.log (2 * Real.cosh (β * h)) :=
  freeEnergyInfinite_J_zero_of_nonempty (IsingModel.latticeGraph d) Λ h β

end Ambient

end IsingModel

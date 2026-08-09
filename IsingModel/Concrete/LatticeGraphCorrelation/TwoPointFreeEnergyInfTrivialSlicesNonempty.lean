import IsingModel.AmbientLatticeSum.TrivialSlices
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# The ℤ^d infinite-volume free energy along any exhaustion, at degenerate records

Concrete `IsingModel.latticeGraph d` statements at an arbitrary `Ambient.Exhaustion` of
`Fin d → ℤ`, at parameter records that switch part of the interaction off. What
distinguishes them from their cubic-exhaustion counterparts is the arbitrary exhaustion,
not the `Nonempty` condition the module name records, which both carry.

At zero inverse temperature, and separately at vanishing coupling and vanishing external
field together, the value is `Real.log 2`; at vanishing coupling alone it is
`Real.log (2 * Real.cosh (β * h))`. None of these takes a hypothesis, and each takes
exactly one instance argument, `Nonempty (Fin d → ℤ)`.
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

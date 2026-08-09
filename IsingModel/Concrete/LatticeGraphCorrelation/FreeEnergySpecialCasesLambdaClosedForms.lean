import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d finite-volume free-energy closed forms on the trivial slices

Concrete `latticeGraph d` closed forms for the free energy on a fixed finite volume. At
vanishing coupling and unrestricted field the value is `Real.log (2 * Real.cosh (β * h))`; at
vanishing inverse temperature, and at vanishing coupling and field together, it is
`Real.log 2`. Nonemptiness of the volume is the only hypothesis of each, and no instance
argument is taken.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d freeEnergyΛ closed form at `J = 0`**:
for nonempty `Λ` and any `h, β`,
`freeEnergyΛ ⟨0, h, β⟩ = log(2·cosh(β·h))`. Concrete specialization of
`freeEnergyΛ_J_zero`. -/
theorem freeEnergyΛ_latticeGraph_J_zero
    (d : ℕ) {Λ : Finset (Fin d → ℤ)} (hne : Λ.Nonempty) (h β : ℝ) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ (⟨0, h, β⟩ : IsingParams ℝ)
      = Real.log (2 * Real.cosh (β * h)) :=
  freeEnergyΛ_J_zero (IsingModel.latticeGraph d) hne h β

/-- **ℤ^d freeEnergyΛ closed form at `β = 0`**:
for nonempty `Λ` and any `J, h`,
`freeEnergyΛ ⟨J, h, 0⟩ = log 2`. Concrete specialization of
`freeEnergyΛ_beta_zero`. -/
theorem freeEnergyΛ_latticeGraph_beta_zero
    (d : ℕ) {Λ : Finset (Fin d → ℤ)} (hne : Λ.Nonempty) (J h : ℝ) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ (⟨J, h, 0⟩ : IsingParams ℝ)
      = Real.log 2 :=
  freeEnergyΛ_beta_zero (IsingModel.latticeGraph d) hne J h

/-- **ℤ^d freeEnergyΛ closed form at `J = 0, h = 0`**:
for nonempty `Λ` and any `β`,
`freeEnergyΛ ⟨0, 0, β⟩ = log 2`. Concrete specialization of
`freeEnergyΛ_zero_params`. -/
theorem freeEnergyΛ_latticeGraph_zero_params
    (d : ℕ) {Λ : Finset (Fin d → ℤ)} (hne : Λ.Nonempty) (β : ℝ) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ (⟨0, 0, β⟩ : IsingParams ℝ)
      = Real.log 2 :=
  freeEnergyΛ_zero_params (IsingModel.latticeGraph d) hne β

end Ambient

end IsingModel

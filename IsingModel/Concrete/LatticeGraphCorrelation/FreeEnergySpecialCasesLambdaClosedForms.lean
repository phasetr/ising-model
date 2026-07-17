import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d `freeEnergyΛ_latticeGraph` closed-form wrappers (J = 0, β = 0)

Narrow child module for 3 ℤ^d `freeEnergyΛ_latticeGraph` closed-form
wrappers extracted from `FreeEnergySpecialCasesLambda.lean`:

* `freeEnergyΛ_latticeGraph_J_zero`,
* `freeEnergyΛ_latticeGraph_beta_zero`,
* `freeEnergyΛ_latticeGraph_zero_params`.

Each result is a thin pass-through of the corresponding ambient
`freeEnergyΛ_{J_zero,beta_zero,zero_params}` lemma at
`G := IsingModel.latticeGraph d`. The theorem names are unchanged
from the former `FreeEnergySpecialCasesLambda` declarations.
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

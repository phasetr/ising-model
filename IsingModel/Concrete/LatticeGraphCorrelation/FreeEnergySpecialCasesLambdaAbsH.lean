import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d freeEnergyΛ |h|-symmetry / monotonicity wrappers

Narrow child module for three ℤ^d
`freeEnergyΛ_latticeGraph_{neg_h,eq_abs_h,monotone_abs_h}` wrappers
extracted from `FreeEnergySpecialCasesLambda.lean`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d freeEnergyΛ h-evenness**:
`freeEnergyΛ ⟨J,-h,β⟩ = freeEnergyΛ ⟨J,h,β⟩` on any ℤ^d-vertex Finset.
Concrete specialization of `freeEnergyΛ_neg_h`. -/
theorem freeEnergyΛ_latticeGraph_neg_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ (⟨J, -h, β⟩ : IsingParams ℝ)
      = freeEnergyΛ (IsingModel.latticeGraph d) Λ (⟨J, h, β⟩ : IsingParams ℝ) :=
  freeEnergyΛ_neg_h (IsingModel.latticeGraph d) Λ J h β

/-- **ℤ^d freeEnergyΛ `|h|`-rewrite**:
`freeEnergyΛ ⟨J,h,β⟩ = freeEnergyΛ ⟨J,|h|,β⟩`. Concrete specialization of
`freeEnergyΛ_eq_abs_h`. -/
theorem freeEnergyΛ_latticeGraph_eq_abs_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ (⟨J, h, β⟩ : IsingParams ℝ)
      = freeEnergyΛ (IsingModel.latticeGraph d) Λ
          (⟨J, |h|, β⟩ : IsingParams ℝ) :=
  freeEnergyΛ_eq_abs_h (IsingModel.latticeGraph d) Λ J h β

/-- **ℤ^d freeEnergyΛ ferromagnetic `|h|`-monotonicity**:
for `J ≥ 0`, `β > 0` and `|h₁| ≤ |h₂|`,
`freeEnergyΛ ⟨J, h₁, β⟩ ≤ freeEnergyΛ ⟨J, h₂, β⟩`. Concrete specialization
of `freeEnergyΛ_monotone_abs_h`. -/
theorem freeEnergyΛ_latticeGraph_monotone_abs_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ (⟨J, h₁, β⟩ : IsingParams ℝ)
      ≤ freeEnergyΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h₂, β⟩ : IsingParams ℝ) :=
  freeEnergyΛ_monotone_abs_h (IsingModel.latticeGraph d) Λ J β hJ hβ hh

end Ambient
end IsingModel

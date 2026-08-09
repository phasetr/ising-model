import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d finite-volume free energy in the external field and its absolute value

Concrete `latticeGraph d` statements about the free energy on a fixed finite volume as the
external field varies. Reversing the sign of the field leaves it unchanged, so its value at
`h` equals its value at `|h|`, and each of those identities is hypothesis-free. Monotonicity
in the absolute field — the value at `h₁` is at most the value at `h₂` whenever `|h₁| ≤ |h₂|`
— assumes `0 ≤ J` and `0 < β` in addition. No instance argument is taken.
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

import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d finite-volume free-energy monotonicity in one parameter

Concrete `latticeGraph d` statements that the free energy on a fixed finite volume, as a
function of one parameter of the record with the others held fixed, is monotone on a ray.
Monotonicity in the coupling on `Set.Ici 0` assumes `0 ≤ h` and `0 < β`; monotonicity in the
external field on `Set.Ici 0` assumes `0 ≤ J` and `0 < β`; monotonicity in the inverse
temperature on `Set.Ioi 0` assumes `0 ≤ J` and `0 ≤ h`. No instance argument is taken.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d freeEnergyΛ J-monotonicity**: for fixed `h ≥ 0`, `β > 0`,
`freeEnergyΛ` is monotone in `J` on `[0, ∞)`. Concrete specialization
of `freeEnergyΛ_monotone_J`. -/
theorem freeEnergyΛ_latticeGraph_monotone_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β) :
    MonotoneOn
      (fun J : ℝ => freeEnergyΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ))
      (Set.Ici 0) :=
  freeEnergyΛ_monotone_J (IsingModel.latticeGraph d) Λ hh hβ

/-- **ℤ^d freeEnergyΛ h-monotonicity**: for fixed `J ≥ 0`, `β > 0`,
`freeEnergyΛ` is monotone in `h` on `[0, ∞)`. Concrete specialization
of `freeEnergyΛ_monotone_h`. -/
theorem freeEnergyΛ_latticeGraph_monotone_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) :
    MonotoneOn
      (fun h : ℝ => freeEnergyΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ))
      (Set.Ici 0) :=
  freeEnergyΛ_monotone_h (IsingModel.latticeGraph d) Λ hJ hβ

/-- **ℤ^d freeEnergyΛ β-monotonicity**: for fixed `J ≥ 0`, `h ≥ 0`,
`freeEnergyΛ` is monotone in `β` on `(0, ∞)`. Concrete specialization
of `freeEnergyΛ_monotone_beta`. -/
theorem freeEnergyΛ_latticeGraph_monotone_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h) :
    MonotoneOn
      (fun β : ℝ => freeEnergyΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ))
      (Set.Ioi 0) :=
  freeEnergyΛ_monotone_beta (IsingModel.latticeGraph d) Λ hJ hh

end Ambient
end IsingModel

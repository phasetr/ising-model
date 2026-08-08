import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete ℤ^d `freeEnergyΛ` special-case wrappers

Instantiates the abstract `freeEnergyΛ_*` special-case estimates at
`IsingModel.latticeGraph d`, so ℤ^d arguments can quote the ferromagnetic lower bounds
without carrying the ambient graph as a variable.
-/

namespace IsingModel
namespace Ambient

/-! ### ℤ^d `freeEnergyΛ` wrappers -/

/-- **ℤ^d freeEnergyΛ ≥ log(2 cosh βh)** (ferromagnetic, nonempty Λ). -/
theorem freeEnergyΛ_latticeGraph_ge_log_two_cosh
    (d : ℕ) {Λ : Finset (Fin d → ℤ)} (hne : Λ.Nonempty)
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) :
    Real.log (2 * Real.cosh (β * h))
      ≤ freeEnergyΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ) :=
  freeEnergyΛ_ge_log_two_cosh (IsingModel.latticeGraph d) hne hJ hh hβ

/-- **ℤ^d freeEnergyΛ ≥ log 2** (ferromagnetic, nonempty Λ). -/
theorem freeEnergyΛ_latticeGraph_ge_log_two
    (d : ℕ) {Λ : Finset (Fin d → ℤ)} (hne : Λ.Nonempty)
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) :
    Real.log 2
      ≤ freeEnergyΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ) :=
  freeEnergyΛ_ge_log_two (IsingModel.latticeGraph d) hne hJ hh hβ

/-- **ℤ^d freeEnergyΛ ≥ 0** (ferromagnetic, nonempty Λ). -/
theorem freeEnergyΛ_latticeGraph_nonneg
    (d : ℕ) {Λ : Finset (Fin d → ℤ)} (hne : Λ.Nonempty)
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    0 ≤ freeEnergyΛ (IsingModel.latticeGraph d) Λ p :=
  freeEnergyΛ_nonneg_of_ferromagnetic (IsingModel.latticeGraph d) hne p hf

end Ambient

end IsingModel

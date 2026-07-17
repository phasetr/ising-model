import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete ℤ^d `freeEnergyΛ` special-case wrappers

Narrow child module for the 12 ℤ^d `freeEnergyΛ_latticeGraph_*`
wrappers (`ge_log_two_cosh`, `ge_log_two`, `nonneg`, `J_zero`,
`beta_zero`, `zero_params`, `neg_h`, `eq_abs_h`, `monotone_abs_h`,
`monotone_J`, `monotone_h`, `monotone_beta`) extracted from
`FreeEnergySpecialCases.lean` in PR #2039. Each is a thin pass-through
to the corresponding abstract `freeEnergyΛ_*` lemma at
`latticeGraph d`. The theorem names are unchanged from the former
`FreeEnergySpecialCases` declarations.
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

/-! ## Moved: freeEnergyΛ closed-form wrappers (J = 0, β = 0)

The three `freeEnergyΛ_latticeGraph_{J_zero,beta_zero,zero_params}`
closed-form wrappers now live in
`FreeEnergySpecialCasesLambdaClosedForms.lean`. -/


/-! ## Moved: freeEnergyΛ |h|-symmetry / monotonicity wrappers

The three wrappers
`freeEnergyΛ_latticeGraph_neg_h`,
`freeEnergyΛ_latticeGraph_eq_abs_h`,
`freeEnergyΛ_latticeGraph_monotone_abs_h` now live in
`FreeEnergySpecialCasesLambdaAbsH.lean`. -/


/-! ## Moved: freeEnergyΛ monotonicity wrappers

The three `freeEnergyΛ_latticeGraph_monotone_{J,h,beta}` wrappers
now live in `FreeEnergySpecialCasesLambdaMonotone.lean`. -/




end Ambient

end IsingModel

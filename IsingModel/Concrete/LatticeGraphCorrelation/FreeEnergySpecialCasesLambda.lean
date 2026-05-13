import IsingModel.Concrete.LatticeGraphBED
import IsingModel.AmbientLattice.SpecialCases.FreeEnergy

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

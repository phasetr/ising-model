import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete ℤ^d finite-volume `freeEnergy` special-case wrappers

Narrow child module for the 16 ℤ^d `freeEnergy_*_latticeGraph`
finite-volume wrappers (monotone in `h`/`J`/`β`/`|h|`, trivial slices
`zero_params`/`beta_zero`/`J_zero`/`neg_h`/`eq_abs_h`,
`eq_bot_at_J_zero`, `ge_log_two_cosh`, `bot_h_zero`,
`card_mul_freeEnergy_eq_log_partitionFunction`,
`ge_log_two_of_ferromagnetic`, `nonneg_of_ferromagnetic`, `bot`)
extracted from `FreeEnergySpecialCases.lean` in PR #2040. Each is a
thin pass-through to the corresponding abstract `IsingModel.freeEnergy*`
lemma on `Ambient.inducedGraph (latticeGraph d) Λ`. The theorem names
are unchanged from the former `FreeEnergySpecialCases` declarations.
-/

namespace IsingModel
namespace Ambient

/-! ### ℤ^d finite-volume free-energy special cases -/

/-! ## Moved: ℤ^d freeEnergy monotone (h, J, β) wrappers

The three wrappers
`freeEnergy_monotone_h_latticeGraph`,
`freeEnergy_monotone_J_latticeGraph`,
`freeEnergy_monotone_beta_latticeGraph` now live in
`FreeEnergySpecialCasesFiniteVolMonotone.lean`. -/


/-! ## Moved: ℤ^d freeEnergy finite-volume closed-form wrappers

The three `freeEnergy_{zero_params,beta_zero,J_zero}_latticeGraph`
trivial-slice closed-form wrappers now live in
`FreeEnergySpecialCasesFiniteVolClosedForms.lean`. -/


/-! ## Moved: freeEnergy h-symmetry wrappers

The three wrappers `freeEnergy_{neg_h,eq_abs_h,monotone_abs_h}_latticeGraph`
now live in `FreeEnergySpecialCasesFiniteVolAbsH.lean`. -/

/-- **ℤ^d freeEnergy_eq_bot_at_J_zero at Λ-induced**. -/
theorem freeEnergy_eq_bot_at_J_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ) :
    IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, h, β⟩ : IsingParams ℝ)
      = IsingModel.freeEnergy (⊥ : SimpleGraph (↑Λ : Type _))
          (⟨0, h, β⟩ : IsingParams ℝ) :=
  IsingModel.freeEnergy_eq_bot_at_J_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β

/-- **ℤ^d freeEnergy_ge_log_two_cosh at Λ-induced** (ferromagnetic). -/
theorem freeEnergy_ge_log_two_cosh_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β)
    (hne : 0 < Fintype.card (↑Λ : Type _)) :
    Real.log (2 * Real.cosh (β * h))
      ≤ IsingModel.freeEnergy
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, h, β⟩ : IsingParams ℝ) :=
  IsingModel.freeEnergy_ge_log_two_cosh
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hJ hh hβ hne

/-- **ℤ^d freeEnergy_bot_h_zero at Λ-induced**:
`freeEnergy (⊥ : SimpleGraph ↑Λ) ⟨J, 0, β⟩ = log 2`. -/
theorem freeEnergy_bot_h_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hne : 0 < Fintype.card (↑Λ : Type _)) :
    IsingModel.freeEnergy (⊥ : SimpleGraph (↑Λ : Type _))
        (⟨J, 0, β⟩ : IsingParams ℝ) = Real.log 2 :=
  IsingModel.freeEnergy_bot_h_zero J β hne

/-! ## Moved: ℤ^d Λ-induced ferromagnetic / bot wrappers

The four wrappers
`card_mul_freeEnergy_eq_log_partitionFunction_latticeGraph`,
`freeEnergy_ge_log_two_of_ferromagnetic_latticeGraph`,
`freeEnergy_nonneg_of_ferromagnetic_latticeGraph`,
`freeEnergy_bot_latticeGraph`
now live in `FreeEnergySpecialCasesFiniteVolFerromagnetic.lean`. -/



end Ambient

end IsingModel

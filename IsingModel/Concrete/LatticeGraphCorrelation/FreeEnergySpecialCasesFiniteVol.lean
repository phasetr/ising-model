import IsingModel.Concrete.LatticeGraphBED
import IsingModel.AmbientLattice.SpecialCases.FreeEnergy

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

/-- **ℤ^d freeEnergy_monotone_h direct** (Λ-induced, ferromagnetic). -/
theorem freeEnergy_monotone_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    MonotoneOn (IsingModel.freeEnergyH
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β) (Set.Ici 0) :=
  IsingModel.freeEnergy_monotone_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β hJ hβ

/-- **ℤ^d freeEnergy_monotone_J direct** (Λ-induced, ferromagnetic). -/
theorem freeEnergy_monotone_J_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ) (hh : 0 ≤ h) (hβ : 0 < β) :
    MonotoneOn (IsingModel.freeEnergyJ
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β) (Set.Ici 0) :=
  IsingModel.freeEnergy_monotone_J
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β hh hβ

/-- **ℤ^d freeEnergy_monotone_beta direct** (Λ-induced, ferromagnetic). -/
theorem freeEnergy_monotone_beta_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J : ℝ) (hJ : 0 ≤ J) (h : ℝ) (hh : 0 ≤ h) :
    MonotoneOn
      (fun β : ℝ => IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) ⟨J, h, β⟩)
      (Set.Ioi 0) :=
  IsingModel.freeEnergy_monotone_beta
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J hJ h hh

/-- **ℤ^d freeEnergy_zero_params at Λ-induced**:
`freeEnergy ⟨0, 0, β⟩ = log 2` for nonempty Λ. -/
theorem freeEnergy_zero_params_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (β : ℝ)
    (hne : 0 < Fintype.card (↑Λ : Type _)) :
    IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, 0, β⟩ : IsingParams ℝ) = Real.log 2 :=
  IsingModel.freeEnergy_zero_params
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) β hne

/-- **ℤ^d freeEnergy_beta_zero at Λ-induced**:
`freeEnergy ⟨J, h, 0⟩ = log 2` for nonempty Λ. -/
theorem freeEnergy_beta_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h : ℝ)
    (hne : 0 < Fintype.card (↑Λ : Type _)) :
    IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, h, 0⟩ : IsingParams ℝ) = Real.log 2 :=
  IsingModel.freeEnergy_beta_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h hne

/-- **ℤ^d freeEnergy_J_zero at Λ-induced**:
`freeEnergy ⟨0, h, β⟩ = log(2·cosh(β·h))` for nonempty Λ. -/
theorem freeEnergy_J_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ)
    (hne : 0 < Fintype.card (↑Λ : Type _)) :
    IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, h, β⟩ : IsingParams ℝ)
      = Real.log (2 * Real.cosh (β * h)) :=
  IsingModel.freeEnergy_J_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β hne

/-- **ℤ^d freeEnergy_neg_h at Λ-induced**. -/
theorem freeEnergy_neg_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ) :
    IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, -h, β⟩ : IsingParams ℝ)
      = IsingModel.freeEnergy
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, h, β⟩ : IsingParams ℝ) :=
  IsingModel.freeEnergy_neg_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β

/-- **ℤ^d freeEnergy_eq_abs_h at Λ-induced**. -/
theorem freeEnergy_eq_abs_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ) :
    IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, h, β⟩ : IsingParams ℝ)
      = IsingModel.freeEnergy
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, |h|, β⟩ : IsingParams ℝ) :=
  IsingModel.freeEnergy_eq_abs_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β

/-- **ℤ^d freeEnergy_monotone_abs_h at Λ-induced** (ferromagnetic). -/
theorem freeEnergy_monotone_abs_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) :
    IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, h₁, β⟩ : IsingParams ℝ)
      ≤ IsingModel.freeEnergy
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, h₂, β⟩ : IsingParams ℝ) :=
  IsingModel.freeEnergy_monotone_abs_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β hJ hβ hh

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

/-- **ℤ^d card_mul_freeEnergy_eq_log_partitionFunction direct** (Λ-induced):
`|ι|·f = log Z` for nonempty Λ. -/
theorem card_mul_freeEnergy_eq_log_partitionFunction_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (hne : 0 < Fintype.card (↑Λ : Type _)) :
    (Fintype.card (↑Λ : Type _) : ℝ)
      * IsingModel.freeEnergy
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p
      = Real.log (IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p) :=
  IsingModel.card_mul_freeEnergy_eq_log_partitionFunction
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hne

/-- **ℤ^d freeEnergy_ge_log_two_of_ferromagnetic at Λ-induced**:
`log 2 ≤ freeEnergy Λ p` for ferromagnetic `p` and nonempty Λ. -/
theorem freeEnergy_ge_log_two_of_ferromagnetic_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (hne : 0 < Fintype.card (↑Λ : Type _)) :
    Real.log 2
      ≤ IsingModel.freeEnergy
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p :=
  IsingModel.freeEnergy_ge_log_two_of_ferromagnetic
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hf hne

/-- **ℤ^d freeEnergy_nonneg_of_ferromagnetic at Λ-induced**:
`0 ≤ freeEnergy G Λ p` for ferromagnetic `p` and nonempty Λ. -/
theorem freeEnergy_nonneg_of_ferromagnetic_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (hne : 0 < Fintype.card (↑Λ : Type _)) :
    0 ≤ IsingModel.freeEnergy
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p :=
  IsingModel.freeEnergy_nonneg_of_ferromagnetic
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hf hne

/-- **ℤ^d freeEnergy_bot at Λ-induced type**: `freeEnergy ⊥ = log(2 cosh(βh))`. -/
theorem freeEnergy_bot_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (hne : 0 < Fintype.card (↑Λ : Type _)) :
    IsingModel.freeEnergy (⊥ : SimpleGraph (↑Λ : Type _)) p
      = Real.log (2 * Real.cosh (p.β * p.h)) :=
  IsingModel.freeEnergy_bot p hne

end Ambient

end IsingModel

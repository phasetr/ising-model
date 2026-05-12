import IsingModel.Concrete.LatticeGraphBED
import IsingModel.AmbientLattice.SpecialCases.FreeEnergy

/-!
# Concrete free-energy special-case wrappers

Narrow child module for concrete `latticeGraph` free-energy closed forms,
monotonicity wrappers, h-symmetry, and bottom-graph comparison wrappers. The
theorem names are the same as the former legacy declarations, but callers can
now avoid importing the monolithic concrete legacy module.
-/

namespace IsingModel
namespace Ambient

/-! ### ℤ^d free-energy infinite-volume and along-exhaustion wrappers -/

/-- **ℤ^d `freeEnergyInfinite_beta_zero`** (any-Exhaustion, ∀ n nonempty):
`freeEnergyInfinite ⟨J, h, 0⟩ = log 2`. -/
theorem freeEnergyInfinite_latticeGraph_beta_zero_forall_nonempty
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J h : ℝ)
    (hne : ∀ n, (Λ.volume n).Nonempty) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ)
      = Real.log 2 :=
  freeEnergyInfinite_beta_zero (IsingModel.latticeGraph d) Λ J h hne

/-- **ℤ^d `freeEnergyInfinite_zero_params`** (any-Exhaustion, ∀ n nonempty):
`freeEnergyInfinite ⟨0, 0, β⟩ = log 2`. -/
theorem freeEnergyInfinite_latticeGraph_zero_params_forall_nonempty
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (β : ℝ)
    (hne : ∀ n, (Λ.volume n).Nonempty) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ)
      = Real.log 2 :=
  freeEnergyInfinite_zero_params (IsingModel.latticeGraph d) Λ β hne

/-- **ℤ^d `freeEnergyInfinite_eq_bot_at_J_zero`** (any-Exhaustion):
at `J = 0` the ∞-vol free energy equals the `⊥`-graph value. -/
theorem freeEnergyInfinite_latticeGraph_eq_bot_at_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
      (⊥ : SimpleGraph (Fin d → ℤ)) (Λ.volume n)).edgeSet]
    (h β : ℝ) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ)
      = freeEnergyInfinite (⊥ : SimpleGraph (Fin d → ℤ)) Λ
          (⟨0, h, β⟩ : IsingParams ℝ) :=
  freeEnergyInfinite_eq_bot_at_J_zero (IsingModel.latticeGraph d) Λ h β

/-- **ℤ^d `freeEnergyAlongExhaustion_eq_bot_at_J_zero`** (any-Exhaustion):
at `J = 0` the per-stage free energy equals the `⊥`-graph value. -/
theorem freeEnergyAlongExhaustion_latticeGraph_eq_bot_at_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
      (⊥ : SimpleGraph (Fin d → ℤ)) (Λ.volume n)).edgeSet]
    (h β : ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) n
      = freeEnergyAlongExhaustion (⊥ : SimpleGraph (Fin d → ℤ)) Λ
          (⟨0, h, β⟩ : IsingParams ℝ) n :=
  freeEnergyAlongExhaustion_eq_bot_at_J_zero
    (IsingModel.latticeGraph d) Λ h β n

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

/-! ## Moved: ℤ^d `freeEnergyΛ` special-case wrappers

The 13 ℤ^d `freeEnergyΛ_latticeGraph_*` wrappers
(`ge_log_two_cosh`, `ge_log_two`, `nonneg`, `J_zero`, `beta_zero`,
`zero_params`, `neg_h`, `eq_abs_h`, `monotone_abs_h`, `monotone_J`,
`monotone_h`, `monotone_beta`) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.FreeEnergySpecialCasesLambda`.
The legacy import path is preserved by re-importing the new child.
-/

/-! ### ℤ^d `freeEnergyAlongExhaustion` wrappers -/

/-- **ℤ^d freeEnergyAlongExhaustion h-evenness** per stage:
`f(Λ_n; J,-h,β) = f(Λ_n; J,h,β)`. Concrete specialization of
`freeEnergyAlongExhaustion_neg_h`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_neg_h
    (d : ℕ) (J h β : ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, -h, β⟩ : IsingParams ℝ) n
      = freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, h, β⟩ : IsingParams ℝ) n :=
  freeEnergyAlongExhaustion_neg_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J h β n

/-- **ℤ^d freeEnergyAlongExhaustion `|h|`-rewrite** per stage. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_eq_abs_h
    (d : ℕ) (J h β : ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h, β⟩ : IsingParams ℝ) n
      = freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, |h|, β⟩ : IsingParams ℝ) n :=
  freeEnergyAlongExhaustion_eq_abs_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J h β n

/-- **ℤ^d freeEnergyAlongExhaustion ferromagnetic `|h|`-monotonicity**
per stage. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_monotone_abs_h
    (d : ℕ) (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h₁, β⟩ : IsingParams ℝ) n
      ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, h₂, β⟩ : IsingParams ℝ) n :=
  freeEnergyAlongExhaustion_monotone_abs_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J β hJ hβ hh n

/-- **ℤ^d freeEnergyAlongExhaustion h-evenness** per stage (any Exhaustion). -/
theorem freeEnergyAlongExhaustion_latticeGraph_neg_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h β : ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, -h, β⟩ : IsingParams ℝ) n
      = freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ) n :=
  freeEnergyAlongExhaustion_neg_h (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d freeEnergyAlongExhaustion `|h|`-rewrite** per stage (any Exhaustion). -/
theorem freeEnergyAlongExhaustion_latticeGraph_eq_abs_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h β : ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) n
      = freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, |h|, β⟩ : IsingParams ℝ) n :=
  freeEnergyAlongExhaustion_eq_abs_h (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d freeEnergyAlongExhaustion ferromagnetic `|h|`-monotonicity**
per stage (any Exhaustion). -/
theorem freeEnergyAlongExhaustion_latticeGraph_monotone_abs_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h₁, β⟩ : IsingParams ℝ) n
      ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h₂, β⟩ : IsingParams ℝ) n :=
  freeEnergyAlongExhaustion_monotone_abs_h (IsingModel.latticeGraph d) Λ
    J β hJ hβ hh n

/-- **ℤ^d freeEnergyAlongExhaustion β=0 per-stage** (any-Exhaustion):
`= log 2`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_beta_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J h : ℝ) (n : ℕ)
    (hne : (Λ.volume n).Nonempty) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ) n
      = Real.log 2 :=
  freeEnergyAlongExhaustion_beta_zero (IsingModel.latticeGraph d) Λ J h n hne

/-- **ℤ^d freeEnergyAlongExhaustion J=h=0 per-stage** (any-Exhaustion):
`= log 2`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_zero_params
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (β : ℝ) (n : ℕ)
    (hne : (Λ.volume n).Nonempty) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) n
      = Real.log 2 :=
  freeEnergyAlongExhaustion_zero_params (IsingModel.latticeGraph d) Λ β n hne

/-- **ℤ^d freeEnergyAlongExhaustion J=0 per-stage** (any-Exhaustion):
`= log(2·cosh(β·h))`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ) (n : ℕ)
    (hne : (Λ.volume n).Nonempty) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) n
      = Real.log (2 * Real.cosh (β * h)) :=
  freeEnergyAlongExhaustion_J_zero (IsingModel.latticeGraph d) Λ h β n hne

/-- **ℤ^d freeEnergyAlongExhaustion β=0 per-stage**: `= log 2`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_beta_zero
    (d : ℕ) (J h : ℝ) (n : ℕ)
    (hne : ((Ambient.cubicExhaustion d).volume n).Nonempty) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h, 0⟩ : IsingParams ℝ) n
      = Real.log 2 :=
  freeEnergyAlongExhaustion_beta_zero (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J h n hne

/-- **ℤ^d freeEnergyAlongExhaustion J=h=0 per-stage**: `= log 2`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_zero_params
    (d : ℕ) (β : ℝ) (n : ℕ)
    (hne : ((Ambient.cubicExhaustion d).volume n).Nonempty) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ) n
      = Real.log 2 :=
  freeEnergyAlongExhaustion_zero_params (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) β n hne

/-- **ℤ^d freeEnergyAlongExhaustion J=0 per-stage**: `= log(2·cosh(β·h))`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_J_zero
    (d : ℕ) (h β : ℝ) (n : ℕ)
    (hne : ((Ambient.cubicExhaustion d).volume n).Nonempty) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨0, h, β⟩ : IsingParams ℝ) n
      = Real.log (2 * Real.cosh (β * h)) :=
  freeEnergyAlongExhaustion_J_zero (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) h β n hne

end Ambient
end IsingModel

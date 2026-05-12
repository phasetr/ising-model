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

/-! ## Moved: ℤ^d finite-volume `freeEnergy_*_latticeGraph` wrappers

The 16 ℤ^d finite-volume `freeEnergy_*_latticeGraph` wrappers
(monotone in `h`/`J`/`β`/`|h|`, trivial slices
`zero_params`/`beta_zero`/`J_zero`/`neg_h`/`eq_abs_h`,
`eq_bot_at_J_zero`, `ge_log_two_cosh`, `bot_h_zero`,
`card_mul_freeEnergy_eq_log_partitionFunction`,
`ge_log_two_of_ferromagnetic`, `nonneg_of_ferromagnetic`, `bot`)
now live in
`IsingModel.Concrete.LatticeGraphCorrelation.FreeEnergySpecialCasesFiniteVol`.
The legacy import path is preserved by re-importing the new child.
-/


/-! ## Moved: ℤ^d `freeEnergyΛ` special-case wrappers

The 12 ℤ^d `freeEnergyΛ_latticeGraph_*` wrappers
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

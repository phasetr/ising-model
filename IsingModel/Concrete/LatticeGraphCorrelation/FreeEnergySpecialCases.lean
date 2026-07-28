import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete free-energy special-case wrappers

Narrow child module for concrete `latticeGraph` free-energy closed forms,
monotonicity wrappers, h-symmetry, and bottom-graph comparison wrappers. The
theorem names are the same as the former declarations, but callers can
now avoid importing the monolithic concrete module.
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

/-! ## Moved: ℤ^d `freeEnergyΛ` special-case wrappers

The 12 ℤ^d `freeEnergyΛ_latticeGraph_*` wrappers
(`ge_log_two_cosh`, `ge_log_two`, `nonneg`, `J_zero`, `beta_zero`,
`zero_params`, `neg_h`, `eq_abs_h`, `monotone_abs_h`, `monotone_J`,
`monotone_h`, `monotone_beta`) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.FreeEnergySpecialCasesLambda`.
The earlier import path is preserved by re-importing the new child.
-/

end Ambient
end IsingModel

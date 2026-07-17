import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d freeEnergyAlongEx trivial-slice tendsto under eventually-nonempty

Narrow child module for three ℤ^d
`freeEnergyAlongExhaustion_latticeGraph_*_tendsto_of_eventually_nonempty`
wrappers extracted from `TwoPointFreeEnergyAlongExTendsto.lean`:

* `_J_zero_tendsto_of_eventually_nonempty`,
* `_beta_zero_tendsto_of_eventually_nonempty`,
* `_zero_params_tendsto_of_eventually_nonempty`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d freeEnergyAlongExhaustion Tendsto at J=0 under eventually-nonempty**
(any-Exhaustion). -/
theorem freeEnergyAlongExhaustion_latticeGraph_J_zero_tendsto_of_eventually_nonempty
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ)
    (hne : ∀ᶠ n in Filter.atTop, (Λ.volume n).Nonempty) :
    Filter.Tendsto
      (freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ))
      Filter.atTop (nhds (Real.log (2 * Real.cosh (β * h)))) :=
  freeEnergyAlongExhaustion_J_zero_tendsto_of_eventually_nonempty
    (IsingModel.latticeGraph d) Λ h β hne

/-- **ℤ^d freeEnergyAlongExhaustion Tendsto at β=0 under eventually-nonempty**
(any-Exhaustion). -/
theorem freeEnergyAlongExhaustion_latticeGraph_beta_zero_tendsto_of_eventually_nonempty
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J h : ℝ)
    (hne : ∀ᶠ n in Filter.atTop, (Λ.volume n).Nonempty) :
    Filter.Tendsto
      (freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ))
      Filter.atTop (nhds (Real.log 2)) :=
  freeEnergyAlongExhaustion_beta_zero_tendsto_of_eventually_nonempty
    (IsingModel.latticeGraph d) Λ J h hne

/-- **ℤ^d freeEnergyAlongExhaustion Tendsto at J=h=0 under eventually-nonempty**
(any-Exhaustion). -/
theorem freeEnergyAlongExhaustion_latticeGraph_zero_params_tendsto_of_eventually_nonempty
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (β : ℝ)
    (hne : ∀ᶠ n in Filter.atTop, (Λ.volume n).Nonempty) :
    Filter.Tendsto
      (freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ))
      Filter.atTop (nhds (Real.log 2)) :=
  freeEnergyAlongExhaustion_zero_params_tendsto_of_eventually_nonempty
    (IsingModel.latticeGraph d) Λ β hne

end Ambient
end IsingModel

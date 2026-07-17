import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d freeEnergyAlongExhaustion tendsto wrappers

Narrow child module for the 9 ℤ^d
`freeEnergyAlongExhaustion_latticeGraph_*_tendsto_*` convergence
wrappers (`J_zero_tendsto_of_hcard_add`, `beta_zero_tendsto_of_hcard_add`,
`tendsto_of_disjoint_tower`, `tendsto_of_disjointTowerHypotheses`,
`tendsto_of_superadditive`, `tendsto_of_eventually_const`,
`J_zero_tendsto_of_eventually_nonempty`,
`beta_zero_tendsto_of_eventually_nonempty`,
`zero_params_tendsto_of_eventually_nonempty`) extracted from
`TwoPointFreeEnergy.lean` in PR #2052. Each is a thin pass-through to
the corresponding abstract `freeEnergyAlongExhaustion_*_tendsto_*`
lemma at `IsingModel.latticeGraph d`. The theorem names are
unchanged from the former `TwoPointFreeEnergy` declarations.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d Fekete J=0 convergence with hcard_add** (any-Exhaustion): given
BED + additive card + non-degenerate base step, `freeEnergyAlongExhaustion
⟨0, h, β⟩` converges to `freeEnergyInfinite ⟨0, h, β⟩`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_J_zero_tendsto_of_hcard_add
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hcard_add : ∀ m n, (Λ.volume (m + n)).card
                          = (Λ.volume m).card + (Λ.volume n).card)
    (hcard_one : (Λ.volume 1).card ≠ 0) :
    Filter.Tendsto
      (freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ))
      Filter.atTop
      (nhds (freeEnergyInfinite (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ))) :=
  freeEnergyAlongExhaustion_J_zero_tendsto_of_hcard_add
    (IsingModel.latticeGraph d) Λ h β hBED hcard_add hcard_one

/-- **ℤ^d Fekete β=0 convergence with hcard_add** (any-Exhaustion). -/
theorem freeEnergyAlongExhaustion_latticeGraph_beta_zero_tendsto_of_hcard_add
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J h : ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hcard_add : ∀ m n, (Λ.volume (m + n)).card
                          = (Λ.volume m).card + (Λ.volume n).card)
    (hcard_one : (Λ.volume 1).card ≠ 0) :
    Filter.Tendsto
      (freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ))
      Filter.atTop
      (nhds (freeEnergyInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ))) :=
  freeEnergyAlongExhaustion_beta_zero_tendsto_of_hcard_add
    (IsingModel.latticeGraph d) Λ J h hBED hcard_add hcard_one

/-! ## Moved: tendsto disjoint_tower / super wrappers

The three wrappers
`freeEnergyAlongExhaustion_latticeGraph_tendsto_of_disjoint_tower`,
`freeEnergyAlongExhaustion_latticeGraph_tendsto_of_disjointTowerHypotheses`,
`freeEnergyAlongExhaustion_latticeGraph_tendsto_of_superadditive` now
live in `TwoPointFreeEnergyAlongExTendstoDisjointSuper.lean`. -/


/-- **ℤ^d generic tendsto helper**: if the stagewise
`freeEnergyAlongExhaustion` is eventually constantly `c`, it tends to `c`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_tendsto_of_eventually_const
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) {c : ℝ}
    (h : ∀ᶠ n in Filter.atTop,
      freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ p n = c) :
    Filter.Tendsto
      (freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ p)
      Filter.atTop (nhds c) :=
  freeEnergyAlongExhaustion_tendsto_of_eventually_const
    (IsingModel.latticeGraph d) Λ p h

/-! ## Moved: ℤ^d freeEnergyAlongEx tendsto under eventually-nonempty

The three wrappers
`freeEnergyAlongExhaustion_latticeGraph_J_zero_tendsto_of_eventually_nonempty`,
`freeEnergyAlongExhaustion_latticeGraph_beta_zero_tendsto_of_eventually_nonempty`,
`freeEnergyAlongExhaustion_latticeGraph_zero_params_tendsto_of_eventually_nonempty`
now live in `TwoPointFreeEnergyAlongExTendstoEventuallyNonempty.lean`. -/



end Ambient

end IsingModel

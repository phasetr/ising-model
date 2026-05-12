import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphCorrelation.Translation
import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.AmbientFKG
import IsingModel.AmbientLattice.SpecialCases.InfiniteVolume
import IsingModel.Concrete.LatticeGraphCorrelation.TwoPoint

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

/-- **ℤ^d Fekete-style convergence under disjoint-tower + BED** (any-Exhaustion):
if `|Λ.volume (m+n)| = |Λ.volume m| + |Λ.volume n|`, log Z is super-additive,
and BED holds, then `freeEnergyAlongExhaustion → freeEnergyInfinite`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_tendsto_of_disjoint_tower
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hcard_add : ∀ m n, (Λ.volume (m + n)).card
                          = (Λ.volume m).card + (Λ.volume n).card)
    (hsuper : ∀ m n,
        Real.log (partitionFunctionΛ (IsingModel.latticeGraph d)
            (Λ.volume m) p)
          + Real.log (partitionFunctionΛ (IsingModel.latticeGraph d)
              (Λ.volume n) p)
        ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d)
            (Λ.volume (m + n)) p))
    (hcard_one : (Λ.volume 1).card ≠ 0) :
    Filter.Tendsto
      (freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ p)
      Filter.atTop
      (nhds (freeEnergyInfinite (IsingModel.latticeGraph d) Λ p)) :=
  freeEnergyAlongExhaustion_tendsto_of_disjoint_tower
    (IsingModel.latticeGraph d) Λ p hBED hcard_add hsuper hcard_one

/-- **ℤ^d Fekete-style convergence under disjoint-tower + BED, bundled form**
(any-Exhaustion): same as `_of_disjoint_tower` but takes a
`DisjointTowerHypotheses` record. -/
theorem freeEnergyAlongExhaustion_latticeGraph_tendsto_of_disjointTowerHypotheses
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (h : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p) :
    Filter.Tendsto
      (freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ p)
      Filter.atTop
      (nhds (freeEnergyInfinite (IsingModel.latticeGraph d) Λ p)) :=
  freeEnergyAlongExhaustion_tendsto_of_disjointTowerHypotheses
    (IsingModel.latticeGraph d) Λ p hBED h

/-- **ℤ^d Fekete-style convergence under super-additivity**
(any-Exhaustion): if `|Λ.volume (m+n)| = |Λ.volume m| + |Λ.volume n|`,
log Z is super-additive on this additive grading, the range is bounded above,
and `|Λ.volume 1| ≠ 0`, then `freeEnergyAlongExhaustion → freeEnergyInfinite`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_tendsto_of_superadditive
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ)
    (hcard_add : ∀ m n, (Λ.volume (m + n)).card
                          = (Λ.volume m).card + (Λ.volume n).card)
    (hsuper : ∀ m n,
        Real.log (partitionFunctionΛ (IsingModel.latticeGraph d)
            (Λ.volume m) p)
          + Real.log (partitionFunctionΛ (IsingModel.latticeGraph d)
              (Λ.volume n) p)
        ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d)
            (Λ.volume (m + n)) p))
    (hbdd : BddAbove (Set.range
      (freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ p)))
    (hcard_one : (Λ.volume 1).card ≠ 0) :
    Filter.Tendsto
      (freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ p)
      Filter.atTop
      (nhds (freeEnergyInfinite (IsingModel.latticeGraph d) Λ p)) :=
  freeEnergyAlongExhaustion_tendsto_of_superadditive
    (IsingModel.latticeGraph d) Λ p hcard_add hsuper hbdd hcard_one

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

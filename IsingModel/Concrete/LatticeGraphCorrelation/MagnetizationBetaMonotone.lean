import IsingModel.Inequalities.MonotonicityBetaBoundaryCondition
import IsingModel.Concrete.LatticeGraphCorrelation.SpontaneousMagnetization

/-!
# β-monotonicity of the infinite-volume magnetization (FV §3.6, Issue #3605)

The infinite-volume `+` magnetization `m⁺(β,h)` and the spontaneous magnetization
`m*(β)` are monotone increasing in the inverse temperature `β` — the order parameter
grows with `β`.  The proof bridges the finite-volume single-spin box expectation to a
`+` boundary spin correlation (`Spin.sign = spinProduct {x}`), applies the boundary
β-monotonicity (`gibbsExpectationBC_plus_monotone_beta_singleton`, #3609), and passes
to the limit.

* `plusBoxObsExpectation_singleSpin_eq` — the finite-volume bridge.
* `plusMagnetization_mono_beta` — `m⁺(β,h)` nondecreasing in `β`.
* `plusStateSpontaneousMagnetization_mono_beta` — `m*(β)` nondecreasing in `β`.

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.6; Glimm–Jaffe Prop. 4.2.1.
-/

namespace IsingModel

namespace Ambient

open Finset Filter Topology

variable {d : ℕ}

/-- **The finite-volume single-spin bridge**: the `+` box expectation of the single
spin at `x` equals the `+` boundary spin correlation `⟨σ_{⟨x⟩}⟩` on the cubic ambient
(`Spin.sign = spinProduct {x}`, with `restrictConfig` transporting the site into the
ambient). -/
theorem plusBoxObsExpectation_singleSpin_eq (n m : ℕ) {J h β : ℝ} (x : Fin d → ℤ)
    (hS : (⟨(singleSpinMonoObs x).S, (singleSpinMonoObs x).φ⟩ : LocalObservable d).S ⊆
      cubicBox d m) :
    plusBoxObsExpectation n m J h β
        (⟨(singleSpinMonoObs x).S, (singleSpinMonoObs x).φ⟩ : LocalObservable d) hS
      = gibbsExpectationBC (inducedGraph (IsingModel.latticeGraph d) (cubicBox d m)) β
          (fun _ => J) h (plusBoxInterior d n m) (plusConfig _)
          (spinProduct {⟨x, hS (Finset.mem_singleton_self x)⟩}) := by
  unfold plusBoxObsExpectation plusBoxExpectation
  congr 1
  funext σ
  rw [spinProduct_singleton]
  rfl

/-- **β-monotonicity of the finite-volume single-spin `+` box expectation**. -/
theorem plusBoxObsExpectation_singleSpin_mono_beta (n m : ℕ) {J h β₁ β₂ : ℝ}
    (hJ : 0 ≤ J) (hh : 0 ≤ h) (x : Fin d → ℤ) (hβ₁ : 0 < β₁) (hβ : β₁ ≤ β₂)
    (hS : (⟨(singleSpinMonoObs x).S, (singleSpinMonoObs x).φ⟩ : LocalObservable d).S ⊆
      cubicBox d m) :
    plusBoxObsExpectation n m J h β₁
        (⟨(singleSpinMonoObs x).S, (singleSpinMonoObs x).φ⟩ : LocalObservable d) hS ≤
      plusBoxObsExpectation n m J h β₂
        (⟨(singleSpinMonoObs x).S, (singleSpinMonoObs x).φ⟩ : LocalObservable d) hS := by
  rw [plusBoxObsExpectation_singleSpin_eq, plusBoxObsExpectation_singleSpin_eq]
  exact gibbsExpectationBC_plus_monotone_beta_singleton
    (inducedGraph (IsingModel.latticeGraph d) (cubicBox d m)) hJ hh
    (plusBoxInterior d n m) ⟨x, hS (Finset.mem_singleton_self x)⟩ hβ₁ hβ

/-- **β-monotonicity of the `+` magnetization** `m⁺(β,h)`: for a ferromagnetic uniform
coupling (`J, h ≥ 0`) and `0 < β₁ ≤ β₂`, `m⁺(β₁,h) ≤ m⁺(β₂,h)` (the magnetization
grows with `β`).  Each finite-volume single-spin box expectation is β-monotone, and
`m⁺` is their limit. -/
theorem plusMagnetization_mono_beta {J h : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (x : Fin d → ℤ)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ : β₁ ≤ β₂) :
    plusMagnetization x J h β₁ ≤ plusMagnetization x J h β₂ := by
  refine le_of_tendsto_of_tendsto'
    (tendsto_plusMagnetization (β := β₁) hβ₁.le hJ x)
    (tendsto_plusMagnetization (β := β₂) (lt_of_lt_of_le hβ₁ hβ).le hJ x)
    (fun k => ?_)
  exact plusBoxObsExpectation_singleSpin_mono_beta _ _ hJ hh x hβ₁ hβ _

/-- **β-monotonicity of the spontaneous magnetization** `m*(β)`: for `J ≥ 0` and
`0 < β₁ ≤ β₂`, `m*(β₁) ≤ m*(β₂)` (the order parameter grows with `β`). -/
theorem plusStateSpontaneousMagnetization_mono_beta {J : ℝ} (hJ : 0 ≤ J)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ : β₁ ≤ β₂) :
    plusStateSpontaneousMagnetization d J β₁ ≤ plusStateSpontaneousMagnetization d J β₂ :=
  plusMagnetization_mono_beta hJ le_rfl (0 : Fin d → ℤ) hβ₁ hβ

end Ambient

end IsingModel

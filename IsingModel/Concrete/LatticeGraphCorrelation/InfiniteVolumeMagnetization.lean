import IsingModel.Concrete.LatticeGraphCorrelation.MinusStateExtremal
import IsingModel.Concrete.LatticeGraphCorrelation.CubicBoxInterlacing
import IsingModel.Inequalities.MonotonicityExtremal

/-!
# Infinite-volume magnetization `m^±(β,h)` (FV §3.4–§3.6, Issue #3599)

The **magnetization** is the order parameter of the Ising phase transition: the
single-spin expectation `m^±(β,h) = μ^±(σ_x)` in the cubic-exhaustion `±`-state.
This file packages the single-spin observable, defines `plusMagnetization` and
`minusMagnetization`, and records the elementary properties inherited from the
`±`-state machinery: convergence of the finite-volume magnetizations, the `[-1,1]`
bounds, and the extremal ordering `m⁻ ≤ m⁺` (FV Lemma 3.23 / Theorem 3.17).

* `singleSpinMonoObs` — the (monotone) single-spin observable at a site.
* `plusMagnetization` / `minusMagnetization` — `m^±(β,h)` at a site.
* `tendsto_plusMagnetization` / `tendsto_minusMagnetization` — finite-volume limits.
* `plusMagnetization_le_one` / `neg_one_le_plusMagnetization` (and `minus`) — bounds.
* `minusMagnetization_le_plusMagnetization` — the `m⁻ ≤ m⁺` ordering.

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.4 (Theorem 3.17), §3.6 (magnetization, phase transition).
-/

namespace IsingModel

namespace Ambient

open Finset Filter Topology

variable {d : ℕ}

/-- **A site lies in the cubic box of its lattice radius**: `x ∈ cubicBox d
(latticeRadius x)`, since every coordinate satisfies `|x i| ≤ latticeRadius x`. -/
theorem mem_cubicBox_latticeRadius (x : Fin d → ℤ) :
    x ∈ cubicBox d (latticeRadius x) := by
  rw [mem_cubicBox]
  intro i
  exact abs_le.mp (abs_coord_le_latticeRadius x i)

/-- **The single-spin monotone observable** at a site `x`: the support is `{x}` and the
function is the spin sign `σ ↦ s(σ_x)`, monotone in the configuration order. -/
noncomputable def singleSpinMonoObs (x : Fin d → ℤ) : LocalMonotoneObservable d where
  S := {x}
  φ := fun σ => Spin.sign ℝ (σ ⟨x, Finset.mem_singleton_self x⟩)
  mono := singleSpinObs_monotone _

/-- The support of the single-spin observable sits inside the cubic box of the site's
lattice radius. -/
theorem singleSpinMonoObs_support_subset (x : Fin d → ℤ) :
    (singleSpinMonoObs x).S ⊆ cubicBox d (latticeRadius x) :=
  Finset.singleton_subset_iff.mpr (mem_cubicBox_latticeRadius x)

/-- **The single spin sign is bounded by `1`**. -/
theorem singleSpinMonoObs_phi_le_one (x : Fin d → ℤ)
    (σ : Config (↑(singleSpinMonoObs x).S : Type _)) : (singleSpinMonoObs x).φ σ ≤ 1 := by
  change Spin.sign ℝ (σ ⟨x, Finset.mem_singleton_self x⟩) ≤ 1
  cases σ ⟨x, Finset.mem_singleton_self x⟩ <;> simp [Spin.sign, Spin.toSign]

/-- **The single spin sign is bounded below by `-1`**. -/
theorem neg_one_le_singleSpinMonoObs_phi (x : Fin d → ℤ)
    (σ : Config (↑(singleSpinMonoObs x).S : Type _)) : (-1 : ℝ) ≤ (singleSpinMonoObs x).φ σ := by
  change (-1 : ℝ) ≤ Spin.sign ℝ (σ ⟨x, Finset.mem_singleton_self x⟩)
  cases σ ⟨x, Finset.mem_singleton_self x⟩ <;> simp [Spin.sign, Spin.toSign]

/-- **The infinite-volume `+` magnetization** `m⁺(β,h) = μ⁺(σ_x)`: the cubic-exhaustion
`+`-state expectation of the single spin at `x`. -/
noncomputable def plusMagnetization (x : Fin d → ℤ) (J h β : ℝ) : ℝ :=
  plusStateExpectation J h β
    (⟨(singleSpinMonoObs x).S, (singleSpinMonoObs x).φ⟩ : LocalObservable d)
    (singleSpinMonoObs_support_subset x)

/-- **The infinite-volume `−` magnetization** `m⁻(β,h) = μ⁻(σ_x)`: the cubic-exhaustion
`−`-state expectation of the single spin at `x`. -/
noncomputable def minusMagnetization (x : Fin d → ℤ) (J h β : ℝ) : ℝ :=
  minusStateExpectation J h β
    (⟨(singleSpinMonoObs x).S, (singleSpinMonoObs x).φ⟩ : LocalObservable d)
    (singleSpinMonoObs_support_subset x)

/-- **`m⁺ ≤ 1`**: the `+` magnetization is at most `1` (the single spin is `≤ 1` and the
`+`-state functional is monotone and normalised). -/
theorem plusMagnetization_le_one {J h β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (x : Fin d → ℤ) : plusMagnetization x J h β ≤ 1 := by
  have hmono := plusStateExpectation_mono (h := h) hβ hJ
    (φ₁ := (singleSpinMonoObs x).φ) (φ₂ := fun _ => (1 : ℝ))
    (singleSpinMonoObs_phi_le_one x) (singleSpinMonoObs_support_subset x)
  rwa [plusStateExpectation_const hβ hJ] at hmono

/-- **`-1 ≤ m⁺`**: the `+` magnetization is at least `-1`. -/
theorem neg_one_le_plusMagnetization {J h β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (x : Fin d → ℤ) : (-1 : ℝ) ≤ plusMagnetization x J h β := by
  have hmono := plusStateExpectation_mono (h := h) hβ hJ
    (φ₁ := fun _ => (-1 : ℝ)) (φ₂ := (singleSpinMonoObs x).φ)
    (neg_one_le_singleSpinMonoObs_phi x) (singleSpinMonoObs_support_subset x)
  rwa [plusStateExpectation_const hβ hJ] at hmono

/-- **`m⁻ ≤ 1`**: the `−` magnetization is at most `1` (the `−` state is the `+` state
of the flipped observable at `−h`, and the flipped single spin is still `≤ 1`). -/
theorem minusMagnetization_le_one {J h β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (x : Fin d → ℤ) : minusMagnetization x J h β ≤ 1 := by
  unfold minusMagnetization minusStateExpectation
  have hmono := plusStateExpectation_mono (h := -h) hβ hJ
    (φ₁ := (⟨(singleSpinMonoObs x).S, (singleSpinMonoObs x).φ⟩ : LocalObservable d).flipObs.φ)
    (φ₂ := fun _ => (1 : ℝ))
    (fun σ => singleSpinMonoObs_phi_le_one x (Config.flip σ))
    (singleSpinMonoObs_support_subset x)
  rwa [plusStateExpectation_const hβ hJ] at hmono

/-- **`-1 ≤ m⁻`**: the `−` magnetization is at least `-1`. -/
theorem neg_one_le_minusMagnetization {J h β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (x : Fin d → ℤ) : (-1 : ℝ) ≤ minusMagnetization x J h β := by
  unfold minusMagnetization minusStateExpectation
  have hmono := plusStateExpectation_mono (h := -h) hβ hJ
    (φ₁ := fun _ => (-1 : ℝ))
    (φ₂ := (⟨(singleSpinMonoObs x).S, (singleSpinMonoObs x).φ⟩ : LocalObservable d).flipObs.φ)
    (fun σ => neg_one_le_singleSpinMonoObs_phi x (Config.flip σ))
    (singleSpinMonoObs_support_subset x)
  rwa [plusStateExpectation_const hβ hJ] at hmono

/-- **The extremal magnetization ordering** `m⁻ ≤ m⁺` (FV Lemma 3.23 / Theorem 3.17):
the `−` magnetization is at most the `+` magnetization, since the single spin is
monotone and `μ⁻ ≤ μ⁺` on monotone observables. -/
theorem minusMagnetization_le_plusMagnetization {J h β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (x : Fin d → ℤ) : minusMagnetization x J h β ≤ plusMagnetization x J h β :=
  minusStateExpectation_le_plusStateExpectation hβ hJ
    (⟨(singleSpinMonoObs x).S, (singleSpinMonoObs x).φ⟩ : LocalObservable d)
    (singleSpinMonoObs x).mono (singleSpinMonoObs_support_subset x)

/-- **Convergence of the finite-volume `+` magnetization**: the screened single-spin
`+` box expectations converge to `m⁺(β,h)`. -/
theorem tendsto_plusMagnetization {J h β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (x : Fin d → ℤ) :
    Tendsto (fun k => plusBoxObsExpectation (latticeRadius x + k) (latticeRadius x + k + 1)
        J h β (⟨(singleSpinMonoObs x).S, (singleSpinMonoObs x).φ⟩ : LocalObservable d)
        ((singleSpinMonoObs_support_subset x).trans
          (cubicBox_mono d (by omega : latticeRadius x ≤ latticeRadius x + k + 1)))) atTop
      (nhds (plusMagnetization x J h β)) :=
  tendsto_plusStateExpectation hβ hJ _ (singleSpinMonoObs_support_subset x)

/-- **Convergence of the finite-volume `−` magnetization**: the screened single-spin
`−` box expectations converge to `m⁻(β,h)`. -/
theorem tendsto_minusMagnetization {J h β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (x : Fin d → ℤ) :
    Tendsto (fun k => plusBoxObsExpectation (latticeRadius x + k) (latticeRadius x + k + 1)
        J (-h) β
        (⟨(singleSpinMonoObs x).S, (singleSpinMonoObs x).φ⟩ : LocalObservable d).flipObs
        ((singleSpinMonoObs_support_subset x).trans
          (cubicBox_mono d (by omega : latticeRadius x ≤ latticeRadius x + k + 1)))) atTop
      (nhds (minusMagnetization x J h β)) :=
  tendsto_minusStateExpectation hβ hJ _ (singleSpinMonoObs_support_subset x)

end Ambient

end IsingModel

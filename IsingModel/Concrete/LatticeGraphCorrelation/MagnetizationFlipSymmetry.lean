import IsingModel.Concrete.LatticeGraphCorrelation.InfiniteVolumeMagnetization
import IsingModel.Concrete.LatticeGraphCorrelation.PlusStateTranslationGeneral

/-!
# Spin-flip symmetry of the infinite-volume magnetization (FV §3.6, Issue #3599)

The global spin-flip `σ ↦ σ.flip` (with `h ↦ −h`) exchanges the `+` and `−` states
and negates the single spin, giving the magnetization symmetry
`m⁻(β,h) = −m⁺(β,−h)`.  In particular, at zero field the `±` magnetizations are
antisymmetric: `m⁻(β,0) = −m⁺(β,0)`.

* `singleSpinMonoObs_phi_flip` — the single spin negates under the flip.
* `minusMagnetization_eq_neg_plusMagnetization_neg_h` / `plus…` — the symmetry.
* `minusMagnetization_zero_eq_neg_plusMagnetization_zero` — the `h = 0` antisymmetry.

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.6 (the `±` magnetizations and spin-flip symmetry).
-/

namespace IsingModel

namespace Ambient

open Finset

variable {d : ℕ}

/-- **The single spin negates under the global flip**: `s(σ_x ∘ flip) = −s(σ_x)`
(`Spin.sign_flip`). -/
theorem singleSpinMonoObs_phi_flip (x : Fin d → ℤ)
    (σ : Config (↑(singleSpinMonoObs x).S : Type _)) :
    (singleSpinMonoObs x).φ (Config.flip σ) = -(singleSpinMonoObs x).φ σ := by
  change Spin.sign ℝ (Config.flip σ ⟨x, Finset.mem_singleton_self x⟩)
    = -Spin.sign ℝ (σ ⟨x, Finset.mem_singleton_self x⟩)
  rw [show Config.flip σ ⟨x, Finset.mem_singleton_self x⟩
      = (σ ⟨x, Finset.mem_singleton_self x⟩).flip from rfl, Spin.sign_flip]

/-- **Spin-flip symmetry of the magnetization** `m⁻(β,h) = −m⁺(β,−h)`: the `−` state
is the `+` state of the flipped observable at `−h`, and the single spin negates under
the flip. -/
theorem minusMagnetization_eq_neg_plusMagnetization_neg_h {J h β : ℝ} (hβ : 0 ≤ β)
    (hJ : 0 ≤ J) (x : Fin d → ℤ) :
    minusMagnetization x J h β = -plusMagnetization x J (-h) β := by
  unfold minusMagnetization minusStateExpectation plusMagnetization
  simp only [LocalObservable.flipObs]
  rw [plusStateExpectation_congr_phi
      (φ₂ := fun σ => (-1 : ℝ) * (singleSpinMonoObs x).φ σ)
      (funext fun σ => by rw [singleSpinMonoObs_phi_flip]; ring)
      (singleSpinMonoObs_support_subset x),
    plusStateExpectation_const_mul hβ hJ]
  ring

/-- **Spin-flip symmetry of the magnetization** `m⁺(β,h) = −m⁻(β,−h)`. -/
theorem plusMagnetization_eq_neg_minusMagnetization_neg_h {J h β : ℝ} (hβ : 0 ≤ β)
    (hJ : 0 ≤ J) (x : Fin d → ℤ) :
    plusMagnetization x J h β = -minusMagnetization x J (-h) β := by
  rw [minusMagnetization_eq_neg_plusMagnetization_neg_h hβ hJ x, neg_neg, neg_neg]

/-- **Zero-field antisymmetry** `m⁻(β,0) = −m⁺(β,0)`: at `h = 0` the `±`
magnetizations are antisymmetric (the spin-flip symmetry with `−h = h = 0`). -/
theorem minusMagnetization_zero_eq_neg_plusMagnetization_zero {J β : ℝ} (hβ : 0 ≤ β)
    (hJ : 0 ≤ J) (x : Fin d → ℤ) :
    minusMagnetization x J 0 β = -plusMagnetization x J 0 β := by
  have := minusMagnetization_eq_neg_plusMagnetization_neg_h (h := 0) hβ hJ x
  rwa [neg_zero] at this

/-- **Zero-field antisymmetry** `m⁺(β,0) = −m⁻(β,0)`. -/
theorem plusMagnetization_zero_eq_neg_minusMagnetization_zero {J β : ℝ} (hβ : 0 ≤ β)
    (hJ : 0 ≤ J) (x : Fin d → ℤ) :
    plusMagnetization x J 0 β = -minusMagnetization x J 0 β := by
  rw [minusMagnetization_zero_eq_neg_plusMagnetization_zero hβ hJ x, neg_neg]

end Ambient

end IsingModel

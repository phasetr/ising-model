import IsingModel.Concrete.LatticeGraphCorrelation.MagnetizationFieldMonotone

/-!
# Spontaneous magnetization `m*(β)` (FV §3.6, order parameter)

The **spontaneous magnetization** is the zero-field `+` magnetization at the origin,
`m*(β) = m⁺(β,0) = μ⁺(σ_0)`, the order parameter of the Ising phase transition.  It
is the basic non-negative quantity distinguishing the ordered phase (`m*(β) > 0`) from
the disordered one (`m*(β) = 0`).

This file records its elementary, unconditional properties inherited from the `±`
magnetization API: `m*(β) ∈ [0,1]` (non-negativity is the key consequence of the
zero-field antisymmetry `m⁻(β,0) = −m⁺(β,0)` together with `m⁻ ≤ m⁺`), the `−`
spontaneous magnetization `−m*(β)`, and monotonicity in the field for the surrounding
magnetization curve.

* `plusStateSpontaneousMagnetization` — `m*(β) = m⁺(β,0)`.
* `plusStateSpontaneousMagnetization_nonneg` / `_le_one` — `m*(β) ∈ [0,1]`.
* `minusStateSpontaneousMagnetization` / `_eq_neg` — the `−` order parameter `= −m*(β)`.

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.6 (spontaneous magnetization, the order parameter).
-/

namespace IsingModel

namespace Ambient

open Finset

variable {d : ℕ}

/-- **The spontaneous magnetization** `m*(β) = m⁺(β,0)`: the zero-field `+`
magnetization at the origin, the order parameter of the phase transition. -/
noncomputable def plusStateSpontaneousMagnetization (d : ℕ) (J β : ℝ) : ℝ :=
  plusMagnetization (0 : Fin d → ℤ) J 0 β

/-- **Non-negativity of the spontaneous magnetization** `0 ≤ m*(β)`: by the zero-field
antisymmetry `m⁻(β,0) = −m⁺(β,0)` and the extremal ordering `m⁻ ≤ m⁺`, one gets
`−m⁺(β,0) ≤ m⁺(β,0)`, hence `0 ≤ m⁺(β,0)`. -/
theorem plusStateSpontaneousMagnetization_nonneg {J β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    0 ≤ plusStateSpontaneousMagnetization d J β := by
  have hle := minusMagnetization_le_plusMagnetization (h := 0) hβ hJ (0 : Fin d → ℤ)
  have hanti := minusMagnetization_zero_eq_neg_plusMagnetization_zero hβ hJ (0 : Fin d → ℤ)
  rw [hanti] at hle
  unfold plusStateSpontaneousMagnetization
  linarith

/-- **Upper bound on the spontaneous magnetization** `m*(β) ≤ 1`. -/
theorem plusStateSpontaneousMagnetization_le_one {J β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    plusStateSpontaneousMagnetization d J β ≤ 1 :=
  plusMagnetization_le_one hβ hJ (0 : Fin d → ℤ)

/-- **The `−` spontaneous magnetization** `−m*(β) = m⁻(β,0)`: the zero-field `−`
magnetization at the origin. -/
noncomputable def minusStateSpontaneousMagnetization (d : ℕ) (J β : ℝ) : ℝ :=
  minusMagnetization (0 : Fin d → ℤ) J 0 β

/-- **The `−` order parameter is the negative of the spontaneous magnetization**
`m⁻(β,0) = −m*(β)`. -/
theorem minusStateSpontaneousMagnetization_eq_neg {J β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    minusStateSpontaneousMagnetization d J β = -plusStateSpontaneousMagnetization d J β :=
  minusMagnetization_zero_eq_neg_plusMagnetization_zero hβ hJ (0 : Fin d → ℤ)

/-- **The `−` spontaneous magnetization is non-positive** `m⁻(β,0) ≤ 0`. -/
theorem minusStateSpontaneousMagnetization_nonpos {J β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    minusStateSpontaneousMagnetization d J β ≤ 0 := by
  rw [minusStateSpontaneousMagnetization_eq_neg hβ hJ]
  exact neg_nonpos.mpr (plusStateSpontaneousMagnetization_nonneg hβ hJ)

/-- **The `−` order parameter is at most the spontaneous magnetization**
`m⁻(β,0) ≤ m*(β)`. -/
theorem minusStateSpontaneousMagnetization_le_plusStateSpontaneousMagnetization {J β : ℝ}
    (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    minusStateSpontaneousMagnetization d J β ≤ plusStateSpontaneousMagnetization d J β :=
  minusMagnetization_le_plusMagnetization (h := 0) hβ hJ (0 : Fin d → ℤ)

end Ambient

end IsingModel

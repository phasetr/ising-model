import IsingModel.Concrete.LatticeGraphCorrelation.MagnetizationFieldMonotone

/-!
# Sign of the magnetization (FV §3.6)

The sign of the infinite-volume magnetization follows from the field monotonicity
(`plusMagnetization_mono_h`) and the zero-field non-negativity (the zero-field
antisymmetry `m⁻(β,0) = −m⁺(β,0)` with the extremal ordering `m⁻ ≤ m⁺`):

* at zero field the `+` magnetization is non-negative at every site;
* for `h ≥ 0` the `+` magnetization is non-negative (it dominates its zero-field value);
* for `h ≤ 0` the `−` magnetization is non-positive (by the spin-flip symmetry).

These are the elementary sign facts underlying the order-parameter picture.

* `plusMagnetization_zero_field_nonneg` — `0 ≤ m⁺(β,0)` at any site.
* `plusMagnetization_nonneg_of_field_nonneg` — `0 ≤ h ⟹ 0 ≤ m⁺(β,h)`.
* `minusMagnetization_nonpos_of_field_nonpos` — `h ≤ 0 ⟹ m⁻(β,h) ≤ 0`.

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.6 (magnetization, sign and the order parameter).
-/

namespace IsingModel

namespace Ambient

open Finset

variable {d : ℕ}

/-- **Zero-field non-negativity of the `+` magnetization** `0 ≤ m⁺(β,0)` at any site:
the zero-field antisymmetry `m⁻(β,0) = −m⁺(β,0)` with the extremal ordering `m⁻ ≤ m⁺`
gives `−m⁺(β,0) ≤ m⁺(β,0)`, hence `0 ≤ m⁺(β,0)`. -/
theorem plusMagnetization_zero_field_nonneg {J β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (x : Fin d → ℤ) : 0 ≤ plusMagnetization x J 0 β := by
  have hle := minusMagnetization_le_plusMagnetization (h := 0) hβ hJ x
  have hanti := minusMagnetization_zero_eq_neg_plusMagnetization_zero hβ hJ x
  rw [hanti] at hle
  linarith

/-- **Non-negativity of the `+` magnetization at non-negative field** `0 ≤ h ⟹
0 ≤ m⁺(β,h)`: the magnetization is nondecreasing in the field and non-negative at
`h = 0`. -/
theorem plusMagnetization_nonneg_of_field_nonneg {J β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (x : Fin d → ℤ) {h : ℝ} (hh : 0 ≤ h) : 0 ≤ plusMagnetization x J h β :=
  le_trans (plusMagnetization_zero_field_nonneg hβ hJ x)
    (plusMagnetization_mono_h hβ hJ x hh)

/-- **Non-positivity of the `−` magnetization at non-positive field** `h ≤ 0 ⟹
m⁻(β,h) ≤ 0`: by the spin-flip symmetry `m⁻(β,h) = −m⁺(β,−h)`, with `−h ≥ 0` so the
`+` magnetization there is non-negative. -/
theorem minusMagnetization_nonpos_of_field_nonpos {J β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (x : Fin d → ℤ) {h : ℝ} (hh : h ≤ 0) : minusMagnetization x J h β ≤ 0 := by
  rw [minusMagnetization_eq_neg_plusMagnetization_neg_h hβ hJ]
  exact neg_nonpos.mpr
    (plusMagnetization_nonneg_of_field_nonneg hβ hJ x (neg_nonneg.mpr hh))

/-- **Non-positivity of the `−` magnetization at zero field** `m⁻(β,0) ≤ 0`. -/
theorem minusMagnetization_zero_field_nonpos {J β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (x : Fin d → ℤ) : minusMagnetization x J 0 β ≤ 0 :=
  minusMagnetization_nonpos_of_field_nonpos hβ hJ x le_rfl

end Ambient

end IsingModel

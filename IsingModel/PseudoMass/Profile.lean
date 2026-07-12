import IsingModel.AmbientLattice.TruncatedFunctions
import IsingModel.BetaDerivative
import IsingModel.PolyDecay
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Pseudo-Mass Profile Function

This module is part of the split `IsingModel.PseudoMass` development.
-/

namespace IsingModel

open Set Real Filter

/-! ## The pseudo-mass profile function -/

/-- **`Real.tanh` is strictly monotone**: derived from
`sinh (y - x) = sinh y · cosh x − cosh y · sinh x > 0` for `x < y`,
divided by `cosh x · cosh y > 0`.

Mathlib lacks a direct `Real.tanh_strictMono`; this is a local
helper. -/
theorem _root_.Real.tanh_strictMono : StrictMono Real.tanh := by
  intro x y hxy
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh]
  have hcx : 0 < Real.cosh x := Real.cosh_pos _
  have hcy : 0 < Real.cosh y := Real.cosh_pos _
  rw [div_lt_div_iff₀ hcx hcy]
  have hsub_pos : 0 < Real.sinh (y - x) := Real.sinh_pos_iff.mpr (sub_pos.mpr hxy)
  have heq : Real.sinh (y - x) =
      Real.sinh y * Real.cosh x - Real.cosh y * Real.sinh x := Real.sinh_sub y x
  linarith

/-- The pseudo-mass profile: `g(t, r, α) = 2 · exp(-(t·r)) / (1 + (t·r)^α)`.
For `r > 0` and `α ≥ 1`, this is a continuous, strictly decreasing function
of `t ≥ 0` with `g(0) = 2` and `g(t) → 0` as `t → ∞`. -/
noncomputable def pseudoMassG (α : ℕ) (r t : ℝ) : ℝ :=
  2 * Real.exp (-(t * r)) / (1 + (t * r) ^ α)

/-- `pseudoMassG` at `t = 0` equals 2. -/
theorem pseudoMassG_zero {α : ℕ} (hα : 1 ≤ α) (r : ℝ) : pseudoMassG α r 0 = 2 := by
  simp [pseudoMassG, zero_mul, Real.exp_zero,
    zero_pow (Nat.one_le_iff_ne_zero.mp hα)]

/-- `pseudoMassG` is positive for `t ≥ 0` and `r > 0`. -/
theorem pseudoMassG_pos (α : ℕ) {r t : ℝ} (ht : 0 ≤ t) (hr : 0 < r) :
    0 < pseudoMassG α r t := by
  unfold pseudoMassG
  apply div_pos (mul_pos two_pos (Real.exp_pos _))
  have h : 0 ≤ (t * r) ^ α := pow_nonneg (mul_nonneg ht hr.le) α
  linarith

/-- **Refined upper bound** (Step 132a): `pseudoMassG α r t ≤ 2 / (1 + (t·r)^α)`.

Proof: `pseudoMassG α r t = 2·exp(-(t·r)) / (1+(t·r)^α) ≤ 2 / (1+(t·r)^α)` since `exp(-(t·r)) ≤ 1`.

This is the key bound used in GJ §17.5 p.312 to replace the correlation `⟨φ(x)φ(z)⟩/A`
by `2/(1+(m^-·d(x,z))^α)` via the pseudo-mass definition.

**References**: Glimm–Jaffe §17.5, Theorem 17.5.1 proof, p.312. -/
theorem pseudoMassG_le_two_div_one_add_pow (α : ℕ) {r t : ℝ} (ht : 0 ≤ t) (hr : 0 < r) :
    pseudoMassG α r t ≤ 2 / (1 + (t * r) ^ α) := by
  unfold pseudoMassG
  have hdenom_pos : (0 : ℝ) < 1 + (t * r) ^ α := by
    have h : 0 ≤ (t * r) ^ α := pow_nonneg (mul_nonneg ht hr.le) α
    linarith
  rw [(div_le_div_iff_of_pos_right hdenom_pos)]
  have hexp : Real.exp (-(t * r)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg ht hr.le))
  linarith [Real.exp_pos (-(t * r))]

/-- **`pseudoMassG α r t ≥ exp(-(t·r))`** (for `t·r ≤ 1`, `t ≥ 0`,
`r > 0`, `α ≥ 1`): in the small-t regime, denominator
`1 + (t·r)^α ≤ 2` (since `(t·r)^α ≤ 1` for `t·r ∈ [0, 1]` and α ≥ 1),
so quotient ≥ numerator/2 = exp(-(t·r)). -/
theorem pseudoMassG_ge_exp_of_tr_le_one {α : ℕ} (hα : 1 ≤ α) {r t : ℝ}
    (ht : 0 ≤ t) (hr : 0 < r) (htr_le : t * r ≤ 1) :
    Real.exp (-(t * r)) ≤ pseudoMassG α r t := by
  unfold pseudoMassG
  have htr_nn : 0 ≤ t * r := mul_nonneg ht hr.le
  have h_pow_nn : 0 ≤ (t * r) ^ α := pow_nonneg htr_nn α
  have h_pow_le_one : (t * r) ^ α ≤ 1 := by
    apply pow_le_one₀ htr_nn htr_le
  have h_denom_pos : 0 < 1 + (t * r) ^ α := by linarith
  have h_denom_le_two : 1 + (t * r) ^ α ≤ 2 := by linarith
  have h_exp_pos : 0 < Real.exp (-(t * r)) := Real.exp_pos _
  rw [le_div_iff₀ h_denom_pos]
  have := hα
  nlinarith

/-- **`pseudoMassG α r t ≥ exp(-(t·r)) / (t·r)^α`** (for `t·r ≥ 1`, `t ≥ 0`,
`r > 0`, `α ≥ 1`): in the large-t regime, denominator
`1 + (t·r)^α ≤ 2·(t·r)^α` (since `(t·r)^α ≥ 1`), so quotient ≥
`2·exp(-(t·r)) / (2·(t·r)^α) = exp(-(t·r))/(t·r)^α`.

Step 119 plan Step 5.7c building block: paired with
`pseudoMassG_ge_exp_of_tr_le_one`, gives a useful lower bound on
`pseudoMassG` in both regimes for the HLS pseudo-mass-to-bridge.bound
analytic step. Combined with `pseudoMass_ge_iff_pseudoMassG_ge` and
the bound-reduction wrapper of #3173, this lets a cubic-path tanh decay
input land directly in the bridge.bound shape. -/
theorem pseudoMassG_ge_exp_div_pow_of_tr_ge_one (α : ℕ)
    {r t : ℝ} (htr_ge : 1 ≤ t * r) :
    Real.exp (-(t * r)) / (t * r) ^ α ≤ pseudoMassG α r t := by
  unfold pseudoMassG
  have htr_pos : 0 < t * r := lt_of_lt_of_le zero_lt_one htr_ge
  have h_pow_pos : 0 < (t * r) ^ α := pow_pos htr_pos α
  have h_pow_ge_one : 1 ≤ (t * r) ^ α := by
    have : (1 : ℝ) ^ α ≤ (t * r) ^ α := pow_le_pow_left₀ zero_le_one htr_ge α
    simpa using this
  have h_denom_pos : 0 < 1 + (t * r) ^ α := by linarith
  have h_denom_le : 1 + (t * r) ^ α ≤ 2 * (t * r) ^ α := by linarith
  have h_exp_pos : 0 < Real.exp (-(t * r)) := Real.exp_pos _
  rw [div_le_div_iff₀ h_pow_pos h_denom_pos]
  nlinarith

/-- **`pseudoMassG α r t ≤ 2·exp(-(t·r))`** (for `t ≥ 0`, `r > 0`):
since the denominator `1 + (tr)^α ≥ 1`, the quotient is dominated
by the numerator. -/
theorem pseudoMassG_le_two_mul_exp (α : ℕ) {r t : ℝ} (ht : 0 ≤ t) (hr : 0 < r) :
    pseudoMassG α r t ≤ 2 * Real.exp (-(t * r)) := by
  unfold pseudoMassG
  have h_pow_nn : 0 ≤ (t * r) ^ α := pow_nonneg (mul_nonneg ht hr.le) α
  have h_denom_pos : 0 < 1 + (t * r) ^ α := by linarith
  have h_denom_ge_one : 1 ≤ 1 + (t * r) ^ α := by linarith
  have h_exp_pos : 0 < Real.exp (-(t * r)) := Real.exp_pos _
  rw [div_le_iff₀ h_denom_pos]
  nlinarith

/-- **GJ §17.5 Theorem 17.5.1 bridge to polynomial decay** (Step 119 plan Step 5.4 bridge).

For `M·t > 0` and `α : ℕ`, the rational pseudo-mass denominator can be bounded by the pure
polynomial decay:

    1 / (1 + (M·t)^α) ≤ 1 / (M·t)^α

This is the pointwise bridge from the pseudo-mass majorant form `1/(1+(M·t)^α)` to the
discrete-HLS polynomial-decay form `(M·t)^(-α) = M^(-α)·t^(-α)`. Proof: `1 + (M·t)^α ≥ (M·t)^α`
(since 1 ≥ 0), and `one_div_le_one_div_of_le` with positivity of `(M·t)^α`. -/
theorem one_div_one_add_pow_le_one_div_pow {α : ℕ} {Mt : ℝ} (hMt : 0 < Mt) :
    1 / (1 + Mt ^ α) ≤ 1 / Mt ^ α := by
  have h_pow_pos : 0 < Mt ^ α := pow_pos hMt α
  have h_denom_pos : 0 < 1 + Mt ^ α := by linarith
  have h_denom_ge : Mt ^ α ≤ 1 + Mt ^ α := by linarith
  exact one_div_le_one_div_of_le h_pow_pos h_denom_ge

/-- **`pseudoMassG`-form pointwise polynomial bridge** (Step 119 plan Step 5.4 bridge).

For `t > 0`, `r > 0`, `α : ℕ` (so `t·r > 0`):

    2 / (1 + (t·r)^α) ≤ 2 / (t·r)^α = 2 · (t·r)^(-α)

Direct consequence of `one_div_one_add_pow_le_one_div_pow` scaled by 2. Couples the
pseudoMass majorant form `2/(1+(t·r)^α)` (PR #3154's
`_le_two_div_one_add_pow_pseudoMassFromParamsAtPair`) to the polynomial decay form
`2·(t·r)^(-α)` directly usable in the HLS sum. -/
theorem two_div_one_add_pow_le_two_div_pow {α : ℕ} {tr : ℝ} (htr : 0 < tr) :
    2 / (1 + tr ^ α) ≤ 2 / tr ^ α := by
  have h_pow_pos : 0 < tr ^ α := pow_pos htr α
  have h_denom_pos : 0 < 1 + tr ^ α := by linarith
  have h_denom_ge : tr ^ α ≤ 1 + tr ^ α := by linarith
  exact div_le_div_of_nonneg_left (by norm_num) h_pow_pos h_denom_ge

/-- **Pair-product polynomial-decay bridge** (Step 119 plan Step 5.4 bridge).

For `M·tx > 0`, `M·ty > 0`, `α : ℕ`:

    1/(1+(M·tx)^α) · 1/(1+(M·ty)^α) ≤ 1/(M·tx)^α · 1/(M·ty)^α

The pair-product form of `one_div_one_add_pow_le_one_div_pow`, used to bridge from the
pseudo-mass pair-product majorant `2/(1+(m⁻·d_x)^α) · 2/(1+(m⁻·d_y)^α)` (PR #3155) to the
polynomial-decay convolution `(m⁻·d_x)^(-α) · (m⁻·d_y)^(-α) = m⁻^(-2α) · d_x^(-α) · d_y^(-α)`
on which the discrete HLS convolution sum bound applies. -/
theorem one_div_one_add_pow_mul_one_div_one_add_pow_le_one_div_pow_mul_one_div_pow
    {α : ℕ} {Mtx Mty : ℝ} (hMtx : 0 < Mtx) (hMty : 0 < Mty) :
    1 / (1 + Mtx ^ α) * (1 / (1 + Mty ^ α)) ≤ 1 / Mtx ^ α * (1 / Mty ^ α) := by
  have hx := one_div_one_add_pow_le_one_div_pow (α := α) hMtx
  have hy := one_div_one_add_pow_le_one_div_pow (α := α) hMty
  have hy_nn : 0 ≤ 1 / (1 + Mty ^ α) := by
    have h_pow_pos : 0 < Mty ^ α := pow_pos hMty α
    have h_denom_pos : 0 < 1 + Mty ^ α := by linarith
    exact div_nonneg (by norm_num) h_denom_pos.le
  have hx_pow_nn : 0 ≤ 1 / Mtx ^ α :=
    div_nonneg (by norm_num) (pow_pos hMtx α).le
  exact mul_le_mul hx hy hy_nn hx_pow_nn

/-- **Scaled pair-product polynomial-decay bridge** (Step 119 plan Step 5.4 bridge):
the `2/(...)·2/(...)` form of the previous lemma, matching the pseudo-mass pair-product
majorant constants. -/
theorem two_div_one_add_pow_mul_two_div_one_add_pow_le_two_div_pow_mul_two_div_pow
    {α : ℕ} {tx ty : ℝ} (htx : 0 < tx) (hty : 0 < ty) :
    2 / (1 + tx ^ α) * (2 / (1 + ty ^ α)) ≤ 2 / tx ^ α * (2 / ty ^ α) := by
  have hx := two_div_one_add_pow_le_two_div_pow (α := α) htx
  have hy := two_div_one_add_pow_le_two_div_pow (α := α) hty
  have hy_nn : 0 ≤ 2 / (1 + ty ^ α) := by
    have h_pow_pos : 0 < ty ^ α := pow_pos hty α
    have h_denom_pos : 0 < 1 + ty ^ α := by linarith
    exact div_nonneg (by norm_num) h_denom_pos.le
  have hx_pow_nn : 0 ≤ 2 / tx ^ α :=
    div_nonneg (by norm_num) (pow_pos htx α).le
  exact mul_le_mul hx hy hy_nn hx_pow_nn

/-- **Polynomial factorization** (Step 119 plan Step 5.4 bridge).

For `M > 0`, `t > 0`, `α : ℕ`:

    1 / (M·t)^α = (1 / M^α) · (1 / t^α)

Direct application of `mul_pow` + division. Reveals the `M^(-α)` prefactor structure used in
the GJ p. 312 HLS sum derivation: factoring out the pseudo-mass `m⁻` from the polynomial
decay form. -/
theorem one_div_mul_pow_eq_one_div_pow_mul_one_div_pow {α : ℕ} {M t : ℝ}
    (hM : 0 < M) (ht : 0 < t) :
    1 / (M * t) ^ α = 1 / M ^ α * (1 / t ^ α) := by
  rw [mul_pow]
  field_simp

/-- **Polynomial pair-product factorization** (Step 119 plan Step 5.4 bridge).

For `M > 0`, `tx > 0`, `ty > 0`, `α : ℕ`:

    (1 / (M·tx)^α) · (1 / (M·ty)^α) = (1 / M^(2α)) · (1 / tx^α) · (1 / ty^α)

Pair-product form. The `M^(-2α)` prefactor matches GJ p. 312's `m⁻^(-2α)` factor in the
HLS sum bound, separating it from the per-site polynomial decay `t_x^(-α)·t_y^(-α)`. -/
theorem one_div_mul_pow_mul_one_div_mul_pow_eq {α : ℕ} {M tx ty : ℝ}
    (hM : 0 < M) (htx : 0 < tx) (hty : 0 < ty) :
    1 / (M * tx) ^ α * (1 / (M * ty) ^ α)
      = 1 / M ^ (2 * α) * (1 / tx ^ α * (1 / ty ^ α)) := by
  rw [one_div_mul_pow_eq_one_div_pow_mul_one_div_pow hM htx,
      one_div_mul_pow_eq_one_div_pow_mul_one_div_pow hM hty]
  rw [show 2 * α = α + α from by ring, pow_add]
  field_simp

/-- **Pointwise bridge from `1/(1+(M·t)^α)` to `1/(1+t^α)`**
(Step 119 plan Step 5.5c bridge).

For `M > 0`, `t ≥ 0`, `α : ℕ`:

    1 / (1 + (M·t)^α) ≤ max(1, (M^α)⁻¹) · (1 / (1 + t^α))

Cases (after expanding `(M·t)^α = M^α·t^α`):
- `M^α ≥ 1` (e.g. `α = 0`, or `α ≥ 1 ∧ M ≥ 1`): max = 1, and
  `1 + t^α ≤ 1 + M^α·t^α` because `t^α ≤ M^α · t^α`.
- `M^α < 1` (necessarily `α ≥ 1 ∧ M < 1`): max = `(M^α)⁻¹ ≥ 1`, and
  `(M^α)⁻¹ · (1 + M^α·t^α) = (M^α)⁻¹ + t^α ≥ 1 + t^α`.

Bridges the natural-α PseudoMass majorant form `1/(1+(M·t)^α)` to the natural-α
form without the `M` factor; the prefactor `max(1, (M^α)⁻¹)` collapses to
`(M^α)⁻¹ = M^(-α)` when `M ≤ 1` (and `α ≥ 1`) and to `1` when `M^α ≥ 1`. Combined
with `one_div_one_add_t_pow_le_two_pow_mul_one_div_one_add_pow_pow` below, this
gives the bridge to the `(1+t)^(-α)` form expected by
`tsum_pow_neg_conv_le_const` (`IsingModel/PolyDecay.lean:207`). -/
theorem one_div_one_add_M_t_pow_le_max_mul_one_div_one_add_t_pow
    {α : ℕ} {M t : ℝ} (hM : 0 < M) (ht : 0 ≤ t) :
    1 / (1 + (M * t) ^ α) ≤ max 1 (M ^ α)⁻¹ * (1 / (1 + t ^ α)) := by
  have hMα_pos : 0 < M ^ α := pow_pos hM α
  have ht_α_nn : 0 ≤ t ^ α := pow_nonneg ht α
  have hMt_eq : (M * t) ^ α = M ^ α * t ^ α := mul_pow M t α
  have hMt_α_nn : 0 ≤ (M * t) ^ α := pow_nonneg (mul_nonneg hM.le ht) α
  have h_denom_left_pos : 0 < 1 + (M * t) ^ α := by linarith
  have h_denom_right_pos : 0 < 1 + t ^ α := by linarith
  have h_max_ge_one : (1 : ℝ) ≤ max 1 (M ^ α)⁻¹ := le_max_left _ _
  have h_max_pos : 0 < max 1 (M ^ α)⁻¹ := lt_of_lt_of_le zero_lt_one h_max_ge_one
  -- Key inequality: 1 + t^α ≤ max(1, (M^α)⁻¹) · (1 + M^α · t^α)
  have h_key : 1 + t ^ α ≤ max 1 (M ^ α)⁻¹ * (1 + M ^ α * t ^ α) := by
    by_cases hM_one : 1 ≤ M ^ α
    · -- M^α ≥ 1: max = 1
      have h_inv_le : (M ^ α)⁻¹ ≤ 1 := by
        rw [inv_le_one_iff₀]
        right; exact hM_one
      have h_max_eq : max 1 (M ^ α)⁻¹ = 1 := max_eq_left h_inv_le
      rw [h_max_eq, one_mul]
      have h_t_le : t ^ α ≤ M ^ α * t ^ α := by
        have : 1 * t ^ α ≤ M ^ α * t ^ α :=
          mul_le_mul_of_nonneg_right hM_one ht_α_nn
        linarith
      linarith
    · -- M^α < 1: max = (M^α)⁻¹
      have hM_lt : M ^ α < 1 := not_le.mp hM_one
      have h_inv_ge_one : (1 : ℝ) ≤ (M ^ α)⁻¹ :=
        one_le_inv_iff₀.mpr ⟨hMα_pos, hM_lt.le⟩
      have h_max_eq : max 1 (M ^ α)⁻¹ = (M ^ α)⁻¹ := max_eq_right h_inv_ge_one
      rw [h_max_eq]
      have h_expand : (M ^ α)⁻¹ * (1 + M ^ α * t ^ α) = (M ^ α)⁻¹ + t ^ α := by
        rw [mul_add, mul_one, ← mul_assoc,
            inv_mul_cancel₀ (ne_of_gt hMα_pos), one_mul]
      rw [h_expand]
      linarith
  -- Convert to goal: divide by (1+(M·t)^α) · (1+t^α)
  rw [mul_one_div, div_le_div_iff₀ h_denom_left_pos h_denom_right_pos]
  rw [one_mul, hMt_eq]
  exact h_key

/-- **Pointwise bridge from `1/(1+t^α)` to `1/(1+t)^α`** (Step 119 plan Step 5.5c bridge).

For `t ≥ 0`, `α : ℕ`:

    1 / (1 + t^α) ≤ 2^α · (1 / (1 + t)^α)

Equivalent to `(1+t)^α ≤ 2^α · (1+t^α)`, proved by case split:
- If `t ≤ 1`: `1+t ≤ 2`, so `(1+t)^α ≤ 2^α ≤ 2^α · (1+t^α)`.
- If `t > 1`: `1+t ≤ 2·t`, so `(1+t)^α ≤ (2t)^α = 2^α · t^α ≤ 2^α · (1+t^α)`.

Bridges the natural-α form `1/(1+t^α)` to the `(1+t)^(-α)` form used by the
discrete-HLS infinite sum `tsum_pow_neg_conv_le_const`. -/
theorem one_div_one_add_t_pow_le_two_pow_mul_one_div_one_add_pow_pow
    {α : ℕ} {t : ℝ} (ht : 0 ≤ t) :
    1 / (1 + t ^ α) ≤ (2 : ℝ) ^ α * (1 / (1 + t) ^ α) := by
  have h1t_pos : 0 < 1 + t := by linarith
  have h1t_α_pos : 0 < (1 + t) ^ α := pow_pos h1t_pos α
  have ht_α_nn : 0 ≤ t ^ α := pow_nonneg ht α
  have h_denom_left_pos : 0 < 1 + t ^ α := by linarith
  have h2_α_pos : (0 : ℝ) < 2 ^ α := pow_pos (by norm_num) α
  -- Key inequality: (1+t)^α ≤ 2^α · (1 + t^α)
  have h_key : (1 + t) ^ α ≤ (2 : ℝ) ^ α * (1 + t ^ α) := by
    by_cases h_t1 : t ≤ 1
    · -- 1+t ≤ 2
      have h_le_2 : 1 + t ≤ 2 := by linarith
      have h_pow_le : (1 + t) ^ α ≤ (2 : ℝ) ^ α :=
        pow_le_pow_left₀ h1t_pos.le h_le_2 α
      have h_one_le : (1 : ℝ) ≤ 1 + t ^ α := by linarith
      calc (1 + t) ^ α
          ≤ (2 : ℝ) ^ α := h_pow_le
        _ = (2 : ℝ) ^ α * 1 := by ring
        _ ≤ (2 : ℝ) ^ α * (1 + t ^ α) :=
            mul_le_mul_of_nonneg_left h_one_le h2_α_pos.le
    · -- 1+t ≤ 2·t
      have h_t1' : 1 < t := not_le.mp h_t1
      have h_le_2t : 1 + t ≤ 2 * t := by linarith
      have h_pow_le : (1 + t) ^ α ≤ (2 * t) ^ α :=
        pow_le_pow_left₀ h1t_pos.le h_le_2t α
      have h_split : (2 * t : ℝ) ^ α = (2 : ℝ) ^ α * t ^ α := mul_pow 2 t α
      have h_inner_le : t ^ α ≤ 1 + t ^ α := by linarith
      calc (1 + t) ^ α
          ≤ (2 * t : ℝ) ^ α := h_pow_le
        _ = (2 : ℝ) ^ α * t ^ α := h_split
        _ ≤ (2 : ℝ) ^ α * (1 + t ^ α) :=
            mul_le_mul_of_nonneg_left h_inner_le h2_α_pos.le
  -- Convert to goal
  rw [mul_one_div, div_le_div_iff₀ h_denom_left_pos h1t_α_pos, one_mul]
  exact h_key

/-- **HLS pointwise bridge: `1/(1+(M·t)^α)` to `(1+t)^(-α)`**
(Step 119 plan Step 5.5c, composition).

For `M > 0`, `t ≥ 0`, `α : ℕ`:

    1 / (1 + (M·t)^α) ≤ max(1, (M^α)⁻¹) · 2^α · (1 / (1 + t)^α)

Composition of `one_div_one_add_M_t_pow_le_max_mul_one_div_one_add_t_pow` (M-bridge,
isolating `max(1, (M^α)⁻¹)` prefactor) and
`one_div_one_add_t_pow_le_two_pow_mul_one_div_one_add_pow_pow` (form bridge to
`(1+t)^(-α)`).

This is the natural-α pointwise companion of the HLS infinite-sum bound
`tsum_pow_neg_conv_le_const` (`IsingModel/PolyDecay.lean:207`, real-α). The
constant prefactor `max(1, (M^α)⁻¹) · 2^α` collapses to
`(M^α)⁻¹ · 2^α = M^(-α) · 2^α` (the GJ p. 312 `m⁻^(-α)` scaling) in the
physically relevant `M ≤ 1` (and `α ≥ 1`) regime, and to `2^α` when `M^α ≥ 1`.
The `(1+t)^(-α)` body matches the existing tsum's polynomial-decay form. -/
theorem one_div_one_add_M_t_pow_le_const_mul_one_div_one_add_pow_pow
    {α : ℕ} {M t : ℝ} (hM : 0 < M) (ht : 0 ≤ t) :
    1 / (1 + (M * t) ^ α) ≤
      max 1 (M ^ α)⁻¹ * (2 : ℝ) ^ α * (1 / (1 + t) ^ α) := by
  have h1 := one_div_one_add_M_t_pow_le_max_mul_one_div_one_add_t_pow
    (M := M) (t := t) (α := α) hM ht
  have h2 := one_div_one_add_t_pow_le_two_pow_mul_one_div_one_add_pow_pow
    (t := t) (α := α) ht
  have h_max_pos : 0 < max 1 (M ^ α)⁻¹ :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  calc 1 / (1 + (M * t) ^ α)
      ≤ max 1 (M ^ α)⁻¹ * (1 / (1 + t ^ α)) := h1
    _ ≤ max 1 (M ^ α)⁻¹ * ((2 : ℝ) ^ α * (1 / (1 + t) ^ α)) :=
        mul_le_mul_of_nonneg_left h2 h_max_pos.le
    _ = max 1 (M ^ α)⁻¹ * (2 : ℝ) ^ α * (1 / (1 + t) ^ α) := by ring

/-- **Form bridge `1/(1+t)^α = (1+t)^(-(α : ℝ))`** (Step 119 plan Step 5.5c bridge).

For `t ≥ 0`, `α : ℕ`:

    1 / (1 + t)^α = (1 + t)^(-(α : ℝ))

where the LHS uses the natural-α `HPow ℝ ℕ ℝ` instance and the RHS uses
`Real.rpow`. Identity bridge to the real-α form expected by the existing
infinite-sum infrastructure `tsum_pow_neg_conv_le_const`
(`IsingModel/PolyDecay.lean:207`). -/
theorem one_div_one_add_pow_eq_rpow_neg {α : ℕ} {t : ℝ} (ht : 0 ≤ t) :
    1 / (1 + t) ^ α = (1 + t) ^ (-(α : ℝ)) := by
  have h1t_nn : 0 ≤ 1 + t := by linarith
  rw [Real.rpow_neg h1t_nn, Real.rpow_natCast, one_div]

/-- **Pair pointwise HLS bridge** (Step 119 plan Step 5.5c, pair form).

For `M > 0`, `tx, ty ≥ 0`, `α : ℕ`:

    1/(1+(M·tx)^α) · 1/(1+(M·ty)^α)
      ≤ (max(1, (M^α)⁻¹) · 2^α)² · (1/(1+tx)^α · 1/(1+ty)^α)

Pair form of `one_div_one_add_M_t_pow_le_const_mul_one_div_one_add_pow_pow`,
obtained by applying the scalar bridge to each factor and combining via
`mul_le_mul`. The squared constant `C² = (max(1, (M^α)⁻¹) · 2^α)²` collapses
to `M^(-2α) · 2^(2α)` (the GJ p. 312 `m⁻^(-2α)` scaling) when `M ≤ 1` and
`α ≥ 1`. Ready for summation with the existing `tsum_pow_neg_conv_le_const`
(via `one_div_one_add_pow_eq_rpow_neg`). -/
theorem one_div_one_add_M_t_pow_pair_le_const_sq_mul_one_div_one_add_pow_pow
    {α : ℕ} {M tx ty : ℝ} (hM : 0 < M) (htx : 0 ≤ tx) (hty : 0 ≤ ty) :
    1 / (1 + (M * tx) ^ α) * (1 / (1 + (M * ty) ^ α)) ≤
      (max 1 (M ^ α)⁻¹ * (2 : ℝ) ^ α) ^ 2 *
        (1 / (1 + tx) ^ α * (1 / (1 + ty) ^ α)) := by
  have h1 := one_div_one_add_M_t_pow_le_const_mul_one_div_one_add_pow_pow
    (M := M) (t := tx) (α := α) hM htx
  have h2 := one_div_one_add_M_t_pow_le_const_mul_one_div_one_add_pow_pow
    (M := M) (t := ty) (α := α) hM hty
  have h_max_pos : 0 < max 1 (M ^ α)⁻¹ :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have h_2pow_pos : (0 : ℝ) < (2 : ℝ) ^ α := pow_pos (by norm_num) α
  have hC_pos : 0 < max 1 (M ^ α)⁻¹ * (2 : ℝ) ^ α := mul_pos h_max_pos h_2pow_pos
  have hMty_inv_nn : 0 ≤ 1 / (1 + (M * ty) ^ α) := by
    apply div_nonneg (by norm_num)
    have : 0 ≤ (M * ty) ^ α := pow_nonneg (mul_nonneg hM.le hty) α
    linarith
  have h_rhs_factor_nn : 0 ≤ max 1 (M ^ α)⁻¹ * (2 : ℝ) ^ α * (1 / (1 + tx) ^ α) := by
    apply mul_nonneg hC_pos.le
    apply div_nonneg (by norm_num)
    exact pow_nonneg (by linarith) α
  calc 1 / (1 + (M * tx) ^ α) * (1 / (1 + (M * ty) ^ α))
      ≤ (max 1 (M ^ α)⁻¹ * (2 : ℝ) ^ α * (1 / (1 + tx) ^ α)) *
          (max 1 (M ^ α)⁻¹ * (2 : ℝ) ^ α * (1 / (1 + ty) ^ α)) := by
        exact mul_le_mul h1 h2 hMty_inv_nn h_rhs_factor_nn
    _ = (max 1 (M ^ α)⁻¹ * (2 : ℝ) ^ α) ^ 2 *
          (1 / (1 + tx) ^ α * (1 / (1 + ty) ^ α)) := by ring

/-- `pseudoMassG` is at most 2 for `t ≥ 0` and `r > 0`.
Corollary of `pseudoMassG_le_two_div_one_add_pow`. -/
theorem pseudoMassG_le_two (α : ℕ) {r t : ℝ} (ht : 0 ≤ t) (hr : 0 < r) :
    pseudoMassG α r t ≤ 2 := by
  unfold pseudoMassG
  have hdenom_pos : (0 : ℝ) < 1 + (t * r) ^ α := by
    have h : 0 ≤ (t * r) ^ α := pow_nonneg (mul_nonneg ht hr.le) α
    linarith
  rw [div_le_iff₀ hdenom_pos]
  have hexp : Real.exp (-(t * r)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg ht hr.le))
  have hdenom_ge : 1 ≤ 1 + (t * r) ^ α := by
    have h : 0 ≤ (t * r) ^ α := pow_nonneg (mul_nonneg ht hr.le) α
    linarith
  nlinarith [Real.exp_pos (-(t * r))]

/-- The denominator `1 + (t·r)^α` is strictly increasing in `t` for `r > 0`, `α ≥ 1`. -/
private lemma pseudoMassG_denom_strictMono
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) :
    StrictMonoOn (fun t => 1 + (t * r) ^ α) (Ici 0) := by
  intro s hs t ht hst
  change 1 + (s * r) ^ α < 1 + (t * r) ^ α
  apply add_lt_add_of_le_of_lt le_rfl
  exact pow_lt_pow_left₀ (mul_lt_mul_of_pos_right hst hr)
    (mul_nonneg (Set.mem_Ici.mp hs) hr.le) (Nat.one_le_iff_ne_zero.mp hα)

/-- `pseudoMassG` is strictly decreasing in `t` on `[0, ∞)` for `r > 0`, `α ≥ 1`. -/
theorem pseudoMassG_strictAntiOn
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) :
    StrictAntiOn (pseudoMassG α r) (Ici 0) := by
  intro s hs t ht hst
  unfold pseudoMassG
  apply div_lt_div₀'
  · -- 2 * exp(-(t*r)) ≤ 2 * exp(-(s*r)): exp is monotone and -(t*r) ≤ -(s*r)
    apply mul_le_mul_of_nonneg_left _ two_pos.le
    apply Real.exp_le_exp.mpr
    linarith [mul_lt_mul_of_pos_right hst hr]
  · -- 1 + (s*r)^α < 1 + (t*r)^α
    exact pseudoMassG_denom_strictMono hα hr hs ht hst
  · -- 0 < 2 * exp(-s*r)
    exact mul_pos two_pos (Real.exp_pos _)
  · -- 0 < 1 + (s*r)^α
    have h : 0 ≤ (s * r) ^ α :=
      pow_nonneg (mul_nonneg (Set.mem_Ici.mp hs) hr.le) α
    linarith

/-- **`pseudoMassG α r` is `AnalyticAt` at every `t ≥ 0`** (for `r > 0`):
the function `2 · exp(-(t·r)) / (1 + (t·r)^α)` is a quotient of analytic
functions with non-vanishing denominator on `[0, ∞)`, hence analytic
everywhere on the closed half-line. -/
theorem pseudoMassG_analyticAt (α : ℕ) {r : ℝ} (hr : 0 < r) {t : ℝ} (ht : 0 ≤ t) :
    AnalyticAt ℝ (pseudoMassG α r) t := by
  unfold pseudoMassG
  have h_tr : AnalyticAt ℝ (fun x : ℝ => x * r) t :=
    analyticAt_id.mul (analyticAt_const)
  have h_neg_tr : AnalyticAt ℝ (fun x : ℝ => -(x * r)) t :=
    h_tr.neg
  have h_exp : AnalyticAt ℝ (fun x : ℝ => Real.exp (-(x * r))) t :=
    analyticAt_rexp.comp h_neg_tr
  have h_two_exp : AnalyticAt ℝ (fun x : ℝ => 2 * Real.exp (-(x * r))) t :=
    analyticAt_const.mul h_exp
  have h_pow : AnalyticAt ℝ (fun x : ℝ => (x * r) ^ α) t :=
    h_tr.pow α
  have h_denom : AnalyticAt ℝ (fun x : ℝ => 1 + (x * r) ^ α) t :=
    analyticAt_const.add h_pow
  have h_denom_ne : (1 + (t * r) ^ α) ≠ 0 := by
    have h_pow_nn : 0 ≤ (t * r) ^ α := pow_nonneg (mul_nonneg ht hr.le) α
    linarith
  exact h_two_exp.div h_denom h_denom_ne

/-- **`pseudoMassG α r` is `AnalyticWithinAt ℝ ... (Ici 0)`** at every
`t ≥ 0` (for `r > 0`): lift `pseudoMassG_analyticAt` (PR #1695)
via `.analyticWithinAt`. Useful at the boundary `t = 0` where
`AnalyticOnNhd` over Ici 0 would require a 2-sided neighborhood. -/
theorem pseudoMassG_analyticWithinAt_Ici_zero (α : ℕ) {r : ℝ} (hr : 0 < r)
    {t : ℝ} (ht : 0 ≤ t) :
    AnalyticWithinAt ℝ (pseudoMassG α r) (Set.Ici 0) t :=
  (pseudoMassG_analyticAt α hr ht).analyticWithinAt


/-- **`pseudoMassG α r` is `ContinuousWithinAt (Ici 0)`** at any
`t ≥ 0`: corollary of `_analyticWithinAt_Ici_zero` via
`AnalyticWithinAt.continuousWithinAt`. Useful at the boundary
`t = 0` where 2-sided continuity isn't directly accessible. -/
theorem pseudoMassG_continuousWithinAt_Ici_zero (α : ℕ) {r : ℝ} (hr : 0 < r)
    {t : ℝ} (ht : 0 ≤ t) :
    ContinuousWithinAt (pseudoMassG α r) (Set.Ici 0) t :=
  (pseudoMassG_analyticWithinAt_Ici_zero α hr ht).continuousWithinAt

/-- **For even `α`, `pseudoMassG α r` is `AnalyticAt` everywhere on `ℝ`**
(`r > 0`): the denominator `1 + (t·r)^α` is bounded below by `1 > 0`
since `(t·r)^α ≥ 0` for even `α`, so the quotient is analytic on all
of `ℝ`. -/
theorem pseudoMassG_analyticAt_of_even {α : ℕ} (hα_even : Even α) (r t : ℝ) :
    AnalyticAt ℝ (pseudoMassG α r) t := by
  unfold pseudoMassG
  have h_tr : AnalyticAt ℝ (fun x : ℝ => x * r) t :=
    analyticAt_id.mul (analyticAt_const)
  have h_neg_tr : AnalyticAt ℝ (fun x : ℝ => -(x * r)) t :=
    h_tr.neg
  have h_exp : AnalyticAt ℝ (fun x : ℝ => Real.exp (-(x * r))) t :=
    analyticAt_rexp.comp h_neg_tr
  have h_two_exp : AnalyticAt ℝ (fun x : ℝ => 2 * Real.exp (-(x * r))) t :=
    analyticAt_const.mul h_exp
  have h_pow : AnalyticAt ℝ (fun x : ℝ => (x * r) ^ α) t :=
    h_tr.pow α
  have h_denom : AnalyticAt ℝ (fun x : ℝ => 1 + (x * r) ^ α) t :=
    analyticAt_const.add h_pow
  have h_pow_nn : 0 ≤ (t * r) ^ α := hα_even.pow_nonneg _
  have h_denom_ne : (1 + (t * r) ^ α) ≠ 0 := by linarith
  exact h_two_exp.div h_denom h_denom_ne

/-- **For even `α`, `pseudoMassG α r` is `AnalyticOnNhd ℝ` on
`Set.univ`**: lift `_analyticAt_of_even` to a set-level form on all
of `ℝ`. -/
theorem pseudoMassG_analyticOnNhd_univ_of_even {α : ℕ} (hα_even : Even α)
    (r : ℝ) :
    AnalyticOnNhd ℝ (pseudoMassG α r) Set.univ := by
  intro t _
  exact pseudoMassG_analyticAt_of_even hα_even r t

/-- **`-pseudoMassG α r` is `StrictMonoOn (Ici 0)`**: dual of
`pseudoMassG_strictAntiOn`. -/
theorem neg_pseudoMassG_strictMonoOn {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) :
    StrictMonoOn (fun t : ℝ => -pseudoMassG α r t) (Set.Ici 0) := by
  intro t₁ ht₁ t₂ ht₂ h
  have hgt : pseudoMassG α r t₂ < pseudoMassG α r t₁ :=
    pseudoMassG_strictAntiOn hα hr ht₁ ht₂ h
  linarith

/-- **`pseudoMassG(t₂) < pseudoMassG(t₁) ↔ t₁ < t₂`** (for `t₁, t₂ ≥ 0`,
`r > 0`, `α ≥ 1`): iff form of `pseudoMassG_strictAntiOn`. -/
theorem pseudoMassG_lt_iff {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {t₁ t₂ : ℝ} (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂) :
    pseudoMassG α r t₂ < pseudoMassG α r t₁ ↔ t₁ < t₂ := by
  have hanti := pseudoMassG_strictAntiOn hα hr
  refine ⟨?_, fun h => hanti (Set.mem_Ici.mpr ht₁) (Set.mem_Ici.mpr ht₂) h⟩
  intro hlt
  by_contra h_neg
  have h_neg' : t₂ ≤ t₁ := not_lt.mp h_neg
  rcases h_neg'.lt_or_eq with hlt_t | heq_t
  · have := hanti (Set.mem_Ici.mpr ht₂) (Set.mem_Ici.mpr ht₁) hlt_t
    linarith
  · subst heq_t
    exact lt_irrefl _ hlt

/-- **`pseudoMassG(t₂) ≤ pseudoMassG(t₁) ↔ t₁ ≤ t₂`** (non-strict). -/
theorem pseudoMassG_le_iff {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {t₁ t₂ : ℝ} (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂) :
    pseudoMassG α r t₂ ≤ pseudoMassG α r t₁ ↔ t₁ ≤ t₂ := by
  have hanti := pseudoMassG_strictAntiOn hα hr
  refine ⟨?_, ?_⟩
  · intro hle
    by_contra h_neg
    have h_neg' : t₂ < t₁ := not_le.mp h_neg
    have := hanti (Set.mem_Ici.mpr ht₂) (Set.mem_Ici.mpr ht₁) h_neg'
    linarith
  · intro hle
    rcases hle.lt_or_eq with hlt | heq
    · exact (hanti (Set.mem_Ici.mpr ht₁) (Set.mem_Ici.mpr ht₂) hlt).le
    · subst heq; exact le_refl _

/-- **`pseudoMassG α r` is `AntitoneOn (Ici 0)`**: non-strict form. -/
theorem pseudoMassG_antitoneOn {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) :
    AntitoneOn (pseudoMassG α r) (Set.Ici (0 : ℝ)) :=
  (pseudoMassG_strictAntiOn hα hr).antitoneOn

/-- **`pseudoMassG α r t < 2` for `t > 0` (strict at positive `t`)**:
direct corollary of `pseudoMassG_strictAntiOn` (strict anti on `Ici 0`)
and `pseudoMassG_zero` (`g(0) = 2`). Sharpens `pseudoMassG_le_two`
to a strict inequality away from `t = 0`. -/
theorem pseudoMassG_lt_two_of_pos {α : ℕ} (hα : 1 ≤ α) {r t : ℝ}
    (ht : 0 < t) (hr : 0 < r) :
    pseudoMassG α r t < 2 := by
  have h_anti := pseudoMassG_strictAntiOn hα hr
  have hzero : pseudoMassG α r 0 = 2 := pseudoMassG_zero hα r
  have hlt : pseudoMassG α r t < pseudoMassG α r 0 :=
    h_anti (Set.mem_Ici.mpr (le_refl 0)) (Set.mem_Ici.mpr ht.le) ht
  rw [hzero] at hlt
  exact hlt

/-- **`pseudoMassG α r t < 2 ↔ 0 < t`** (for `t ≥ 0`, `r > 0`,
`α ≥ 1`): combines `_lt_two_of_pos` (forward, t > 0 → g < 2) with
`pseudoMassG_zero` (reverse: t = 0 → g = 2 ≥ 2 contradicts g < 2). -/
theorem pseudoMassG_lt_two_iff_pos {α : ℕ} (hα : 1 ≤ α) {r t : ℝ}
    (ht : 0 ≤ t) (hr : 0 < r) :
    pseudoMassG α r t < 2 ↔ 0 < t := by
  refine ⟨?_, fun h => pseudoMassG_lt_two_of_pos hα h hr⟩
  intro hlt
  by_contra h_neg
  have h_neg' : t ≤ 0 := not_lt.mp h_neg
  have ht_eq : t = 0 := le_antisymm h_neg' ht
  rw [ht_eq, pseudoMassG_zero hα] at hlt
  exact lt_irrefl _ hlt

/-- **`pseudoMassG α r t = 2 ↔ t = 0`** (for `t ≥ 0`, `r > 0`,
`α ≥ 1`): boundary value characterisation. Forward via
`pseudoMassG_le_two` (≤ 2) + `pseudoMassG_lt_two_iff_pos` (strict
< 2 iff t > 0). Reverse: direct from `pseudoMassG_zero`. -/
theorem pseudoMassG_eq_two_iff_zero {α : ℕ} (hα : 1 ≤ α) {r t : ℝ}
    (ht : 0 ≤ t) (hr : 0 < r) :
    pseudoMassG α r t = 2 ↔ t = 0 := by
  refine ⟨?_, fun h_eq => by rw [h_eq]; exact pseudoMassG_zero hα r⟩
  intro h_eq
  by_contra h_ne
  have ht_pos : 0 < t := lt_of_le_of_ne ht (Ne.symm h_ne)
  have h_lt : pseudoMassG α r t < 2 := pseudoMassG_lt_two_of_pos hα ht_pos hr
  rw [h_eq] at h_lt
  exact lt_irrefl _ h_lt

/-- **Correlation decay bound via global pseudo-mass** (Step 132b):
If `pseudoMassG α 1 m₁ = c` (defining equation for per-pair pseudo-mass `m₁ = m^-_{x,z} · d(x,z)`)
and `m₀ ≤ m₁` (e.g. `m₀ = m^-_global · d(x,z)` with `m^-_global ≤ m^-_{x,z}`), then
`c ≤ 2 / (1 + m₀^α)`.

Proof: `c = pseudoMassG(m₁) ≤ pseudoMassG(m₀)` (strict antitonicity) `≤ 2/(1+m₀^α)` (Step 132a).

This is the abstract form of GJ §17.5 p.312: `⟨φ(x)φ(z)⟩/A ≤ 2/(1+(m^-_global·d(x,z))^α)`.
Combined with the Lebowitz bound and HLS (Step 130), this yields the `hc_der` hypothesis
for `pseudoMass_power_deriv_le` (Step 131b).

**References**: Glimm–Jaffe §17.5, Theorem 17.5.1 proof, pp.311–312
(the bound `c_{x,z} ≤ 2/(1+(m^-_global·d)^α)` used on p.312). -/
theorem pseudoMassG_le_two_div_one_add_pow_of_preimage_le
    {α : ℕ} (hα : 1 ≤ α) {m₀ m₁ : ℝ}
    (hm₀ : 0 ≤ m₀) (hle : m₀ ≤ m₁)
    {c : ℝ} (heq : pseudoMassG α 1 m₁ = c) :
    c ≤ 2 / (1 + m₀ ^ α) := by
  have h_anti := (pseudoMassG_strictAntiOn hα one_pos).antitoneOn
  have hm₀_mem : m₀ ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr hm₀
  have hm₁_mem : m₁ ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr (le_trans hm₀ hle)
  have hstep_a := pseudoMassG_le_two_div_one_add_pow α hm₀ one_pos
  simp only [mul_one] at hstep_a
  calc c = pseudoMassG α 1 m₁ := heq.symm
      _ ≤ pseudoMassG α 1 m₀ := h_anti hm₀_mem hm₁_mem hle
      _ ≤ 2 / (1 + m₀ ^ α) := hstep_a

/-- `pseudoMassG` is continuous on `[0, ∞)`. -/
theorem pseudoMassG_continuousOn (α : ℕ) {r : ℝ} (hr : 0 < r) :
    ContinuousOn (pseudoMassG α r) (Ici 0) := by
  unfold pseudoMassG
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro t ht
    have ht' : 0 ≤ t := Set.mem_Ici.mp ht
    have h : 0 ≤ (t * r) ^ α := pow_nonneg (mul_nonneg ht' hr.le) α
    exact ne_of_gt (by linarith)

/-- **`pseudoMassG α r` is `ContinuousOn (Ioi 0)`**: sub-interval form. -/
theorem pseudoMassG_continuousOn_Ioi_zero (α : ℕ) {r : ℝ} (hr : 0 < r) :
    ContinuousOn (pseudoMassG α r) (Set.Ioi (0 : ℝ)) := by
  apply (pseudoMassG_continuousOn α hr).mono
  intro t ht
  exact Set.mem_Ici.mpr (le_of_lt ht)

/-- **`pseudoMassG α r` is `ContinuousAt t` for `t > 0`**: pointwise
form. -/
theorem pseudoMassG_continuousAt_of_pos (α : ℕ) {r : ℝ} (hr : 0 < r)
    {t : ℝ} (ht : 0 < t) :
    ContinuousAt (pseudoMassG α r) t :=
  (pseudoMassG_analyticAt α hr ht.le).continuousAt

/-- **`pseudoMassG α r` is `DifferentiableAt t` for `t ≥ 0`**: from
`pseudoMassG_analyticAt`. -/
theorem pseudoMassG_differentiableAt (α : ℕ) {r : ℝ} (hr : 0 < r)
    {t : ℝ} (ht : 0 ≤ t) :
    DifferentiableAt ℝ (pseudoMassG α r) t :=
  (pseudoMassG_analyticAt α hr ht).differentiableAt

/-- **`pseudoMassG α r` is `DifferentiableOn ℝ ... (Ioi 0)`**: lifted
from `differentiableAt`. -/
theorem pseudoMassG_differentiableOn_Ioi_zero (α : ℕ) {r : ℝ} (hr : 0 < r) :
    DifferentiableOn ℝ (pseudoMassG α r) (Set.Ioi (0 : ℝ)) := by
  intro t ht
  exact (pseudoMassG_differentiableAt α hr ht.le).differentiableWithinAt

/-- **`pseudoMassG α r` is `DifferentiableAt t` for `t > 0`**: pointwise
form on the open positive line. -/
theorem pseudoMassG_differentiableAt_of_pos (α : ℕ) {r : ℝ} (hr : 0 < r)
    {t : ℝ} (ht : 0 < t) :
    DifferentiableAt ℝ (pseudoMassG α r) t :=
  pseudoMassG_differentiableAt α hr ht.le

/-- `pseudoMassG` tends to 0 as `t → ∞` for `r > 0`. -/
theorem pseudoMassG_tendsto_zero (α : ℕ) {r : ℝ} (hr : 0 < r) :
    Filter.Tendsto (pseudoMassG α r) Filter.atTop (nhds 0) := by
  -- Squeeze between 0 and 2 * exp(-t*r)
  apply squeeze_zero'
  · -- lower bound: g(t) ≥ 0 eventually (for t ≥ 0)
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    exact le_of_lt (pseudoMassG_pos α ht hr)
  · -- upper bound: g(t) ≤ 2 * exp(-t*r) for t ≥ 0
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    unfold pseudoMassG
    apply div_le_self (by positivity)
    have h : 0 ≤ (t * r) ^ α := pow_nonneg (mul_nonneg ht hr.le) α
    linarith
  · -- 2 * exp(-(t*r)) → 0 as t → ∞
    have h_tr_atTop : Filter.Tendsto (fun t : ℝ => t * r) Filter.atTop Filter.atTop :=
      Filter.tendsto_id.atTop_mul_const hr
    have h_exp_zero : Filter.Tendsto (fun t : ℝ => Real.exp (-(t * r))) Filter.atTop (nhds 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp h_tr_atTop
    have key : Filter.Tendsto (fun t : ℝ => 2 * Real.exp (-(t * r))) Filter.atTop (nhds (2 * 0)) :=
      tendsto_const_nhds.mul h_exp_zero
    simpa using key


end IsingModel

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

/-- **`pseudoMassG α r t < 2·exp(-(t·r))`** (for `t > 0`, `r > 0`,
`α ≥ 1`): since the denominator `1 + (tr)^α > 1` strictly when
`tr > 0`, the quotient is strictly dominated. -/
theorem pseudoMassG_lt_two_mul_exp_of_pos {α : ℕ} (hα : 1 ≤ α) {r t : ℝ}
    (ht : 0 < t) (hr : 0 < r) :
    pseudoMassG α r t < 2 * Real.exp (-(t * r)) := by
  unfold pseudoMassG
  have htr_pos : 0 < t * r := mul_pos ht hr
  -- (t*r)^α > 0 since t*r > 0 and α ≥ 1
  have h_pow_pos : 0 < (t * r) ^ α := pow_pos htr_pos α
  have h_denom_pos : 0 < 1 + (t * r) ^ α := by linarith
  have h_denom_gt_one : 1 < 1 + (t * r) ^ α := by linarith
  have h_exp_pos : 0 < Real.exp (-(t * r)) := Real.exp_pos _
  rw [div_lt_iff₀ h_denom_pos]
  -- Suppress unused warning by linking hα
  have := hα
  nlinarith

/-- **`pseudoMassG α r t ≠ 0`** for `t ≥ 0`, `r > 0`: direct from
`pseudoMassG_pos`. Useful when `≠ 0` form is needed (e.g., division). -/
theorem pseudoMassG_ne_zero (α : ℕ) {r t : ℝ} (ht : 0 ≤ t) (hr : 0 < r) :
    pseudoMassG α r t ≠ 0 :=
  (pseudoMassG_pos α ht hr).ne'

/-- **`pseudoMassG α r t ∈ Set.Ioi 0`** for `t ≥ 0`, `r > 0`. -/
theorem pseudoMassG_mem_Ioi_zero (α : ℕ) {r t : ℝ} (ht : 0 ≤ t) (hr : 0 < r) :
    pseudoMassG α r t ∈ Set.Ioi (0 : ℝ) :=
  pseudoMassG_pos α ht hr

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

/-- **`pseudoMassG α r t ∈ Set.Ioc 0 2`** for `t ≥ 0`, `r > 0`,
combining pos and ≤ 2. -/
theorem pseudoMassG_mem_Ioc_zero_two (α : ℕ) {r t : ℝ} (ht : 0 ≤ t) (hr : 0 < r) :
    pseudoMassG α r t ∈ Set.Ioc (0 : ℝ) 2 :=
  ⟨pseudoMassG_pos α ht hr, pseudoMassG_le_two α ht hr⟩

/-- **`pseudoMassG α r t ∈ Set.Ici 0`** for `t ≥ 0`, `r > 0`. -/
theorem pseudoMassG_mem_Ici_zero (α : ℕ) {r t : ℝ} (ht : 0 ≤ t) (hr : 0 < r) :
    pseudoMassG α r t ∈ Set.Ici (0 : ℝ) :=
  le_of_lt (pseudoMassG_pos α ht hr)

/-- **`pseudoMassG α r t ∈ Set.Iic 2`** for `t ≥ 0`, `r > 0`. -/
theorem pseudoMassG_mem_Iic_two (α : ℕ) {r t : ℝ} (ht : 0 ≤ t) (hr : 0 < r) :
    pseudoMassG α r t ∈ Set.Iic (2 : ℝ) :=
  pseudoMassG_le_two α ht hr

/-- **`pseudoMassG α r t ∉ Set.Iio 0`**: trivial via positive. -/
theorem pseudoMassG_not_mem_Iio_zero (α : ℕ) {r t : ℝ} (ht : 0 ≤ t) (hr : 0 < r) :
    pseudoMassG α r t ∉ Set.Iio (0 : ℝ) :=
  not_lt.mpr (le_of_lt (pseudoMassG_pos α ht hr))

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

/-- **`pseudoMassG α r` is `AnalyticOnNhd ℝ` on `Ioi 0`** (for `r > 0`):
lift `pseudoMassG_analyticAt` to a global form on the open positive
real interval. -/
theorem pseudoMassG_analyticOnNhd_Ioi_zero (α : ℕ) {r : ℝ} (hr : 0 < r) :
    AnalyticOnNhd ℝ (pseudoMassG α r) (Set.Ioi 0) := by
  intro t ht
  exact pseudoMassG_analyticAt α hr (le_of_lt ht)

/-- **`pseudoMassG α r` is `AnalyticWithinAt ℝ ... (Ici 0)`** at every
`t ≥ 0` (for `r > 0`): lift `pseudoMassG_analyticAt` (PR #1695)
via `.analyticWithinAt`. Useful at the boundary `t = 0` where
`AnalyticOnNhd` over Ici 0 would require a 2-sided neighborhood. -/
theorem pseudoMassG_analyticWithinAt_Ici_zero (α : ℕ) {r : ℝ} (hr : 0 < r)
    {t : ℝ} (ht : 0 ≤ t) :
    AnalyticWithinAt ℝ (pseudoMassG α r) (Set.Ici 0) t :=
  (pseudoMassG_analyticAt α hr ht).analyticWithinAt

/-- **`pseudoMassG α r` is `AnalyticOn ℝ ... (Ici 0)`**: set-level
form of `_analyticWithinAt_Ici_zero`. -/
theorem pseudoMassG_analyticOn_Ici_zero (α : ℕ) {r : ℝ} (hr : 0 < r) :
    AnalyticOn ℝ (pseudoMassG α r) (Set.Ici 0) := by
  intro t ht
  exact pseudoMassG_analyticWithinAt_Ici_zero α hr (Set.mem_Ici.mp ht)


/-- **`pseudoMassG α r` is `ContinuousWithinAt (Ici 0)`** at any
`t ≥ 0`: corollary of `_analyticWithinAt_Ici_zero` via
`AnalyticWithinAt.continuousWithinAt`. Useful at the boundary
`t = 0` where 2-sided continuity isn't directly accessible. -/
theorem pseudoMassG_continuousWithinAt_Ici_zero (α : ℕ) {r : ℝ} (hr : 0 < r)
    {t : ℝ} (ht : 0 ≤ t) :
    ContinuousWithinAt (pseudoMassG α r) (Set.Ici 0) t :=
  (pseudoMassG_analyticWithinAt_Ici_zero α hr ht).continuousWithinAt

/-- **`pseudoMassG α r` is `DifferentiableWithinAt ℝ ... (Ici 0)`**
at any `t ≥ 0`: corollary of `_analyticWithinAt_Ici_zero` via
`AnalyticWithinAt.differentiableWithinAt`. -/
theorem pseudoMassG_differentiableWithinAt_Ici_zero (α : ℕ) {r : ℝ} (hr : 0 < r)
    {t : ℝ} (ht : 0 ≤ t) :
    DifferentiableWithinAt ℝ (pseudoMassG α r) (Set.Ici 0) t := by
  have h_insert : insert t (Set.Ici (0 : ℝ)) = Set.Ici 0 := by
    apply Set.insert_eq_self.mpr
    exact Set.mem_Ici.mpr ht
  have h := (pseudoMassG_analyticWithinAt_Ici_zero α hr ht).differentiableWithinAt
  rwa [h_insert] at h

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

/-- **For even `α`, `pseudoMassG α r` is `Continuous`**: lift
`_analyticAt_of_even` to global continuity. -/
theorem pseudoMassG_continuous_of_even {α : ℕ} (hα_even : Even α) (r : ℝ) :
    Continuous (pseudoMassG α r) :=
  continuous_iff_continuousAt.mpr fun t =>
    (pseudoMassG_analyticAt_of_even hα_even r t).continuousAt

/-- **For even `α`, `pseudoMassG α r` is `Differentiable ℝ`**. -/
theorem pseudoMassG_differentiable_of_even {α : ℕ} (hα_even : Even α) (r : ℝ) :
    Differentiable ℝ (pseudoMassG α r) :=
  fun t => (pseudoMassG_analyticAt_of_even hα_even r t).differentiableAt

/-- **For even `α`, `pseudoMassG α r` is `AnalyticOn ℝ Set.univ`**. -/
theorem pseudoMassG_analyticOn_univ_of_even {α : ℕ} (hα_even : Even α)
    (r : ℝ) :
    AnalyticOn ℝ (pseudoMassG α r) Set.univ :=
  (pseudoMassG_analyticOnNhd_univ_of_even hα_even r).analyticOn

/-- **`-pseudoMassG α r` is `StrictMonoOn (Ici 0)`**: dual of
`pseudoMassG_strictAntiOn`. -/
theorem neg_pseudoMassG_strictMonoOn {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) :
    StrictMonoOn (fun t : ℝ => -pseudoMassG α r t) (Set.Ici 0) := by
  intro t₁ ht₁ t₂ ht₂ h
  have hgt : pseudoMassG α r t₂ < pseudoMassG α r t₁ :=
    pseudoMassG_strictAntiOn hα hr ht₁ ht₂ h
  linarith

/-- **`-pseudoMassG α r` is `StrictMonoOn (Ioi 0)`**: sub-interval form. -/
theorem neg_pseudoMassG_strictMonoOn_Ioi_zero
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) :
    StrictMonoOn (fun t : ℝ => -pseudoMassG α r t) (Set.Ioi 0) := by
  intro t₁ ht₁ t₂ ht₂ h
  exact (neg_pseudoMassG_strictMonoOn hα hr) (Set.mem_Ici.mpr (le_of_lt ht₁))
    (Set.mem_Ici.mpr (le_of_lt ht₂)) h

/-- **`-pseudoMassG α r` is `MonotoneOn (Ici 0)`**: non-strict. -/
theorem neg_pseudoMassG_monotoneOn {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) :
    MonotoneOn (fun t : ℝ => -pseudoMassG α r t) (Set.Ici 0) :=
  (neg_pseudoMassG_strictMonoOn hα hr).monotoneOn

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

/-- **`pseudoMassG(t₂) = pseudoMassG(t₁) ↔ t₁ = t₂`** (for `t₁, t₂ ≥ 0`):
strict anti is injective, so equality on values reverses to equality
on arguments. -/
theorem pseudoMassG_eq_iff_eq {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {t₁ t₂ : ℝ} (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂) :
    pseudoMassG α r t₂ = pseudoMassG α r t₁ ↔ t₁ = t₂ := by
  refine ⟨?_, ?_⟩
  · intro heq
    have h1 := (pseudoMassG_le_iff hα hr ht₁ ht₂).mp heq.le
    have h2 := (pseudoMassG_le_iff hα hr ht₂ ht₁).mp heq.ge
    linarith
  · intro heq_t
    subst heq_t
    rfl

/-- **`pseudoMassG α r` is `StrictAntiOn (Ioi 0)`**: sub-interval form
of `pseudoMassG_strictAntiOn` on `Ici 0`. -/
theorem pseudoMassG_strictAntiOn_Ioi_zero {α : ℕ} (hα : 1 ≤ α) {r : ℝ}
    (hr : 0 < r) :
    StrictAntiOn (pseudoMassG α r) (Set.Ioi (0 : ℝ)) := by
  intro s hs t ht hst
  exact pseudoMassG_strictAntiOn hα hr (Set.mem_Ici.mpr (le_of_lt hs))
    (Set.mem_Ici.mpr (le_of_lt ht)) hst

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

import IsingModel.AmbientLattice
import IsingModel.BetaDerivative
import IsingModel.PolyDecay
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Pseudo-mass construction for GJ §17.5 Theorem 17.5.1 (Step 117c)

The pseudo-mass `m⁻(β, A)` of Glimm–Jaffe §17.5 (2nd ed., pp. 311–312)
is the key analytic tool for proving continuity of the lattice mass.

For a finite volume `A ⊂ ℤ^d`, distinct `x, y ∈ A`, and integer parameter `α ≥ 1`
(a special case of GJ's general `α > d/2`):
the pseudo-mass `m⁻(x, y, β, A)` is the unique `t ≥ 0` satisfying

  `2 · exp(-t · dist(x,y)) / (1 + (t · dist(x,y))^α) = ⟨σ_x σ_y⟩_{β,A}`

Its key properties:
* m⁻(β, A) is strictly positive for bounded connected A
* 0 ≤ m⁻(β) ≤ latticeMass(β) ≤ const · m⁻(β)
* m⁻(β, A)^{2α+1} is Lipschitz continuous in β uniformly in A

These properties give continuity of latticeMass in β (Thm 17.5.1).

## Main results

* `pseudoMassG_strictAntiOn` — g(t,r,α) is strictly decreasing in t for r > 0
* `pseudoMassG_zero` — g(0,r,α) = 2
* `pseudoMassG_tendsto_zero` — g(t,r,α) → 0 as t → ∞
* `pseudoMassG_exists_of_mem_Ioo` — existence for c ∈ (0,2)
* `pseudoMassG_unique` — uniqueness

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.5 pp. 310–312, Springer 1987.
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

/-! ## Existence and uniqueness of pseudo-mass -/

/-- For `c ∈ (0, 2)` and `r > 0`, there exists `t ≥ 0` with `pseudoMassG α r t = c`. -/
theorem pseudoMassG_exists_of_mem_Ioo
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) {c : ℝ} (hc : c ∈ Ioo 0 2) :
    ∃ t ≥ 0, pseudoMassG α r t = c := by
  have hg0 : pseudoMassG α r 0 = 2 := pseudoMassG_zero hα r
  have h_cont : ContinuousOn (pseudoMassG α r) (Ici 0) := pseudoMassG_continuousOn α hr
  -- Find T large enough that g(T) < c
  obtain ⟨T, hT0, hTval⟩ : ∃ T : ℝ, 0 ≤ T ∧ pseudoMassG α r T < c := by
    have htend := pseudoMassG_tendsto_zero α hr
    rw [Metric.tendsto_atTop] at htend
    obtain ⟨N, hN⟩ := htend (c / 2) (by linarith [hc.1])
    refine ⟨max 0 N, le_max_left _ _, ?_⟩
    have hpos : 0 < pseudoMassG α r (max 0 N) :=
      pseudoMassG_pos α (le_max_left _ _) hr
    have hmem := hN (max 0 N) (le_max_right _ _)
    simp only [Real.dist_eq, sub_zero, abs_of_pos hpos] at hmem
    linarith
  -- Apply IVT on [0, T]: g continuous, g(0) = 2 > c > g(T)
  have h_mem : c ∈ Icc (pseudoMassG α r T) (pseudoMassG α r 0) :=
    ⟨le_of_lt hTval, by rw [hg0]; exact le_of_lt hc.2⟩
  obtain ⟨t, ht_mem, htval⟩ :=
    intermediate_value_Icc' hT0 (h_cont.mono Icc_subset_Ici_self) h_mem
  exact ⟨t, ht_mem.1, htval⟩

/-- For `c ∈ (0, 2)` and `r > 0`, the solution `t` is unique (strict antitone). -/
theorem pseudoMassG_unique
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) {c t₁ t₂ : ℝ}
    (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂)
    (h₁ : pseudoMassG α r t₁ = c) (h₂ : pseudoMassG α r t₂ = c) :
    t₁ = t₂ :=
  (pseudoMassG_strictAntiOn hα hr).injOn (Set.mem_Ici.mpr ht₁) (Set.mem_Ici.mpr ht₂)
    (h₁.trans h₂.symm)

/-! ## Derivative of the pseudo-mass profile -/

/-- `pseudoMassG α r` has derivative
`(-2·r·exp(-(t·r))·(1+(t·r)^α) - 2·exp(-(t·r))·(α·(t·r)^(α-1)·r)) / (1+(t·r)^α)^2`
at any point `t ≥ 0` with `r > 0`. Proved via quotient rule. -/
theorem pseudoMassG_hasDerivAt (α : ℕ) {r t : ℝ} (ht : 0 ≤ t) (hr : 0 < r) :
    HasDerivAt (pseudoMassG α r)
      ((-2 * r * Real.exp (-(t * r)) * (1 + (t * r) ^ α) -
        2 * Real.exp (-(t * r)) * (↑α * (t * r) ^ (α - 1) * r)) /
       (1 + (t * r) ^ α) ^ 2) t := by
  have hne : (1 + (t * r) ^ α : ℝ) ≠ 0 := by
    have h : 0 ≤ (t * r) ^ α := pow_nonneg (mul_nonneg ht hr.le) α
    linarith
  -- Derivative of fun t => t * r is r, then neg gives fun t => -(t * r) with deriv -r
  have h_mul : HasDerivAt (fun t : ℝ => t * r) r t := by
    have h := (hasDerivAt_id t).mul_const r
    simp only [Function.id_def, one_mul] at h
    exact h
  -- Numerator: 2 * exp(-(t * r)) with derivative 2 * (exp(-(t*r)) * (-r))
  have hf : HasDerivAt (fun t : ℝ => 2 * Real.exp (-(t * r)))
      (2 * (Real.exp (-(t * r)) * (-r))) t :=
    h_mul.neg.exp.const_mul 2
  -- Denominator: 1 + (t * r)^α with derivative ↑α * (t*r)^(α-1) * r
  have hh : HasDerivAt (fun t => 1 + (t * r) ^ α) (↑α * (t * r) ^ (α - 1) * r) t := by
    have h := (hasDerivAt_const t (1 : ℝ)).add (h_mul.pow α)
    simp only [zero_add] at h
    exact h
  unfold pseudoMassG
  have hdiv := hf.div hh hne
  convert hdiv using 1; ring

/-- **Step 117h (Issue #1645): `pseudoMassG α r` has a STRICT derivative
at any `t ≥ 0`** (`HasStrictDerivAt`, not just `HasDerivAt`).

Proof: `pseudoMassG α r t = 2 · exp(-(t·r)) / (1 + (t·r)^α)`, and each
component is built from `HasStrictDerivAt` primitives:
- `t ↦ -(t·r)` is affine.
- `t ↦ Real.exp(...)` is `HasStrictDerivAt` via `Real.exp.hasStrictDerivAt` chain.
- `t ↦ (t·r)^α` is polynomial.
- `1 + (t·r)^α ≠ 0` (denominator non-zero), so division preserves
  `HasStrictDerivAt`.

This is the prerequisite for the implicit function theorem application
to deduce `HasDerivAt` for `pseudoMass` (the inverse), unlocking the
substantive bridge of GJ §17.5 Lemma 17.5.2 (Issue #1645). -/
theorem pseudoMassG_hasStrictDerivAt (α : ℕ) {r t : ℝ} (ht : 0 ≤ t) (hr : 0 < r) :
    HasStrictDerivAt (pseudoMassG α r)
      ((-2 * r * Real.exp (-(t * r)) * (1 + (t * r) ^ α) -
        2 * Real.exp (-(t * r)) * (↑α * (t * r) ^ (α - 1) * r)) /
       (1 + (t * r) ^ α) ^ 2) t := by
  have hne : (1 + (t * r) ^ α : ℝ) ≠ 0 := by
    have h : 0 ≤ (t * r) ^ α := pow_nonneg (mul_nonneg ht hr.le) α
    linarith
  -- t ↦ t * r has strict derivative r
  have h_mul : HasStrictDerivAt (fun t : ℝ => t * r) r t := by
    have h := (hasStrictDerivAt_id t).mul_const r
    simpa using h
  -- t ↦ -(t * r) has strict derivative -r
  -- t ↦ 2 * exp(-(t * r)) has strict derivative 2 * (exp(-(t*r)) * (-r))
  have hf : HasStrictDerivAt (fun t : ℝ => 2 * Real.exp (-(t * r)))
      (2 * (Real.exp (-(t * r)) * (-r))) t :=
    h_mul.neg.exp.const_mul 2
  -- t ↦ 1 + (t * r)^α has strict derivative ↑α * (t*r)^(α-1) * r
  have hh : HasStrictDerivAt (fun t => 1 + (t * r) ^ α)
      (↑α * (t * r) ^ (α - 1) * r) t := by
    have h := (hasStrictDerivAt_const t (1 : ℝ)).add (h_mul.pow α)
    convert h using 1
    simp
  -- Division gives the quotient rule derivative
  unfold pseudoMassG
  have hdiv := hf.div hh hne
  convert hdiv using 1; ring

/-- The derivative of `pseudoMassG α r` at `t > 0` is strictly negative,
confirming the strict antitonicity on `(0, ∞)`. -/
theorem pseudoMassG_deriv_neg (α : ℕ) {r t : ℝ} (ht : 0 < t) (hr : 0 < r) :
    (-2 * r * Real.exp (-(t * r)) * (1 + (t * r) ^ α) -
      2 * Real.exp (-(t * r)) * (↑α * (t * r) ^ (α - 1) * r)) /
     (1 + (t * r) ^ α) ^ 2 < 0 := by
  have htr : 0 < t * r := mul_pos ht hr
  have hpow : 0 ≤ (t * r) ^ α := pow_nonneg htr.le α
  have hpow1 : 0 ≤ (t * r) ^ (α - 1) := pow_nonneg htr.le _
  have hα_nn : (0 : ℝ) ≤ (α : ℝ) := by exact_mod_cast Nat.zero_le α
  have hdenom : 0 < (1 + (t * r) ^ α) ^ 2 := by positivity
  rw [div_neg_iff]
  right
  refine ⟨?_, hdenom⟩
  have hexp := Real.exp_pos (-(t * r))
  have h1 : 0 < 2 * r * Real.exp (-(t * r)) * (1 + (t * r) ^ α) := by
    apply mul_pos (mul_pos (mul_pos two_pos hr) hexp)
    linarith
  have h2 : 0 ≤ 2 * Real.exp (-(t * r)) * (↑α * (t * r) ^ (α - 1) * r) :=
    mul_nonneg (mul_nonneg two_pos.le hexp.le)
      (mul_nonneg (mul_nonneg hα_nn hpow1) hr.le)
  linarith

/-! ## Definition and basic properties of the pseudo-mass -/

/-- `pseudoMass hα hr hc` is the unique `t ≥ 0` with `pseudoMassG α r t = c`,
defined via the classical choice principle for `c ∈ (0, 2)` and `r > 0`. -/
noncomputable def pseudoMass {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) {c : ℝ}
    (hc : c ∈ Ioo 0 2) : ℝ :=
  (pseudoMassG_exists_of_mem_Ioo hα hr hc).choose

/-- The pseudo-mass satisfies its defining equation. -/
theorem pseudoMass_spec {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) {c : ℝ}
    (hc : c ∈ Ioo 0 2) :
    pseudoMassG α r (pseudoMass hα hr hc) = c :=
  (pseudoMassG_exists_of_mem_Ioo hα hr hc).choose_spec.2

/-- The pseudo-mass is nonneg. -/
theorem pseudoMass_nonneg {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) {c : ℝ}
    (hc : c ∈ Ioo 0 2) :
    0 ≤ pseudoMass hα hr hc :=
  (pseudoMassG_exists_of_mem_Ioo hα hr hc).choose_spec.1

/-- **`pseudoMass(c) ≤ log(2/c)/r`**: explicit upper bound on the
pseudo-mass. From the inequality
`g(t, r, α) = 2·exp(-(t·r)) / (1 + (t·r)^α) ≤ 2·exp(-(t·r))`
(denominator ≥ 1), the defining equation `g(pm) = c` yields
`c ≤ 2·exp(-pm·r)`, i.e., `exp(-pm·r) ≥ c/2 > 0`, hence
`-pm·r ≥ log(c/2)`, hence `pm ≤ -log(c/2)/r = log(2/c)/r`.

This is the natural quantitative bound on `pseudoMass`: as `c → 2-`,
`pm(c) → 0+`; as `c → 0+`, `pm(c) → ∞`. -/
theorem pseudoMass_le_log_two_div {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {c : ℝ} (hc : c ∈ Ioo 0 2) :
    pseudoMass hα hr hc ≤ Real.log (2 / c) / r := by
  set pm := pseudoMass hα hr hc with hpm_def
  have hpm_nn : 0 ≤ pm := pseudoMass_nonneg hα hr hc
  have hg : pseudoMassG α r pm = c := pseudoMass_spec hα hr hc
  have hc_pos : 0 < c := hc.1
  have h_two_pos : (0 : ℝ) < 2 := by norm_num
  -- Step 1: c ≤ 2·exp(-pm·r)
  have h_pow_nn : 0 ≤ (pm * r) ^ α :=
    pow_nonneg (mul_nonneg hpm_nn hr.le) α
  have h_denom_ge_one : 1 ≤ 1 + (pm * r) ^ α := by linarith
  have h_denom_pos : 0 < 1 + (pm * r) ^ α := by linarith
  have h_step1 : c ≤ 2 * Real.exp (-(pm * r)) := by
    rw [← hg]
    unfold pseudoMassG
    rw [div_le_iff₀ h_denom_pos]
    have h_exp_pos : 0 < Real.exp (-(pm * r)) := Real.exp_pos _
    nlinarith
  -- Step 2: c/2 ≤ exp(-pm·r)
  have h_step2 : c / 2 ≤ Real.exp (-(pm * r)) := by linarith
  -- Step 3: log(c/2) ≤ -pm·r
  have h_c_div_2_pos : 0 < c / 2 := by linarith
  have h_log_le : Real.log (c / 2) ≤ -(pm * r) := by
    have := Real.log_le_log h_c_div_2_pos h_step2
    rwa [Real.log_exp] at this
  -- Step 4: pm·r ≤ -log(c/2) = log(2/c)
  have h_log_eq : Real.log (2 / c) = -Real.log (c / 2) := by
    rw [show (2 / c) = (c / 2)⁻¹ from by field_simp,
        Real.log_inv]
  have h_pm_r_le : pm * r ≤ Real.log (2 / c) := by
    rw [h_log_eq]; linarith
  -- Step 5: pm ≤ log(2/c)/r
  rw [le_div_iff₀ hr]
  linarith

/-- **`pseudoMass(c) · r ≤ log(2/c)`**: multiplied form of
`pseudoMass_le_log_two_div`, useful when `r` appears as a factor
(e.g., `pm·d(x,z)` decay rates). Direct from the divided form
multiplied through by `r > 0`. -/
theorem pseudoMass_mul_r_le_log_two_div {α : ℕ} (hα : 1 ≤ α) {r : ℝ}
    (hr : 0 < r) {c : ℝ} (hc : c ∈ Ioo 0 2) :
    pseudoMass hα hr hc * r ≤ Real.log (2 / c) := by
  have h := pseudoMass_le_log_two_div hα hr hc
  rw [le_div_iff₀ hr] at h
  exact h


/-- Characterisation of the pseudo-mass: `pseudoMass = t ↔ pseudoMassG α r t = c`
for `t ≥ 0`. -/
theorem pseudoMass_eq_iff {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) {c : ℝ}
    (hc : c ∈ Ioo 0 2) {t : ℝ} (ht : 0 ≤ t) :
    pseudoMass hα hr hc = t ↔ pseudoMassG α r t = c := by
  constructor
  · intro h; rw [← h]; exact pseudoMass_spec hα hr hc
  · intro h
    exact pseudoMassG_unique hα hr (pseudoMass_nonneg hα hr hc) ht
      (pseudoMass_spec hα hr hc) h

/-! ## Implicit differentiation of the defining equation -/

/-- If `h` satisfies the pseudo-mass defining equation `pseudoMassG α r (h β) = c β`
and is differentiable at `β`, then its derivative equals `c'(β) / g'(h(β))`,
where `g' = d/dt pseudoMassG α r`.
This is the key implicit differentiation step for the GJ §17.5 Lipschitz estimate. -/
theorem pseudoMass_deriv_formula
    (α : ℕ) {r : ℝ} (hr : 0 < r)
    {h c : ℝ → ℝ} {h' c' β : ℝ}
    (hh : HasDerivAt h h' β)
    (hc : HasDerivAt c c' β)
    (hβ : 0 ≤ h β)
    (hg_eq : ∀ β, pseudoMassG α r (h β) = c β)
    (hg' : 0 < h β) :
    h' = c' / ((-2 * r * Real.exp (-(h β * r)) * (1 + (h β * r) ^ α) -
        2 * Real.exp (-(h β * r)) * (↑α * (h β * r) ^ (α - 1) * r)) /
       (1 + (h β * r) ^ α) ^ 2) := by
  -- Let g' denote the value of the derivative of pseudoMassG at h β
  set g' := (-2 * r * Real.exp (-(h β * r)) * (1 + (h β * r) ^ α) -
    2 * Real.exp (-(h β * r)) * (↑α * (h β * r) ^ (α - 1) * r)) /
    (1 + (h β * r) ^ α) ^ 2 with hg'_def
  -- g' ≠ 0 (from pseudoMassG_deriv_neg, since h β > 0)
  have hg'_ne : g' ≠ 0 := ne_of_lt (pseudoMassG_deriv_neg α hg' hr)
  -- HasDerivAt (pseudoMassG α r) g' (h β)
  have hgd : HasDerivAt (pseudoMassG α r) g' (h β) :=
    pseudoMassG_hasDerivAt α hβ hr
  -- Chain rule: HasDerivAt (pseudoMassG α r ∘ h) (g' * h') β
  have hcomp := hgd.comp β hh
  -- But pseudoMassG α r ∘ h = c (by hg_eq)
  have hcomp' : HasDerivAt c (g' * h') β := by
    have : (pseudoMassG α r ∘ h) = c := funext hg_eq
    exact this ▸ hcomp
  -- By uniqueness of derivatives: g' * h' = c'
  have huniq : g' * h' = c' := hcomp'.unique hc
  -- Conclude h' = c' / g'
  field_simp [hg'_ne] at huniq ⊢
  linarith

/-- Corollary: if the pseudo-mass `m⁻ = pseudoMass hα hr hc(β)` is differentiable
at `β` with derivative `m'`, then `m'` satisfies the implicit differentiation formula.
(The differentiability of `pseudoMass` as a function of `β` follows from the
implicit function theorem, which requires additional infrastructure.) -/
theorem pseudoMass_deriv_formula_corollary
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {c : ℝ → ℝ} {c' β m' : ℝ}
    (hc_mem : c β ∈ Ioo 0 2)
    (hc_fam : ∀ β', c β' ∈ Ioo 0 2)
    (hc : HasDerivAt c c' β)
    (hm_pos : 0 < pseudoMass hα hr hc_mem)
    (hm_diff : HasDerivAt (fun β' => pseudoMass hα hr (hc_fam β')) m' β) :
    m' = c' / ((-2 * r * Real.exp (-(pseudoMass hα hr hc_mem * r)) *
        (1 + (pseudoMass hα hr hc_mem * r) ^ α) -
        2 * Real.exp (-(pseudoMass hα hr hc_mem * r)) *
        (↑α * (pseudoMass hα hr hc_mem * r) ^ (α - 1) * r)) /
       (1 + (pseudoMass hα hr hc_mem * r) ^ α) ^ 2) := by
  apply pseudoMass_deriv_formula α hr hm_diff hc (pseudoMass_nonneg hα hr hc_mem) _ hm_pos
  intro β'
  exact pseudoMass_spec hα hr (hc_fam β')

/-! ## Derivation lemma for the Lipschitz estimate (Step 117f partial) -/

/-- For `t ≥ 0`, `r > 0`, the absolute value of `pseudoMassG` derivative
satisfies `|g'(t,r,α)| ≥ r · g(t,r,α)`.
Algebraically: `|g'| - r·g = 2·exp(-(tr))·↑α·(tr)^{α-1}·r / (1+(tr)^α)^2 ≥ 0`.
This is a key analytic ingredient for the GJ §17.5 Lipschitz estimate. -/
theorem pseudoMassG_deriv_abs_ge (α : ℕ) {r t : ℝ} (ht : 0 ≤ t) (hr : 0 < r) :
    r * pseudoMassG α r t ≤
    |(-2 * r * Real.exp (-(t * r)) * (1 + (t * r) ^ α) -
      2 * Real.exp (-(t * r)) * (↑α * (t * r) ^ (α - 1) * r)) /
     (1 + (t * r) ^ α) ^ 2| := by
  have htr : 0 ≤ t * r := mul_nonneg ht hr.le
  have hpow : 0 ≤ (t * r) ^ α := pow_nonneg htr α
  have hpow1 : 0 ≤ (t * r) ^ (α - 1) := pow_nonneg htr _
  have hα_nn : (0 : ℝ) ≤ (α : ℝ) := by exact_mod_cast Nat.zero_le α
  have hD : 0 < (1 + (t * r) ^ α) ^ 2 := by positivity
  have hD_base : 0 < 1 + (t * r) ^ α := by linarith
  have he := Real.exp_pos (-(t * r))
  -- Key algebraic identity:
  -- |g'| = (2r*e*(1+u^α) + 2e*α*u^{α-1}*r) / (1+u^α)^2
  -- r*g  = 2r*e / (1+u^α)
  -- |g'| - r*g = 2e*α*u^{α-1}*r / (1+u^α)^2 ≥ 0
  -- Rewrite as: r*g ≤ |g'| iff r*g*(1+u^α)^2 ≤ |numerator|
  -- iff 2r*e*(1+u^α) ≤ 2r*e*(1+u^α) + 2e*α*u^{α-1}*r, i.e., 0 ≤ 2e*α*u^{α-1}*r
  -- N := numerator (negative), -N ≥ 0
  set N := -2 * r * Real.exp (-(t * r)) * (1 + (t * r) ^ α) -
      2 * Real.exp (-(t * r)) * (↑α * (t * r) ^ (α - 1) * r) with hN_def
  have hN_neg : N ≤ 0 := by
    have : 0 ≤ 2 * Real.exp (-(t * r)) * (↑α * (t * r) ^ (α - 1) * r) :=
      mul_nonneg (mul_nonneg two_pos.le he.le) (mul_nonneg (mul_nonneg hα_nn hpow1) hr.le)
    simp only [hN_def]
    nlinarith [mul_pos (mul_pos two_pos hr) he]
  -- |g'| = (-N) / D
  have h_abs_eq : |N / (1 + (t * r) ^ α) ^ 2| = (-N) / (1 + (t * r) ^ α) ^ 2 := by
    rw [abs_div, abs_of_nonpos hN_neg, abs_of_pos hD]
  rw [h_abs_eq]
  -- Goal: r * g(t) ≤ (-N) / D
  unfold pseudoMassG
  -- Rewrite to: r * (2*e/(1+u^α)) * D ≤ -N
  -- Cross-multiply by hD: goal becomes r*(2*e/(1+u^α)) * D ≤ -N
  -- = 2*r*e*(1+u^α) ≤ 2r*e*(1+u^α) + 2e*α*u^{α-1}*r (after simplification)
  have h_cross : r * (2 * Real.exp (-(t * r)) / (1 + (t * r) ^ α)) *
      (1 + (t * r) ^ α) ^ 2 ≤ -N := by
    have h_simp : r * (2 * Real.exp (-(t * r)) / (1 + (t * r) ^ α)) *
        (1 + (t * r) ^ α) ^ 2 = 2 * r * Real.exp (-(t * r)) * (1 + (t * r) ^ α) := by
      field_simp [hD_base.ne']
    rw [h_simp]
    -- Goal: 2*r*e*(1+u^α) ≤ -N
    -- -N = 2r*e*(1+u^α) + 2e*α*u^{α-1}*r (from hN_def)
    have hN_expand : -N = 2 * r * Real.exp (-(t * r)) * (1 + (t * r) ^ α) +
        2 * Real.exp (-(t * r)) * (↑α * (t * r) ^ (α - 1) * r) := by
      simp only [hN_def]; ring
    rw [hN_expand]
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg two_pos.le he.le)
                (mul_nonneg hα_nn hpow1)) hr.le]
  linarith [le_div_iff₀ hD |>.mpr h_cross]

/-! ## Lemma 17.5.2 (partial): positivity and monotonicity of pseudo-mass (Step 117g) -/

/-- The pseudo-mass is strictly positive for `c ∈ (0, 2)` and `r > 0`.
Proof: `g(0) = 2 > c`, and `g(m⁻) = c`, so strict antitonicity gives `m⁻ > 0`.
This is the first part of GJ Lemma 17.5.2. -/
theorem pseudoMass_pos {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) {c : ℝ}
    (hc : c ∈ Ioo 0 2) : 0 < pseudoMass hα hr hc := by
  have hspec := pseudoMass_spec hα hr hc
  have hnonneg := pseudoMass_nonneg hα hr hc
  rcases hnonneg.lt_or_eq with h | h
  · exact h
  · exfalso
    rw [← h, pseudoMassG_zero hα r] at hspec
    linarith [hc.2]

/-- **`pseudoMass(c) < (2-c)/(c·r)`**: strict version of
`pseudoMass_le_two_sub_div_mul_r`, using
`Real.log_lt_sub_one_of_pos` (strict at `c ≠ 2`). For `c ∈ Ioo 0 2`,
`c ≠ 2` is automatic. -/
theorem pseudoMass_lt_two_sub_div_mul_r {α : ℕ} (hα : 1 ≤ α) {r : ℝ}
    (hr : 0 < r) {c : ℝ} (hc : c ∈ Ioo 0 2) :
    pseudoMass hα hr hc < (2 - c) / (c * r) := by
  have hc_pos : 0 < c := hc.1
  have hc_lt : c < 2 := hc.2
  have hcr_pos : 0 < c * r := mul_pos hc_pos hr
  have h2c_pos : 0 < (2 : ℝ) / c := by positivity
  have h2c_ne_one : (2 : ℝ) / c ≠ 1 := by
    intro h_eq
    have : (2 : ℝ) = c := by field_simp at h_eq; linarith
    linarith
  have h_log_lt : Real.log (2 / c) < 2 / c - 1 :=
    Real.log_lt_sub_one_of_pos h2c_pos h2c_ne_one
  have h_eq : (2 : ℝ) / c - 1 = (2 - c) / c := by field_simp
  have h_step1 : pseudoMass hα hr hc ≤ Real.log (2 / c) / r :=
    pseudoMass_le_log_two_div hα hr hc
  have h_step2 : Real.log (2 / c) / r < (2 - c) / c / r := by
    apply div_lt_div_of_pos_right
    · rw [← h_eq]; exact h_log_lt
    · exact hr
  have h_div : (2 - c) / c / r = (2 - c) / (c * r) := by rw [div_div]
  linarith [h_step1, h_step2, h_div.symm.le, h_div.le]

/-- **`pseudoMass(c) ≤ (2-c)/(c·r)`**: sharper bound near `c = 2`,
where `log(2/c) ≤ 2/c - 1 = (2-c)/c` via `Real.log_le_sub_one_of_pos`.
Captures the boundary behavior `pseudoMass(c) → 0` linearly as
`c → 2-`. -/
theorem pseudoMass_le_two_sub_div_mul_r {α : ℕ} (hα : 1 ≤ α) {r : ℝ}
    (hr : 0 < r) {c : ℝ} (hc : c ∈ Ioo 0 2) :
    pseudoMass hα hr hc ≤ (2 - c) / (c * r) := by
  have hc_pos : 0 < c := hc.1
  have hcr_pos : 0 < c * r := mul_pos hc_pos hr
  have h2c_pos : 0 < (2 : ℝ) / c := by positivity
  have h_log_le : Real.log (2 / c) ≤ 2 / c - 1 :=
    Real.log_le_sub_one_of_pos h2c_pos
  have h_eq : (2 : ℝ) / c - 1 = (2 - c) / c := by field_simp
  have h_step1 : pseudoMass hα hr hc ≤ Real.log (2 / c) / r :=
    pseudoMass_le_log_two_div hα hr hc
  have h_step2 : Real.log (2 / c) / r ≤ (2 - c) / c / r := by
    apply div_le_div_of_nonneg_right
    · rw [← h_eq]; exact h_log_le
    · exact hr.le
  have h_div : (2 - c) / c / r = (2 - c) / (c * r) := by
    rw [div_div]
  linarith [h_step1, h_step2, h_div.symm.le, h_div.le]

/-- **`pseudoMass(c) < log(2/c)/r`** (strict version of
`pseudoMass_le_log_two_div`): since `pseudoMass(c) > 0` (pseudoMass_pos)
for `c ∈ Ioo 0 2` and `α ≥ 1`, the denominator `1 + (pm·r)^α > 1`
strictly, giving `c < 2·exp(-pm·r)` strictly. -/
theorem pseudoMass_lt_log_two_div {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {c : ℝ} (hc : c ∈ Ioo 0 2) :
    pseudoMass hα hr hc < Real.log (2 / c) / r := by
  set pm := pseudoMass hα hr hc with hpm_def
  have hpm_pos : 0 < pm := pseudoMass_pos hα hr hc
  have hg : pseudoMassG α r pm = c := pseudoMass_spec hα hr hc
  have hc_pos : 0 < c := hc.1
  have hpmr_pos : 0 < pm * r := mul_pos hpm_pos hr
  have hpow_pos : 0 < (pm * r) ^ α := by positivity
  have hdenom_gt_one : 1 < 1 + (pm * r) ^ α := by linarith
  have hdenom_pos : 0 < 1 + (pm * r) ^ α := by linarith
  have hexp_pos : 0 < Real.exp (-(pm * r)) := Real.exp_pos _
  have h_step1 : c < 2 * Real.exp (-(pm * r)) := by
    rw [← hg]
    unfold pseudoMassG
    rw [div_lt_iff₀ hdenom_pos]
    nlinarith
  have h_step2 : c / 2 < Real.exp (-(pm * r)) := by linarith
  have h_c_div_2_pos : 0 < c / 2 := by linarith
  have h_log_lt : Real.log (c / 2) < -(pm * r) := by
    have := Real.log_lt_log h_c_div_2_pos h_step2
    rwa [Real.log_exp] at this
  have h_log_eq : Real.log (2 / c) = -Real.log (c / 2) := by
    rw [show (2 / c) = (c / 2)⁻¹ from by field_simp,
        Real.log_inv]
  have h_pm_r_lt : pm * r < Real.log (2 / c) := by
    rw [h_log_eq]; linarith
  rw [lt_div_iff₀ hr]
  linarith

/-- **`pseudoMass(c) · r < log(2/c)`**: strict multiplied form of
`pseudoMass_lt_log_two_div`. -/
theorem pseudoMass_mul_r_lt_log_two_div {α : ℕ} (hα : 1 ≤ α) {r : ℝ}
    (hr : 0 < r) {c : ℝ} (hc : c ∈ Ioo 0 2) :
    pseudoMass hα hr hc * r < Real.log (2 / c) := by
  have h := pseudoMass_lt_log_two_div hα hr hc
  rw [lt_div_iff₀ hr] at h
  exact h

/-- **`pseudoMass(c) ∈ Ioo 0 (log(2/c)/r)`**: bundles
`pseudoMass_pos` and `pseudoMass_lt_log_two_div` into one Ioo
membership statement. -/
theorem pseudoMass_mem_Ioo_zero_log_two_div {α : ℕ} (hα : 1 ≤ α) {r : ℝ}
    (hr : 0 < r) {c : ℝ} (hc : c ∈ Ioo 0 2) :
    pseudoMass hα hr hc ∈ Set.Ioo (0 : ℝ) (Real.log (2 / c) / r) :=
  ⟨pseudoMass_pos hα hr hc,
   pseudoMass_lt_log_two_div hα hr hc⟩

/-- **`pseudoMass(c) ∈ Ioo 0 ((2-c)/(c·r))`**: bundle of `pos` and
strict sharper `(2-c)/(c·r)` upper bound. -/
theorem pseudoMass_mem_Ioo_zero_two_sub_div {α : ℕ} (hα : 1 ≤ α) {r : ℝ}
    (hr : 0 < r) {c : ℝ} (hc : c ∈ Ioo 0 2) :
    pseudoMass hα hr hc ∈ Set.Ioo (0 : ℝ) ((2 - c) / (c * r)) :=
  ⟨pseudoMass_pos hα hr hc,
   pseudoMass_lt_two_sub_div_mul_r hα hr hc⟩

/-- **`pseudoMass(c) ∈ Iio (log(2/c)/r)`**: trivial via `_lt_log_two_div`. -/
theorem pseudoMass_mem_Iio_log_two_div {α : ℕ} (hα : 1 ≤ α) {r : ℝ}
    (hr : 0 < r) {c : ℝ} (hc : c ∈ Ioo 0 2) :
    pseudoMass hα hr hc ∈ Set.Iio (Real.log (2 / c) / r) :=
  pseudoMass_lt_log_two_div hα hr hc

/-- **`pseudoMass(c) ∈ Iio ((2-c)/(c·r))`**: trivial via `_lt_two_sub_div_mul_r`. -/
theorem pseudoMass_mem_Iio_two_sub_div {α : ℕ} (hα : 1 ≤ α) {r : ℝ}
    (hr : 0 < r) {c : ℝ} (hc : c ∈ Ioo 0 2) :
    pseudoMass hα hr hc ∈ Set.Iio ((2 - c) / (c * r)) :=
  pseudoMass_lt_two_sub_div_mul_r hα hr hc

/-- The pseudo-mass is strictly decreasing in `c`: larger correlation value
means smaller pseudo-mass (slower decay). -/
theorem pseudoMass_strictAnti {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {c₁ c₂ : ℝ} (hc₁ : c₁ ∈ Ioo 0 2) (hc₂ : c₂ ∈ Ioo 0 2) (h : c₁ < c₂) :
    pseudoMass hα hr hc₂ < pseudoMass hα hr hc₁ := by
  have h₁ := pseudoMass_spec hα hr hc₁
  have h₂ := pseudoMass_spec hα hr hc₂
  have h₁_nn := pseudoMass_nonneg hα hr hc₁
  have h₂_nn := pseudoMass_nonneg hα hr hc₂
  -- g(m₂⁻) = c₂ > c₁ = g(m₁⁻), so by strict antitonicity, m₂⁻ < m₁⁻
  have hanti := pseudoMassG_strictAntiOn hα hr
  by_contra hle
  simp only [not_lt] at hle
  -- hle : m₁⁻ ≤ m₂⁻
  rcases hle.lt_or_eq with hlt | heq
  · -- g(m₁⁻) > g(m₂⁻) from strict antitonicity, contradicting c₁ < c₂
    have hg_lt := hanti (Set.mem_Ici.mpr h₁_nn) (Set.mem_Ici.mpr h₂_nn) hlt
    -- hg_lt : pseudoMassG α r m₂⁻ < pseudoMassG α r m₁⁻
    -- h₁ : pseudoMassG α r m₁⁻ = c₁, h₂ : pseudoMassG α r m₂⁻ = c₂
    linarith [h₁.symm.le, h₂.le, hg_lt]
  · -- m₁⁻ = m₂⁻, so c₁ = g(m₁⁻) = g(m₂⁻) = c₂, contradicting c₁ < c₂
    rw [heq, h₂] at h₁
    linarith

/-- **`pseudoMass(c) ≠ 0`** for `c ∈ Ioo 0 2`: direct from
`pseudoMass_pos`. -/
theorem pseudoMass_ne_zero {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) {c : ℝ}
    (hc : c ∈ Ioo 0 2) :
    pseudoMass hα hr hc ≠ 0 :=
  (pseudoMass_pos hα hr hc).ne'

/-- **`pseudoMass(c) ∈ Set.Ioi 0`** for `c ∈ Ioo 0 2`: direct from
`pseudoMass_pos`. -/
theorem pseudoMass_mem_Ioi_zero {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) {c : ℝ}
    (hc : c ∈ Ioo 0 2) :
    pseudoMass hα hr hc ∈ Set.Ioi (0 : ℝ) :=
  pseudoMass_pos hα hr hc

/-- **`pseudoMass(c) ∈ Set.Ici 0`** for `c ∈ Ioo 0 2`: direct from
`pseudoMass_nonneg`. -/
theorem pseudoMass_mem_Ici_zero {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) {c : ℝ}
    (hc : c ∈ Ioo 0 2) :
    pseudoMass hα hr hc ∈ Set.Ici (0 : ℝ) :=
  pseudoMass_nonneg hα hr hc

/-- **`pseudoMass(c) ∉ Set.Iio 0`** for `c ∈ Ioo 0 2`: direct from `pos`. -/
theorem pseudoMass_not_mem_Iio_zero {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {c : ℝ} (hc : c ∈ Ioo 0 2) :
    pseudoMass hα hr hc ∉ Set.Iio (0 : ℝ) :=
  not_lt.mpr (pseudoMass_nonneg hα hr hc)

/-- **Implicit definition: `pseudoMass(c) ≤ t ↔ pseudoMassG α r t ≤ c`** for
`t ≥ 0` and `c ∈ Ioo 0 2`: characterizes pseudoMass(c) as the unique
threshold by the anti-monotone defining equation `g(pseudoMass(c)) = c`. -/
theorem pseudoMass_le_iff_pseudoMassG_le {α : ℕ} (hα : 1 ≤ α) {r : ℝ}
    (hr : 0 < r) {c : ℝ} (hc : c ∈ Ioo 0 2) {t : ℝ} (ht : 0 ≤ t) :
    pseudoMass hα hr hc ≤ t ↔ pseudoMassG α r t ≤ c := by
  have hspec : pseudoMassG α r (pseudoMass hα hr hc) = c := pseudoMass_spec hα hr hc
  have hpm_nn : 0 ≤ pseudoMass hα hr hc := pseudoMass_nonneg hα hr hc
  have hG_iff : pseudoMassG α r t ≤ pseudoMassG α r (pseudoMass hα hr hc) ↔
                  pseudoMass hα hr hc ≤ t :=
    pseudoMassG_le_iff hα hr hpm_nn ht
  rw [hspec] at hG_iff
  exact hG_iff.symm

/-- **Implicit definition strict version**: `pseudoMass(c) < t ↔ pseudoMassG α r t < c`. -/
theorem pseudoMass_lt_iff_pseudoMassG_lt {α : ℕ} (hα : 1 ≤ α) {r : ℝ}
    (hr : 0 < r) {c : ℝ} (hc : c ∈ Ioo 0 2) {t : ℝ} (ht : 0 ≤ t) :
    pseudoMass hα hr hc < t ↔ pseudoMassG α r t < c := by
  have hspec : pseudoMassG α r (pseudoMass hα hr hc) = c := pseudoMass_spec hα hr hc
  have hpm_nn : 0 ≤ pseudoMass hα hr hc := pseudoMass_nonneg hα hr hc
  have hG_iff : pseudoMassG α r t < pseudoMassG α r (pseudoMass hα hr hc) ↔
                  pseudoMass hα hr hc < t :=
    pseudoMassG_lt_iff hα hr hpm_nn ht
  rw [hspec] at hG_iff
  exact hG_iff.symm

/-- **Implicit definition: `t ≤ pseudoMass(c) ↔ c ≤ pseudoMassG α r t`** (reverse). -/
theorem pseudoMass_ge_iff_pseudoMassG_ge {α : ℕ} (hα : 1 ≤ α) {r : ℝ}
    (hr : 0 < r) {c : ℝ} (hc : c ∈ Ioo 0 2) {t : ℝ} (ht : 0 ≤ t) :
    t ≤ pseudoMass hα hr hc ↔ c ≤ pseudoMassG α r t := by
  have hspec : pseudoMassG α r (pseudoMass hα hr hc) = c := pseudoMass_spec hα hr hc
  have hpm_nn : 0 ≤ pseudoMass hα hr hc := pseudoMass_nonneg hα hr hc
  have hG_iff : pseudoMassG α r (pseudoMass hα hr hc) ≤ pseudoMassG α r t ↔
                  t ≤ pseudoMass hα hr hc :=
    pseudoMassG_le_iff hα hr ht hpm_nn
  rw [hspec] at hG_iff
  exact hG_iff.symm

/-- **Implicit definition strict reverse**: `t < pseudoMass(c) ↔ c < pseudoMassG α r t`. -/
theorem pseudoMass_gt_iff_pseudoMassG_gt {α : ℕ} (hα : 1 ≤ α) {r : ℝ}
    (hr : 0 < r) {c : ℝ} (hc : c ∈ Ioo 0 2) {t : ℝ} (ht : 0 ≤ t) :
    t < pseudoMass hα hr hc ↔ c < pseudoMassG α r t := by
  have hspec : pseudoMassG α r (pseudoMass hα hr hc) = c := pseudoMass_spec hα hr hc
  have hpm_nn : 0 ≤ pseudoMass hα hr hc := pseudoMass_nonneg hα hr hc
  have hG_iff : pseudoMassG α r (pseudoMass hα hr hc) < pseudoMassG α r t ↔
                  t < pseudoMass hα hr hc :=
    pseudoMassG_lt_iff hα hr ht hpm_nn
  rw [hspec] at hG_iff
  exact hG_iff.symm

/-- **`pseudoMass` is antitone (non-strict)**: corollary of
`pseudoMass_strictAnti` weakened to `≤`. Useful when the strict
inequality is unnecessarily strong (e.g., bound chains). -/
theorem pseudoMass_antitone {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {c₁ c₂ : ℝ} (hc₁ : c₁ ∈ Ioo 0 2) (hc₂ : c₂ ∈ Ioo 0 2) (h : c₁ ≤ c₂) :
    pseudoMass hα hr hc₂ ≤ pseudoMass hα hr hc₁ := by
  rcases h.lt_or_eq with hlt | heq
  · exact (pseudoMass_strictAnti hα hr hc₁ hc₂ hlt).le
  · subst heq
    exact le_refl _

/-- **`pseudoMass(c₂) < pseudoMass(c₁) ↔ c₁ < c₂`**: iff form of
`pseudoMass_strictAnti`. -/
theorem pseudoMass_lt_iff {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {c₁ c₂ : ℝ} (hc₁ : c₁ ∈ Ioo 0 2) (hc₂ : c₂ ∈ Ioo 0 2) :
    pseudoMass hα hr hc₂ < pseudoMass hα hr hc₁ ↔ c₁ < c₂ := by
  refine ⟨?_, fun h => pseudoMass_strictAnti hα hr hc₁ hc₂ h⟩
  intro hlt
  by_contra h_neg
  have h_neg' : c₂ ≤ c₁ := not_lt.mp h_neg
  have := pseudoMass_antitone hα hr hc₂ hc₁ h_neg'
  linarith

/-- **`pseudoMass(c₂) ≤ pseudoMass(c₁) ↔ c₁ ≤ c₂`**: iff form of
`pseudoMass_antitone`. -/
theorem pseudoMass_le_iff {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {c₁ c₂ : ℝ} (hc₁ : c₁ ∈ Ioo 0 2) (hc₂ : c₂ ∈ Ioo 0 2) :
    pseudoMass hα hr hc₂ ≤ pseudoMass hα hr hc₁ ↔ c₁ ≤ c₂ := by
  refine ⟨?_, fun h => pseudoMass_antitone hα hr hc₁ hc₂ h⟩
  intro hle
  by_contra h_neg
  have h_neg' : c₂ < c₁ := not_le.mp h_neg
  have := pseudoMass_strictAnti hα hr hc₂ hc₁ h_neg'
  linarith

/-- **`pseudoMass(c₂) = pseudoMass(c₁) ↔ c₁ = c₂`**: equality iff
via antisymmetry. -/
theorem pseudoMass_eq_iff_eq {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {c₁ c₂ : ℝ} (hc₁ : c₁ ∈ Ioo 0 2) (hc₂ : c₂ ∈ Ioo 0 2) :
    pseudoMass hα hr hc₂ = pseudoMass hα hr hc₁ ↔ c₁ = c₂ := by
  refine ⟨?_, ?_⟩
  · intro heq
    have h1 := (pseudoMass_le_iff hα hr hc₁ hc₂).mp heq.le
    have h2 := (pseudoMass_le_iff hα hr hc₂ hc₁).mp heq.ge
    linarith
  · intro heq_c
    subst heq_c
    rfl

/-! ## Discrete Hardy-Littlewood-Sobolev inequality (axiom) -/

/-- **Discrete HLS constant** (Step 129): For `2α > d`, a positive constant exists.

We exhibit `C = ∑_z (1 + d(0,z))^{-2α}`, which is finite by `summable_pow_neg_latticeDistance`
(Step 128, since `2α > d`) and positive (the `z = 0` term equals 1).

**References**: GJ §17.5 (pp.310–312); de-axiomatized via `IsingModel.PolyDecay`. -/
theorem discrete_hls_constant (α d : ℕ) (hαd : 2 * α > d) :
    ∃ C : ℝ, C > 0 := by
  have hγ : (d : ℝ) < 2 * (α : ℝ) := by exact_mod_cast hαd
  exact ⟨∑' z : Fin d → ℤ, (1 + latticeDistance d 0 z : ℝ) ^ (-(2 * (α : ℝ))),
    (summable_pow_neg_latticeDistance d hγ).tsum_pos
      (fun z => by positivity)
      (0 : Fin d → ℤ)
      (by simp [latticeDistance])⟩

/-! ## Lemma 17.5.2: Bounds on lattice mass

The full GJ Lemma 17.5.2 statement is

  `m⁻(β) ≤ m(β) ≤ const · m⁻(β)`

where `m⁻` is the pseudo-mass (the abstract `pseudoMass` defined above
in terms of parameters `α, r, c`) and `m(β)` is the lattice mass
`latticeMass d Λ p : ENNReal` (defined in
`Concrete/LatticeGraphCorrelation/Inequalities.lean` as the supremum
of validating exponential decay rates).

**Status: Partial**. Bridging the abstract `pseudoMass` to the concrete
`latticeMass` requires:

1. A concrete map `(d, Λ, p) → (α, r, c)` (the physically-motivated
   parameter selection used in GJ p.311);
2. Exponential decay bounds on ℤ^d (Step 117h+, not yet formalized);
3. Connecting `pseudoMass`-positivity to a validating decay rate for
   `latticeMass`.

The helper theorems below (`pseudoMass_pos`,
`discrete_hls_constant`) are ingredients toward the full lemma, but
the bridge is not yet in place. Earlier names
`latticeMass_ge_pseudoMass` / `latticeMass_le_constant_mul_pseudoMass`
were misleading aliases of `pseudoMass_pos` and
`discrete_hls_constant` respectively (their conclusions did not
mention `latticeMass`); they have been renamed to avoid the
appearance of completeness.

**References**: Glimm–Jaffe §17.5, Lemma 17.5.2, pp. 311–312
(proof uses HLS + Lipschitz). -/

/-- **Lemma 17.5.2 lower-bound helper** (positivity of `pseudoMass`).
Alias of `pseudoMass_pos`; kept for §17.5 cross-referencing.
The actual lower-bound statement `pseudoMass ≤ latticeMass` requires
linking `pseudoMass` to a validating exponential decay rate for
`latticeMass` (Step 117h+, not yet formalized).

**References**: Glimm–Jaffe §17.5, p. 311. -/
theorem lemma_17_5_2_pseudoMass_pos (α : ℕ) (hα : 1 ≤ α) {r : ℝ}
    (hr : 0 < r) {c : ℝ} (hc : c ∈ Ioo 0 2) :
    0 < pseudoMass hα hr hc :=
  pseudoMass_pos hα hr hc

/-- **Lemma 17.5.2 upper-bound helper** (existence of the discrete
HLS constant). Alias of `discrete_hls_constant`; kept for §17.5
cross-referencing. The actual upper-bound statement
`latticeMass ≤ const · pseudoMass` requires the discrete HLS
inequality + Lipschitz estimate combined with exponential decay
on ℤ^d (Step 117h+, not yet formalized).

**References**: Glimm–Jaffe §17.5, Lemma 17.5.2, p. 311. -/
theorem lemma_17_5_2_constant_exists (α d : ℕ) (hαd : 2 * α > d) :
    ∃ C : ℝ, C > 0 :=
  discrete_hls_constant α d hαd

/-! ## Theorem 17.5.1: Lipschitz bound (Step 131) -/

/-- **Abstract Lipschitz bound** (Step 131a): pseudo-mass derivative satisfies
`|h'| ≤ |c'| / (r * c β)`.

Proof combines:
- `pseudoMass_deriv_formula` (Step 117e): `h' = c' / g'`
- `pseudoMassG_deriv_abs_ge` (Step 117f): `r * c β = r * pseudoMassG α r (h β) ≤ |g'|`

Since `g' < 0` (from `pseudoMassG_deriv_neg`) we have `|g'| > 0`, and thus
`|h'| = |c'| / |g'| ≤ |c'| / (r * c β)`.

**References**: Glimm–Jaffe §17.5, Theorem 17.5.1 proof, p.312. -/
theorem pseudoMass_deriv_abs_le
    (α : ℕ) {r : ℝ} (hr : 0 < r)
    {h c : ℝ → ℝ} {h' c' β : ℝ}
    (hh : HasDerivAt h h' β)
    (hc : HasDerivAt c c' β)
    (hβ : 0 ≤ h β)
    (hg_eq : ∀ β', pseudoMassG α r (h β') = c β')
    (hm_pos : 0 < h β)
    (hc_pos : 0 < c β) :
    |h'| ≤ |c'| / (r * c β) := by
  set g' := (-2 * r * Real.exp (-(h β * r)) * (1 + (h β * r) ^ α) -
      2 * Real.exp (-(h β * r)) * (↑α * (h β * r) ^ (α - 1) * r)) /
     (1 + (h β * r) ^ α) ^ 2 with hg'_def
  have hform : h' = c' / g' := pseudoMass_deriv_formula α hr hh hc hβ hg_eq hm_pos
  have hg'_neg : g' < 0 := pseudoMassG_deriv_neg α hm_pos hr
  have hge : r * c β ≤ |g'| := by
    have h1 := pseudoMassG_deriv_abs_ge α hβ hr
    rwa [hg_eq β] at h1
  have hrc_pos : 0 < r * c β := mul_pos hr hc_pos
  have hg'_pos : 0 < |g'| := lt_of_lt_of_le hrc_pos hge
  rw [hform, abs_div]
  exact div_le_div_of_nonneg_left (abs_nonneg c') hrc_pos hge

/-- **Lipschitz power bound** (Step 131b): `(h β)^(2α) * |h'| ≤ K / r`.

If the correlation derivative satisfies `|c'| ≤ K * c β / (h β)^(2α)` (motivated by
the HLS convolution bound `tsum_pow_neg_conv_le_const` (Step 130) via Lebowitz's inequality
applied to lattice correlations), then the Lipschitz power bound holds.

This is the abstract version of GJ §17.5: `m⁻^{2α} · dm⁻/dσ ≤ const`, which via the
chain rule gives Lipschitz continuity of `m⁻^{2α+1}` in σ (Theorem 17.5.1, p.312).

**References**: Glimm–Jaffe §17.5, Theorem 17.5.1 proof, p.312. -/
theorem pseudoMass_power_deriv_le
    (α : ℕ) {r K : ℝ} (hr : 0 < r)
    {h c : ℝ → ℝ} {h' c' β : ℝ}
    (hh : HasDerivAt h h' β)
    (hc : HasDerivAt c c' β)
    (hβ : 0 ≤ h β)
    (hg_eq : ∀ β', pseudoMassG α r (h β') = c β')
    (hm_pos : 0 < h β)
    (hc_pos : 0 < c β)
    (hc_der : |c'| ≤ K * c β / (h β) ^ (2 * α)) :
    (h β) ^ (2 * α) * |h'| ≤ K / r := by
  have h1 := pseudoMass_deriv_abs_le α hr hh hc hβ hg_eq hm_pos hc_pos
  have hm_pow_pos : 0 < (h β) ^ (2 * α) := pow_pos hm_pos _
  have hrc_pos : 0 < r * c β := mul_pos hr hc_pos
  have key : (h β) ^ (2 * α) * |c'| ≤ K * c β := by
    calc (h β) ^ (2 * α) * |c'|
        ≤ (h β) ^ (2 * α) * (K * c β / (h β) ^ (2 * α)) :=
            mul_le_mul_of_nonneg_left hc_der hm_pow_pos.le
      _ = K * c β := by field_simp [hm_pow_pos.ne']
  calc (h β) ^ (2 * α) * |h'|
      ≤ (h β) ^ (2 * α) * (|c'| / (r * c β)) :=
          mul_le_mul_of_nonneg_left h1 hm_pow_pos.le
    _ = (h β) ^ (2 * α) * |c'| / (r * c β) := by ring
    _ ≤ K * c β / (r * c β) := (div_le_div_iff_of_pos_right hrc_pos).mpr key
    _ = K / r := by field_simp [hc_pos.ne', hr.ne']

/-- **Lipschitz derivative of (m⁻)^{2α+1}** (Step 133):
The derivative of `β ↦ (h β)^(2α+1)` exists with absolute value `≤ (2α+1) · K/r`.

This is the abstract derivative/Lipschitz core used in the proof of GJ §17.5 Theorem 17.5.1
(p.312): `(m⁻)^{2α+1}` is Lipschitz in σ with constant `(2α+1)·K/r`. Via the MVT:
`|(m⁻(σ₂))^{2α+1} − (m⁻(σ₁))^{2α+1}| ≤ (2α+1)·K/r �� |σ₂ − σ₁|`.

Proof: chain rule gives `d/dβ [(h β)^(2α+1)] = (2α+1)·(h β)^(2α)·h'`;
then `(h β)^(2α)·|h'| ≤ K/r` by `pseudoMass_power_deriv_le` (Step 131b).

**References**: Glimm–Jaffe §17.5, used in the proof of Theorem 17.5.1, p.312. -/
theorem pseudoMass_pow_succ_deriv_bound
    (α : ℕ) {r K : ℝ} (hr : 0 < r)
    {h c : ℝ → ℝ} {h' c' β : ℝ}
    (hh : HasDerivAt h h' β)
    (hc : HasDerivAt c c' β)
    (hβ : 0 ≤ h β)
    (hg_eq : ∀ β', pseudoMassG α r (h β') = c β')
    (hm_pos : 0 < h β)
    (hc_pos : 0 < c β)
    (hc_der : |c'| ≤ K * c β / (h β) ^ (2 * α)) :
    ∃ d : ℝ,
      HasDerivAt (fun β' => (h β') ^ (2 * α + 1)) d β ∧
      |d| ≤ ↑(2 * α + 1) * K / r := by
  have hbound := pseudoMass_power_deriv_le α hr hh hc hβ hg_eq hm_pos hc_pos hc_der
  have hpow_pos : (0 : ℝ) < ↑(2 * α + 1) := by exact_mod_cast Nat.succ_pos (2 * α)
  have hm_pow_pos : 0 < (h β) ^ (2 * α) := pow_pos hm_pos _
  have hderiv : HasDerivAt (fun β' => h β' ^ (2 * α + 1))
      (↑(2 * α + 1) * h β ^ (2 * α + 1 - 1) * h') β := hh.fun_pow (2 * α + 1)
  have hexp_eq : 2 * α + 1 - 1 = 2 * α := by omega
  rw [hexp_eq] at hderiv
  refine ⟨↑(2 * α + 1) * (h β) ^ (2 * α) * h', hderiv, ?_⟩
  rw [abs_mul, abs_mul, abs_of_pos hpow_pos, abs_of_pos hm_pow_pos]
  calc ↑(2 * α + 1) * (h β) ^ (2 * α) * |h'|
      = ↑(2 * α + 1) * ((h β) ^ (2 * α) * |h'|) := by ring
    _ ≤ ↑(2 * α + 1) * (K / r) := mul_le_mul_of_nonneg_left hbound hpow_pos.le
    _ = ↑(2 * α + 1) * K / r := by ring

/-- **GJ §17.5 Theorem 17.5.1 (abstract Lipschitz)** (Step 134):
`|(h β₂)^(2α+1) − (h β₁)^(2α+1)| ≤ ↑(2α+1)·K/r · (β₂ − β₁)` for β₁ ≤ β₂.

This is the abstract Lipschitz continuity of GJ §17.5 Theorem 17.5.1 (p.312):
`m⁻(σ)^{2α+1}` is Lipschitz in σ with constant `(2α+1)·K/r`, uniform in Λ.

Proof: apply MVT (`norm_image_sub_le_of_norm_deriv_le_segment'`) using:
- `HasDerivAt.fun_pow` for the chain rule derivative
- `pseudoMass_power_deriv_le` (Step 131b) for the derivative bound at each point

**References**: Glimm–Jaffe §17.5, Theorem 17.5.1, pp.311–312. -/
theorem pseudoMass_pow_succ_lipschitz
    (α : ℕ) {r K : ℝ} (hr : 0 < r) {β₁ β₂ : ℝ} (hβ : β₁ ≤ β₂)
    {h c : ℝ → ℝ}
    (hh_diff : ∀ β' ∈ Set.Icc β₁ β₂, HasDerivAt h (deriv h β') β')
    (hc_diff : ∀ β' ∈ Set.Icc β₁ β₂, HasDerivAt c (deriv c β') β')
    (hβ_nn : ∀ β' ∈ Set.Icc β₁ β₂, 0 ≤ h β')
    (hg_eq : ∀ β', pseudoMassG α r (h β') = c β')
    (hm_pos : ∀ β' ∈ Set.Icc β₁ β₂, 0 < h β')
    (hc_pos : ∀ β' ∈ Set.Icc β₁ β₂, 0 < c β')
    (hc_der : ∀ β' ∈ Set.Icc β₁ β₂,
        |deriv c β'| ≤ K * c β' / (h β') ^ (2 * α)) :
    |(h β₂) ^ (2 * α + 1) - (h β₁) ^ (2 * α + 1)| ≤
      ↑(2 * α + 1) * K / r * (β₂ - β₁) := by
  rw [← Real.norm_eq_abs]
  have := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun β' => (h β') ^ (2 * α + 1))
    (f' := fun β' => ↑(2 * α + 1) * (h β') ^ (2 * α) * deriv h β')
    (a := β₁) (b := β₂) (C := ↑(2 * α + 1) * K / r)
    (hf := fun β' hβ' => by
      have hderiv := (hh_diff β' hβ').fun_pow (2 * α + 1)
      have hexp : 2 * α + 1 - 1 = 2 * α := by omega
      rw [hexp] at hderiv
      exact hderiv.hasDerivWithinAt)
    (bound := fun β' hβ' => by
      have hβ'_mem : β' ∈ Set.Icc β₁ β₂ := Set.Ico_subset_Icc_self hβ'
      have h1 := pseudoMass_power_deriv_le α hr
        (hh_diff β' hβ'_mem) (hc_diff β' hβ'_mem)
        (hβ_nn β' hβ'_mem) hg_eq
        (hm_pos β' hβ'_mem) (hc_pos β' hβ'_mem) (hc_der β' hβ'_mem)
      have hpow_pos : (0 : ℝ) < ↑(2 * α + 1) := by exact_mod_cast Nat.succ_pos (2 * α)
      have hm_pow_pos : 0 < (h β') ^ (2 * α) := pow_pos (hm_pos β' hβ'_mem) _
      simp only [Real.norm_eq_abs, abs_mul, abs_of_pos hpow_pos, abs_of_pos hm_pow_pos]
      calc ↑(2 * α + 1) * (h β') ^ (2 * α) * |deriv h β'|
          = ↑(2 * α + 1) * ((h β') ^ (2 * α) * |deriv h β'|) := by ring
        _ ≤ ↑(2 * α + 1) * (K / r) := mul_le_mul_of_nonneg_left h1 hpow_pos.le
        _ = ↑(2 * α + 1) * K / r := by ring)
  have hmem : β₂ ∈ Set.Icc β₁ β₂ := Set.right_mem_Icc.mpr hβ
  simpa using this β₂ hmem

/-! ## Theorem 17.5.1: Continuity at the critical point -/

/-! ## Continuity of pseudoMass in c (Step 119) -/

/-- The pseudo-mass as a map between subtypes:
`pseudoMassFn c = pseudoMass(c)` for `c ∈ Ioo 0 2`, with value in `Ioi 0`. -/
private noncomputable def pseudoMassFn {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) :
    ↑(Set.Ioo (0 : ℝ) 2) → ↑(Set.Ioi (0 : ℝ)) :=
  fun x => ⟨pseudoMass hα hr x.2, pseudoMass_pos hα hr x.2⟩

/-- `pseudoMassFn` is strictly anti (larger c → smaller pseudoMass). -/
private theorem pseudoMassFn_strictAnti {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) :
    StrictAnti (pseudoMassFn hα hr) := by
  intro ⟨c₁, hc₁⟩ ⟨c₂, hc₂⟩ h
  simp only [Subtype.mk_lt_mk, pseudoMassFn]
  exact pseudoMass_strictAnti hα hr hc₁ hc₂ (Subtype.mk_lt_mk.mp h)

/-- For `t > 0`, `pseudoMassG α r t ∈ Ioo 0 2`. -/
private lemma pseudoMassG_pos_mem_Ioo {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) {t : ℝ}
    (ht : 0 < t) : pseudoMassG α r t ∈ Set.Ioo 0 2 := by
  refine ⟨pseudoMassG_pos α ht.le hr, ?_⟩
  have hstrict := pseudoMassG_strictAntiOn hα hr
    (Set.mem_Ici.mpr (le_refl 0)) (Set.mem_Ici.mpr ht.le) ht
  rw [pseudoMassG_zero hα r] at hstrict
  linarith [pseudoMassG_le_two α ht.le hr]

/-- `pseudoMassFn` is surjective: every `t > 0` is the pseudo-mass of some `c ∈ Ioo 0 2`. -/
private theorem pseudoMassFn_surjective {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) :
    Function.Surjective (pseudoMassFn hα hr) := by
  intro ⟨t, ht⟩
  have ht_pos : 0 < t := Set.mem_Ioi.mp ht
  have hmem : pseudoMassG α r t ∈ Set.Ioo 0 2 := pseudoMassG_pos_mem_Ioo hα hr ht_pos
  exact ⟨⟨pseudoMassG α r t, hmem⟩, by
    simp only [pseudoMassFn, Subtype.mk.injEq]
    exact (pseudoMass_eq_iff hα hr hmem ht_pos.le).mpr rfl⟩

/-- `pseudoMassFn` is continuous: antitone and surjective onto a densely ordered codomain. -/
theorem pseudoMassFn_continuous {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) :
    Continuous (pseudoMassFn hα hr) := by
  have h_anti : Antitone (pseudoMassFn hα hr) := (pseudoMassFn_strictAnti hα hr).antitone
  -- View via dual order: OrderDual.toDual ∘ pseudoMassFn is Monotone
  have h_mono : Monotone (fun x => OrderDual.toDual (pseudoMassFn hα hr x)) :=
    fun _ _ hab => h_anti hab
  have h_surj : Function.Surjective (fun x => OrderDual.toDual (pseudoMassFn hα hr x)) :=
    fun b => let ⟨a, ha⟩ := pseudoMassFn_surjective hα hr (OrderDual.ofDual b)
            ⟨a, by simp [ha]⟩
  have h_cont_dual : Continuous (fun x => OrderDual.toDual (pseudoMassFn hα hr x)) :=
    h_mono.continuous_of_surjective h_surj
  exact h_cont_dual

/-- The pseudo-mass function is continuous on `Ioo 0 2`.
Proof: pseudoMassFn is continuous and the restriction/projection compose continuously. -/
theorem pseudoMass_continuousOn {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) :
    ContinuousOn (fun c => if hc : c ∈ Set.Ioo 0 2 then pseudoMass hα hr hc else 0)
      (Set.Ioo 0 2) := by
  rw [continuousOn_iff_continuous_restrict]
  have h_eq : Set.restrict (Set.Ioo 0 2)
      (fun c => if hc : c ∈ Set.Ioo 0 2 then pseudoMass hα hr hc else 0) =
      fun c => (pseudoMassFn hα hr c).1 := by
    ext ⟨c, hc⟩
    simp [Set.restrict, pseudoMassFn, hc]
  rw [h_eq]
  exact continuous_subtype_val.comp (pseudoMassFn_continuous hα hr)

/-- **Corollary (Step 119)**: The pseudo-mass is continuous at any `c₀ ∈ Ioo 0 2`.

This follows directly from `pseudoMass_continuousOn`.

Note: This is **not** the full GJ Theorem 17.5.1 (β-continuity of lattice mass at β_c).
That theorem requires connecting `pseudoMass` to concrete lattice correlations via
Lemma 17.5.2 bounds plus a Lipschitz derivation (Steps 117e-f + HLS axiom, deferred).

**References**: Glimm–Jaffe 2nd ed., §17.5 (pp.310–312).
-/
theorem pseudoMass_continuousAt {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) {c₀ : ℝ}
    (hc₀ : c₀ ∈ Set.Ioo 0 2) :
    ContinuousAt (fun c => if hc : c ∈ Set.Ioo 0 2 then pseudoMass hα hr hc else 0) c₀ :=
  (pseudoMass_continuousOn hα hr).continuousAt (Ioo_mem_nhds hc₀.1 hc₀.2)

/-- **Step 117i (Issue #1645): `pseudoMass` `HasStrictDerivAt` via inverse function theorem**.

The totalized pseudo-mass `fun c => if c ∈ Ioo 0 2 then pseudoMass hα hr hc else 0`
is strictly differentiable at every `c₀ ∈ Ioo 0 2`, with derivative the
reciprocal of `pseudoMassG α r`'s derivative at `pseudoMass(c₀)`.

Proof via `HasStrictDerivAt.of_local_left_inverse` applied to:
- `f = pseudoMassG α r`, `g = pseudoMassExt`, `a = c₀`.
- `g(c₀) = pseudoMass(c₀) > 0` (by `pseudoMass_pos`).
- Strict derivative of `f` at `g(c₀)` from `pseudoMassG_hasStrictDerivAt` (PR #1647).
- Non-zero derivative from `pseudoMassG_deriv_neg`.
- Local-left-inverse from `pseudoMass_spec` on a neighborhood of `c₀` in `Ioo 0 2`.

**References**: Glimm–Jaffe §17.5, p. 311 (implicit differentiation).
**Issue**: tracks Step 117i of Issue #1645. -/
theorem pseudoMass_hasStrictDerivAt {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {c₀ : ℝ} (hc₀ : c₀ ∈ Set.Ioo 0 2) :
    HasStrictDerivAt
      (fun c => if hc : c ∈ Set.Ioo 0 2 then pseudoMass hα hr hc else 0)
      (((-2 * r * Real.exp (-(pseudoMass hα hr hc₀ * r)) *
            (1 + (pseudoMass hα hr hc₀ * r) ^ α) -
          2 * Real.exp (-(pseudoMass hα hr hc₀ * r)) *
            (↑α * (pseudoMass hα hr hc₀ * r) ^ (α - 1) * r)) /
         (1 + (pseudoMass hα hr hc₀ * r) ^ α) ^ 2)⁻¹) c₀ := by
  set g : ℝ → ℝ := fun c =>
    if hc : c ∈ Set.Ioo 0 2 then pseudoMass hα hr hc else 0 with hg_def
  have hg_at_c₀ : g c₀ = pseudoMass hα hr hc₀ := by
    change (if hc : c₀ ∈ Set.Ioo 0 2 then pseudoMass hα hr hc else 0) =
        pseudoMass hα hr hc₀
    rw [dif_pos hc₀]
  -- Hypotheses for `HasStrictDerivAt.of_local_left_inverse`
  have hg_cont : ContinuousAt g c₀ := pseudoMass_continuousAt hα hr hc₀
  have hpm_pos : 0 < pseudoMass hα hr hc₀ := pseudoMass_pos hα hr hc₀
  have hf_strict : HasStrictDerivAt (pseudoMassG α r)
      ((-2 * r * Real.exp (-(pseudoMass hα hr hc₀ * r)) *
            (1 + (pseudoMass hα hr hc₀ * r) ^ α) -
          2 * Real.exp (-(pseudoMass hα hr hc₀ * r)) *
            (↑α * (pseudoMass hα hr hc₀ * r) ^ (α - 1) * r)) /
         (1 + (pseudoMass hα hr hc₀ * r) ^ α) ^ 2)
      (g c₀) := by
    rw [hg_at_c₀]
    exact pseudoMassG_hasStrictDerivAt α hpm_pos.le hr
  have hf_ne :
      ((-2 * r * Real.exp (-(pseudoMass hα hr hc₀ * r)) *
            (1 + (pseudoMass hα hr hc₀ * r) ^ α) -
          2 * Real.exp (-(pseudoMass hα hr hc₀ * r)) *
            (↑α * (pseudoMass hα hr hc₀ * r) ^ (α - 1) * r)) /
         (1 + (pseudoMass hα hr hc₀ * r) ^ α) ^ 2) ≠ 0 :=
    ne_of_lt (pseudoMassG_deriv_neg α hpm_pos hr)
  -- Local-left-inverse: pseudoMassG α r (g y) = y for y near c₀ in Ioo 0 2
  have hfg : ∀ᶠ y in nhds c₀, pseudoMassG α r (g y) = y := by
    filter_upwards [Ioo_mem_nhds hc₀.1 hc₀.2] with y hy
    change pseudoMassG α r
        (if hc : y ∈ Set.Ioo 0 2 then pseudoMass hα hr hc else 0) = y
    rw [dif_pos hy]
    exact pseudoMass_spec hα hr hy
  exact hf_strict.of_local_left_inverse hg_cont hf_ne hfg

/-- **Step 117i corollary: `pseudoMass` `HasDerivAt`** (non-strict version). -/
theorem pseudoMass_hasDerivAt {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {c₀ : ℝ} (hc₀ : c₀ ∈ Set.Ioo 0 2) :
    HasDerivAt
      (fun c => if hc : c ∈ Set.Ioo 0 2 then pseudoMass hα hr hc else 0)
      (((-2 * r * Real.exp (-(pseudoMass hα hr hc₀ * r)) *
            (1 + (pseudoMass hα hr hc₀ * r) ^ α) -
          2 * Real.exp (-(pseudoMass hα hr hc₀ * r)) *
            (↑α * (pseudoMass hα hr hc₀ * r) ^ (α - 1) * r)) /
         (1 + (pseudoMass hα hr hc₀ * r) ^ α) ^ 2)⁻¹) c₀ :=
  (pseudoMass_hasStrictDerivAt hα hr hc₀).hasDerivAt

/-- **Step 117i corollary: `pseudoMass` `DifferentiableAt`**. -/
theorem pseudoMass_differentiableAt {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {c₀ : ℝ} (hc₀ : c₀ ∈ Set.Ioo 0 2) :
    DifferentiableAt ℝ
      (fun c => if hc : c ∈ Set.Ioo 0 2 then pseudoMass hα hr hc else 0) c₀ :=
  (pseudoMass_hasDerivAt hα hr hc₀).differentiableAt

/-- **Step 117i corollary: `pseudoMass` `DifferentiableOn` `Ioo 0 2`**. -/
theorem pseudoMass_differentiableOn {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) :
    DifferentiableOn ℝ
      (fun c => if hc : c ∈ Set.Ioo 0 2 then pseudoMass hα hr hc else 0)
      (Set.Ioo 0 2) :=
  fun _ hc₀ => (pseudoMass_differentiableAt hα hr hc₀).differentiableWithinAt

/-! ## Step 117j: named totalization `pseudoMassExt` (Issue #1645) -/

/-- **Step 117j (Issue #1645): named totalization of `pseudoMass`** as
a function `ℝ → ℝ`.

`pseudoMassExt hα hr c` returns `pseudoMass hα hr hc` if `c ∈ Ioo 0 2`,
else 0. This is a named version of the conditional `if-then-else 0`
appearing throughout `pseudoMass_continuousAt`, `_hasStrictDerivAt`,
etc., useful for cleaner statements in subsequent steps (117k, 117l)
of the §17.5 Lemma 17.5.2 plan. -/
noncomputable def pseudoMassExt {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (c : ℝ) : ℝ :=
  if hc : c ∈ Set.Ioo 0 2 then pseudoMass hα hr hc else 0

/-- **`pseudoMassExt c` agrees with `pseudoMass hα hr hc` when `c ∈ Ioo 0 2`**. -/
theorem pseudoMassExt_of_mem {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {c : ℝ} (hc : c ∈ Set.Ioo 0 2) :
    pseudoMassExt hα hr c = pseudoMass hα hr hc := by
  unfold pseudoMassExt
  rw [dif_pos hc]

/-- **`pseudoMassExt c = 0` when `c ∉ Ioo 0 2`**. -/
theorem pseudoMassExt_of_not_mem {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {c : ℝ} (hc : c ∉ Set.Ioo 0 2) :
    pseudoMassExt hα hr c = 0 := by
  unfold pseudoMassExt
  rw [dif_neg hc]

/-- **`pseudoMassExt` non-negative**. -/
theorem pseudoMassExt_nonneg {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (c : ℝ) :
    0 ≤ pseudoMassExt hα hr c := by
  unfold pseudoMassExt
  by_cases hc : c ∈ Set.Ioo 0 2
  · rw [dif_pos hc]
    exact pseudoMass_nonneg hα hr hc
  · rw [dif_neg hc]

/-- **`pseudoMassExt` positive on `Ioo 0 2`**. -/
theorem pseudoMassExt_pos_of_mem {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {c : ℝ} (hc : c ∈ Set.Ioo 0 2) :
    0 < pseudoMassExt hα hr c := by
  rw [pseudoMassExt_of_mem hα hr hc]
  exact pseudoMass_pos hα hr hc

/-- **`pseudoMassExt c ≠ 0`** for `c ∈ Ioo 0 2`. -/
theorem pseudoMassExt_ne_zero_of_mem {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {c : ℝ} (hc : c ∈ Set.Ioo 0 2) :
    pseudoMassExt hα hr c ≠ 0 :=
  (pseudoMassExt_pos_of_mem hα hr hc).ne'

/-- **`pseudoMassExt c ∈ Set.Ici 0`** (always): direct from
`pseudoMassExt_nonneg`. -/
theorem pseudoMassExt_mem_Ici_zero {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (c : ℝ) :
    pseudoMassExt hα hr c ∈ Set.Ici (0 : ℝ) :=
  pseudoMassExt_nonneg hα hr c

/-- **`pseudoMassExt c ∈ Set.Ioi 0`** for `c ∈ Ioo 0 2`. -/
theorem pseudoMassExt_mem_Ioi_zero_of_mem {α : ℕ} (hα : 1 ≤ α) {r : ℝ}
    (hr : 0 < r) {c : ℝ} (hc : c ∈ Set.Ioo 0 2) :
    pseudoMassExt hα hr c ∈ Set.Ioi (0 : ℝ) :=
  pseudoMassExt_pos_of_mem hα hr hc


/-- **`pseudoMassExt c ∈ Set.Ioo 0 (log(2/c)/r)`** for `c ∈ Ioo 0 2`:
combine pos with strict log upper bound. -/
theorem pseudoMassExt_mem_Ioo_zero_log_two_div {α : ℕ} (hα : 1 ≤ α) {r : ℝ}
    (hr : 0 < r) {c : ℝ} (hc : c ∈ Set.Ioo 0 2) :
    pseudoMassExt hα hr c ∈ Set.Ioo (0 : ℝ) (Real.log (2 / c) / r) := by
  rw [pseudoMassExt_of_mem hα hr hc]
  exact pseudoMass_mem_Ioo_zero_log_two_div hα hr hc

/-- **`pseudoMassExt c ∈ Set.Ioo 0 ((2-c)/(c·r))`** for `c ∈ Ioo 0 2`. -/
theorem pseudoMassExt_mem_Ioo_zero_two_sub_div {α : ℕ} (hα : 1 ≤ α) {r : ℝ}
    (hr : 0 < r) {c : ℝ} (hc : c ∈ Set.Ioo 0 2) :
    pseudoMassExt hα hr c ∈ Set.Ioo (0 : ℝ) ((2 - c) / (c * r)) := by
  rw [pseudoMassExt_of_mem hα hr hc]
  exact pseudoMass_mem_Ioo_zero_two_sub_div hα hr hc

/-- **`pseudoMassExt c ∈ Set.Iio (log(2/c)/r)`** for `c ∈ Ioo 0 2`. -/
theorem pseudoMassExt_mem_Iio_log_two_div {α : ℕ} (hα : 1 ≤ α) {r : ℝ}
    (hr : 0 < r) {c : ℝ} (hc : c ∈ Set.Ioo 0 2) :
    pseudoMassExt hα hr c ∈ Set.Iio (Real.log (2 / c) / r) := by
  rw [pseudoMassExt_of_mem hα hr hc]
  exact pseudoMass_mem_Iio_log_two_div hα hr hc

/-- **`pseudoMassExt c ∈ Set.Iio ((2-c)/(c·r))`** for `c ∈ Ioo 0 2`. -/
theorem pseudoMassExt_mem_Iio_two_sub_div {α : ℕ} (hα : 1 ≤ α) {r : ℝ}
    (hr : 0 < r) {c : ℝ} (hc : c ∈ Set.Ioo 0 2) :
    pseudoMassExt hα hr c ∈ Set.Iio ((2 - c) / (c * r)) := by
  rw [pseudoMassExt_of_mem hα hr hc]
  exact pseudoMass_mem_Iio_two_sub_div hα hr hc

/-- **`0 < pseudoMassExt c ↔ pseudoMassExt c ≠ 0`**: standard
nonneg → pos iff ne_zero pattern (`pseudoMassExt_nonneg`). -/
theorem pseudoMassExt_pos_iff_ne_zero {α : ℕ} (hα : 1 ≤ α) {r : ℝ}
    (hr : 0 < r) (c : ℝ) :
    0 < pseudoMassExt hα hr c ↔ pseudoMassExt hα hr c ≠ 0 :=
  (pseudoMassExt_nonneg hα hr c).lt_iff_ne.trans
    ⟨fun h => h.symm, fun h => h.symm⟩

/-- **`¬(pseudoMassExt c < 0)`**: trivial via nonneg. -/
theorem pseudoMassExt_not_lt_zero {α : ℕ} (hα : 1 ≤ α) {r : ℝ}
    (hr : 0 < r) (c : ℝ) :
    ¬ (pseudoMassExt hα hr c < 0) :=
  not_lt.mpr (pseudoMassExt_nonneg hα hr c)

/-- **`pseudoMassExt c ≤ 0 ↔ pseudoMassExt c = 0`**: trivial via
nonneg + antisymmetry. -/
theorem pseudoMassExt_le_zero_iff_eq_zero {α : ℕ} (hα : 1 ≤ α) {r : ℝ}
    (hr : 0 < r) (c : ℝ) :
    pseudoMassExt hα hr c ≤ 0 ↔ pseudoMassExt hα hr c = 0 := by
  refine ⟨?_, fun h => le_of_eq h⟩
  intro hle
  exact le_antisymm hle (pseudoMassExt_nonneg hα hr c)

/-- **`pseudoMassExt` `ContinuousAt c₀ ∈ Ioo 0 2`**: re-statement of
`pseudoMass_continuousAt` using the named definition. -/
theorem pseudoMassExt_continuousAt {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {c₀ : ℝ} (hc₀ : c₀ ∈ Set.Ioo 0 2) :
    ContinuousAt (pseudoMassExt hα hr) c₀ :=
  pseudoMass_continuousAt hα hr hc₀

/-- **`pseudoMassExt` `HasStrictDerivAt c₀ ∈ Ioo 0 2`**: re-statement of
`pseudoMass_hasStrictDerivAt` using the named definition. -/
theorem pseudoMassExt_hasStrictDerivAt {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {c₀ : ℝ} (hc₀ : c₀ ∈ Set.Ioo 0 2) :
    HasStrictDerivAt (pseudoMassExt hα hr)
      (((-2 * r * Real.exp (-(pseudoMass hα hr hc₀ * r)) *
            (1 + (pseudoMass hα hr hc₀ * r) ^ α) -
          2 * Real.exp (-(pseudoMass hα hr hc₀ * r)) *
            (↑α * (pseudoMass hα hr hc₀ * r) ^ (α - 1) * r)) /
         (1 + (pseudoMass hα hr hc₀ * r) ^ α) ^ 2)⁻¹) c₀ :=
  pseudoMass_hasStrictDerivAt hα hr hc₀

/-- **`pseudoMassExt` `DifferentiableAt c₀ ∈ Ioo 0 2`**. -/
theorem pseudoMassExt_differentiableAt {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {c₀ : ℝ} (hc₀ : c₀ ∈ Set.Ioo 0 2) :
    DifferentiableAt ℝ (pseudoMassExt hα hr) c₀ :=
  pseudoMass_differentiableAt hα hr hc₀

/-- **`pseudoMassExt` `DifferentiableOn (Ioo 0 2)`**. -/
theorem pseudoMassExt_differentiableOn {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) :
    DifferentiableOn ℝ (pseudoMassExt hα hr) (Set.Ioo 0 2) :=
  pseudoMass_differentiableOn hα hr

/-- **`pseudoMassExt` strict anti on `Ioo 0 2`**: lifted from
`pseudoMass_strictAnti`. -/
theorem pseudoMassExt_strictAntiOn {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) :
    StrictAntiOn (pseudoMassExt hα hr) (Set.Ioo 0 2) := by
  intro c₁ hc₁ c₂ hc₂ h
  rw [pseudoMassExt_of_mem hα hr hc₁, pseudoMassExt_of_mem hα hr hc₂]
  exact pseudoMass_strictAnti hα hr hc₁ hc₂ h

/-- **`pseudoMassExt` antitone (non-strict) on `Ioo 0 2`**: weaker form
of `_strictAntiOn`. Convenience corollary for non-strict bound chains. -/
theorem pseudoMassExt_antitoneOn {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) :
    AntitoneOn (pseudoMassExt hα hr) (Set.Ioo 0 2) :=
  (pseudoMassExt_strictAntiOn hα hr).antitoneOn

/-- **`-pseudoMassExt` is `StrictMonoOn (Ioo 0 2)`**: dual of
`pseudoMassExt_strictAntiOn`. -/
theorem neg_pseudoMassExt_strictMonoOn {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) :
    StrictMonoOn (fun c => -pseudoMassExt hα hr c) (Set.Ioo 0 2) := by
  intro c₁ hc₁ c₂ hc₂ h
  have hgt : pseudoMassExt hα hr c₂ < pseudoMassExt hα hr c₁ :=
    pseudoMassExt_strictAntiOn hα hr hc₁ hc₂ h
  linarith

/-- **`-pseudoMassExt` is `MonotoneOn (Ioo 0 2)`**: non-strict. -/
theorem neg_pseudoMassExt_monotoneOn {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) :
    MonotoneOn (fun c => -pseudoMassExt hα hr c) (Set.Ioo 0 2) :=
  (neg_pseudoMassExt_strictMonoOn hα hr).monotoneOn


/-- **`pseudoMassExt(c₂) < pseudoMassExt(c₁) ↔ c₁ < c₂`** for both
in `Ioo 0 2`: iff form of `pseudoMassExt_strictAntiOn`. -/
theorem pseudoMassExt_lt_iff {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {c₁ c₂ : ℝ} (hc₁ : c₁ ∈ Set.Ioo 0 2) (hc₂ : c₂ ∈ Set.Ioo 0 2) :
    pseudoMassExt hα hr c₂ < pseudoMassExt hα hr c₁ ↔ c₁ < c₂ := by
  rw [pseudoMassExt_of_mem hα hr hc₁, pseudoMassExt_of_mem hα hr hc₂]
  exact pseudoMass_lt_iff hα hr hc₁ hc₂

/-- **`pseudoMassExt(c₂) ≤ pseudoMassExt(c₁) ↔ c₁ ≤ c₂`** for both
in `Ioo 0 2`. -/
theorem pseudoMassExt_le_iff {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {c₁ c₂ : ℝ} (hc₁ : c₁ ∈ Set.Ioo 0 2) (hc₂ : c₂ ∈ Set.Ioo 0 2) :
    pseudoMassExt hα hr c₂ ≤ pseudoMassExt hα hr c₁ ↔ c₁ ≤ c₂ := by
  rw [pseudoMassExt_of_mem hα hr hc₁, pseudoMassExt_of_mem hα hr hc₂]
  exact pseudoMass_le_iff hα hr hc₁ hc₂

/-- **`pseudoMassExt(c₂) = pseudoMassExt(c₁) ↔ c₁ = c₂`** for both
in `Ioo 0 2`. -/
theorem pseudoMassExt_eq_iff_of_mem {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {c₁ c₂ : ℝ} (hc₁ : c₁ ∈ Set.Ioo 0 2) (hc₂ : c₂ ∈ Set.Ioo 0 2) :
    pseudoMassExt hα hr c₂ = pseudoMassExt hα hr c₁ ↔ c₁ = c₂ := by
  rw [pseudoMassExt_of_mem hα hr hc₁, pseudoMassExt_of_mem hα hr hc₂]
  exact pseudoMass_eq_iff_eq hα hr hc₁ hc₂

/-- **`pseudoMassExt` strictly anti on `Ioo 0 1`** (sub-interval of
`Ioo 0 2`): convenient when working with `tanh^2 ∈ [0, 1)` regime. -/
theorem pseudoMassExt_strictAntiOn_Ioo_zero_one
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) :
    StrictAntiOn (pseudoMassExt hα hr) (Set.Ioo 0 1) := by
  intro c₁ hc₁ c₂ hc₂ h
  have hc₁_in : c₁ ∈ Set.Ioo (0 : ℝ) 2 := ⟨hc₁.1, by linarith [hc₁.2]⟩
  have hc₂_in : c₂ ∈ Set.Ioo (0 : ℝ) 2 := ⟨hc₂.1, by linarith [hc₂.2]⟩
  exact pseudoMassExt_strictAntiOn hα hr hc₁_in hc₂_in h

/-- **`pseudoMassExt` antitone on `Ioo 0 1`** (sub-interval form). -/
theorem pseudoMassExt_antitoneOn_Ioo_zero_one
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) :
    AntitoneOn (pseudoMassExt hα hr) (Set.Ioo 0 1) :=
  (pseudoMassExt_strictAntiOn_Ioo_zero_one hα hr).antitoneOn

/-- **`-pseudoMassExt` is `StrictMonoOn (Ioo 0 1)`**: sub-interval. -/
theorem neg_pseudoMassExt_strictMonoOn_Ioo_zero_one
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) :
    StrictMonoOn (fun c => -pseudoMassExt hα hr c) (Set.Ioo 0 1) := by
  intro c₁ hc₁ c₂ hc₂ h
  have hgt : pseudoMassExt hα hr c₂ < pseudoMassExt hα hr c₁ :=
    pseudoMassExt_strictAntiOn_Ioo_zero_one hα hr hc₁ hc₂ h
  linarith

/-- **`pseudoMassExt` strictly anti on `Ioc 0 1`** (boundary-inclusive
sub-interval): `Ioc 0 1 ⊂ Ioo 0 2` since `1 < 2`. -/
theorem pseudoMassExt_strictAntiOn_Ioc_zero_one
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) :
    StrictAntiOn (pseudoMassExt hα hr) (Set.Ioc 0 1) := by
  intro c₁ hc₁ c₂ hc₂ h
  have hc₁_in : c₁ ∈ Set.Ioo (0 : ℝ) 2 := ⟨hc₁.1, by linarith [hc₁.2]⟩
  have hc₂_in : c₂ ∈ Set.Ioo (0 : ℝ) 2 := ⟨hc₂.1, by linarith [hc₂.2]⟩
  exact pseudoMassExt_strictAntiOn hα hr hc₁_in hc₂_in h

/-- **`pseudoMassExt` antitone on `Ioc 0 1`**. -/
theorem pseudoMassExt_antitoneOn_Ioc_zero_one
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) :
    AntitoneOn (pseudoMassExt hα hr) (Set.Ioc 0 1) :=
  (pseudoMassExt_strictAntiOn_Ioc_zero_one hα hr).antitoneOn

/-- **`-pseudoMassExt` is `StrictMonoOn (Ioc 0 1)`**. -/
theorem neg_pseudoMassExt_strictMonoOn_Ioc_zero_one
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) :
    StrictMonoOn (fun c => -pseudoMassExt hα hr c) (Set.Ioc 0 1) := by
  intro c₁ hc₁ c₂ hc₂ h
  have hgt : pseudoMassExt hα hr c₂ < pseudoMassExt hα hr c₁ :=
    pseudoMassExt_strictAntiOn_Ioc_zero_one hα hr hc₁ hc₂ h
  linarith

/-- **`-pseudoMassExt` is `MonotoneOn (Ioc 0 1)`**. -/
theorem neg_pseudoMassExt_monotoneOn_Ioc_zero_one
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) :
    MonotoneOn (fun c => -pseudoMassExt hα hr c) (Set.Ioc 0 1) :=
  (neg_pseudoMassExt_strictMonoOn_Ioc_zero_one hα hr).monotoneOn

/-- **`pseudoMassExt(tanh(t)^2)` `ContinuousAt` for `0 < t`**: composition
of continuous functions. `tanh` is continuous, squaring is continuous,
`pseudoMassExt` is continuous at `tanh(t)^2 ∈ Ioo 0 1 ⊂ Ioo 0 2`. -/
theorem pseudoMassExt_tanh_sq_continuousAt_pos
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) {t : ℝ} (ht : 0 < t) :
    ContinuousAt (fun s : ℝ => pseudoMassExt hα hr (Real.tanh s ^ 2)) t := by
  have htanh_pos : 0 < Real.tanh t := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr ht) (Real.cosh_pos _)
  have htanh_lt : Real.tanh t < 1 := lt_of_abs_lt (Real.abs_tanh_lt_one _)
  have hmem : Real.tanh t ^ 2 ∈ Set.Ioo (0 : ℝ) 2 := by
    refine ⟨by positivity, ?_⟩
    nlinarith
  have h_tanh_cont : Continuous Real.tanh := by
    have h_eq : Real.tanh = fun x : ℝ => Real.sinh x / Real.cosh x :=
      funext (fun x => Real.tanh_eq_sinh_div_cosh x)
    rw [h_eq]
    exact Real.continuous_sinh.div Real.continuous_cosh
      (fun x => (Real.cosh_pos x).ne')
  have h_tanh_cont_at : ContinuousAt Real.tanh t := h_tanh_cont.continuousAt
  have h_sq_cont_at : ContinuousAt (fun x : ℝ => x ^ 2) (Real.tanh t) :=
    (continuous_pow 2).continuousAt
  have h_inner_cont : ContinuousAt (fun s : ℝ => Real.tanh s ^ 2) t :=
    h_sq_cont_at.comp h_tanh_cont_at
  have h_outer_cont : ContinuousAt (pseudoMassExt hα hr) (Real.tanh t ^ 2) :=
    pseudoMassExt_continuousAt hα hr hmem
  change ContinuousAt ((pseudoMassExt hα hr) ∘ (fun s : ℝ => Real.tanh s ^ 2)) t
  exact ContinuousAt.comp h_outer_cont h_inner_cont

/-- **`pseudoMassExt(tanh(t)^2)` `DifferentiableAt` for `0 < t`**:
composition of differentiable functions on `Ioi 0`. -/
theorem pseudoMassExt_tanh_sq_differentiableAt_pos
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) {t : ℝ} (ht : 0 < t) :
    DifferentiableAt ℝ (fun s : ℝ => pseudoMassExt hα hr (Real.tanh s ^ 2)) t := by
  have htanh_pos : 0 < Real.tanh t := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr ht) (Real.cosh_pos _)
  have htanh_lt : Real.tanh t < 1 := lt_of_abs_lt (Real.abs_tanh_lt_one _)
  have hmem : Real.tanh t ^ 2 ∈ Set.Ioo (0 : ℝ) 2 := by
    refine ⟨by positivity, ?_⟩
    nlinarith
  have h_tanh_diff : Differentiable ℝ Real.tanh := by
    have h_eq : Real.tanh = fun x : ℝ => Real.sinh x / Real.cosh x :=
      funext (fun x => Real.tanh_eq_sinh_div_cosh x)
    rw [h_eq]
    exact Real.differentiable_sinh.div Real.differentiable_cosh
      (fun x => (Real.cosh_pos x).ne')
  have h_tanh_diff_at : DifferentiableAt ℝ Real.tanh t := h_tanh_diff.differentiableAt
  have h_sq_diff_at : DifferentiableAt ℝ (fun x : ℝ => x ^ 2) (Real.tanh t) :=
    (differentiable_pow 2).differentiableAt
  have h_inner_diff : DifferentiableAt ℝ (fun s : ℝ => Real.tanh s ^ 2) t :=
    h_sq_diff_at.comp t h_tanh_diff_at
  have h_outer_diff : DifferentiableAt ℝ (pseudoMassExt hα hr) (Real.tanh t ^ 2) :=
    pseudoMassExt_differentiableAt hα hr hmem
  change DifferentiableAt ℝ ((pseudoMassExt hα hr) ∘ (fun s : ℝ => Real.tanh s ^ 2)) t
  exact DifferentiableAt.comp t h_outer_diff h_inner_diff

/-- **`pseudoMassExt(tanh(t)^2)` strictly anti in `t` on `Ioi 0`**:
the composition of the strictly increasing `t ↦ tanh(t)^2` (mapping
`Ioi 0` into `Ioo 0 1`) with the strictly anti `pseudoMassExt`
(restricted to `Ioo 0 1`) is strictly anti. Useful for §17.5 §J=0
slice analysis where the bridge is `pseudoMassExt(tanh(β·h)^2)`
parametrised by the product `β·h`. -/
theorem pseudoMassExt_tanh_sq_strictAntiOn_Ioi_zero
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) :
    StrictAntiOn (fun t : ℝ => pseudoMassExt hα hr (Real.tanh t ^ 2))
      (Set.Ioi 0) := by
  intro t₁ ht₁ t₂ ht₂ hlt
  simp only [Set.mem_Ioi] at ht₁ ht₂
  have htanh_pos₁ : 0 < Real.tanh t₁ := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr ht₁) (Real.cosh_pos _)
  have htanh_pos₂ : 0 < Real.tanh t₂ := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr ht₂) (Real.cosh_pos _)
  have htanh_lt₁ : Real.tanh t₁ < 1 := lt_of_abs_lt (Real.abs_tanh_lt_one _)
  have htanh_lt₂ : Real.tanh t₂ < 1 := lt_of_abs_lt (Real.abs_tanh_lt_one _)
  have htanh_mono : Real.tanh t₁ < Real.tanh t₂ := Real.tanh_strictMono hlt
  have hsq_lt : Real.tanh t₁ ^ 2 < Real.tanh t₂ ^ 2 := by
    have h1 : Real.tanh t₁ ^ 2 = Real.tanh t₁ * Real.tanh t₁ := sq _
    have h2 : Real.tanh t₂ ^ 2 = Real.tanh t₂ * Real.tanh t₂ := sq _
    rw [h1, h2]
    exact mul_lt_mul' htanh_mono.le htanh_mono htanh_pos₁.le htanh_pos₂
  have hmem₁ : Real.tanh t₁ ^ 2 ∈ Set.Ioo (0 : ℝ) 1 := by
    refine ⟨by positivity, ?_⟩
    nlinarith
  have hmem₂ : Real.tanh t₂ ^ 2 ∈ Set.Ioo (0 : ℝ) 1 := by
    refine ⟨by positivity, ?_⟩
    nlinarith
  exact pseudoMassExt_strictAntiOn_Ioo_zero_one hα hr hmem₁ hmem₂ hsq_lt

/-- **`pseudoMassExt` continuous on `Ioo 0 2`**: lifted from
`pseudoMass_continuousOn`. -/
theorem pseudoMassExt_continuousOn {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) :
    ContinuousOn (pseudoMassExt hα hr) (Set.Ioo 0 2) :=
  pseudoMass_continuousOn hα hr

/-- **`pseudoMassExt c = 0 ↔ c ∉ Ioo 0 2`**: characterisation. The
forward direction uses `pseudoMass_pos` (positive on `Ioo 0 2`) to
contradict `pseudoMassExt = 0` when `c ∈ Ioo 0 2`. -/
theorem pseudoMassExt_eq_zero_iff {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (c : ℝ) :
    pseudoMassExt hα hr c = 0 ↔ c ∉ Set.Ioo (0 : ℝ) 2 := by
  refine ⟨?_, pseudoMassExt_of_not_mem hα hr⟩
  intro h_eq
  by_contra hmem
  -- `by_contra` cleaned up the double negation: `hmem : c ∈ Ioo 0 2`
  have : 0 < pseudoMassExt hα hr c := pseudoMassExt_pos_of_mem hα hr hmem
  linarith

/-- **`pseudoMassExt c > 0 ↔ c ∈ Ioo 0 2`**: dual characterisation. -/
theorem pseudoMassExt_pos_iff {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (c : ℝ) :
    0 < pseudoMassExt hα hr c ↔ c ∈ Set.Ioo (0 : ℝ) 2 := by
  refine ⟨?_, pseudoMassExt_pos_of_mem hα hr⟩
  intro h_pos
  by_contra hnotmem
  rw [pseudoMassExt_of_not_mem hα hr hnotmem] at h_pos
  exact lt_irrefl 0 h_pos

/-- **`pseudoMassExt c ∈ Set.Ioi 0 ↔ c ∈ Ioo 0 2`**: combines positivity
iff with mem reformulation. -/
theorem pseudoMassExt_mem_Ioi_iff_mem {α : ℕ} (hα : 1 ≤ α) {r : ℝ}
    (hr : 0 < r) (c : ℝ) :
    pseudoMassExt hα hr c ∈ Set.Ioi (0 : ℝ) ↔ c ∈ Set.Ioo (0 : ℝ) 2 :=
  pseudoMassExt_pos_iff hα hr c

/-- **`pseudoMassExt c ∈ Set.Iio 0` is False**: `pseudoMassExt` is nonneg. -/
theorem pseudoMassExt_not_mem_Iio_zero {α : ℕ} (hα : 1 ≤ α) {r : ℝ}
    (hr : 0 < r) (c : ℝ) :
    pseudoMassExt hα hr c ∉ Set.Iio (0 : ℝ) :=
  not_lt.mpr (pseudoMassExt_nonneg hα hr c)

/-- **`pseudoMassExt 0 = 0`**: zero is not in `Ioo 0 2` (open interval). -/
theorem pseudoMassExt_zero {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) :
    pseudoMassExt hα hr 0 = 0 :=
  pseudoMassExt_of_not_mem hα hr (by simp [Set.mem_Ioo])

/-- **`pseudoMassExt 2 = 0`**: 2 is not in `Ioo 0 2` (open interval). -/
theorem pseudoMassExt_two {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) :
    pseudoMassExt hα hr 2 = 0 :=
  pseudoMassExt_of_not_mem hα hr (by simp [Set.mem_Ioo])

/-- **`pseudoMassExt` of a negative value = 0**. -/
theorem pseudoMassExt_of_nonpos {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {c : ℝ} (hc : c ≤ 0) :
    pseudoMassExt hα hr c = 0 := by
  apply pseudoMassExt_of_not_mem
  intro hmem
  exact lt_irrefl 0 (lt_of_lt_of_le hmem.1 hc)

/-- **`pseudoMassExt` of a value ≥ 2 = 0**. -/
theorem pseudoMassExt_of_two_le {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {c : ℝ} (hc : 2 ≤ c) :
    pseudoMassExt hα hr c = 0 := by
  apply pseudoMassExt_of_not_mem
  intro hmem
  exact lt_irrefl 2 (lt_of_le_of_lt hc hmem.2)

/-! ## Continuity of pseudoMass composition with correlation (Step 120) -/

/-- **pseudoMass∘correlation is continuous in β** (Step 120).

When the correlation `c(β) = ⟨σ^A⟩_β` lies in `(0, 2)`, the totalized function
`β ↦ if c(β) ∈ Ioo 0 2 then pseudoMass(c(β)) else 0` is continuous at `β`.

Proof: manual ContinuousAt composition via Filter.Tendsto.

This is a partial result toward GJ §17.5 Thm 17.5.1: the full theorem requires
connecting the abstract pseudoMass to the concrete lattice mass via Lemma 17.5.2 bounds.

**References**: Glimm–Jaffe §17.5 pp.310–312.
-/
theorem pseudoMass_comp_corr_continuousAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (A : Finset ι)
    (hcorr : correlation G (⟨J, 0, β⟩ : IsingParams ℝ) A ∈ Set.Ioo 0 2) :
    ContinuousAt (fun β' =>
        if hc : correlation G (⟨J, 0, β'⟩ : IsingParams ℝ) A ∈ Set.Ioo 0 2
        then pseudoMass hα hr hc else 0) β := by
  -- Proof via continuousAt_def + manual composition (Filter.Tendsto)
  set c₀ := correlation G (⟨J, 0, β⟩ : IsingParams ℝ) A
  have h_g := (IsingModel.correlation_continuousAt_beta G J β A).tendsto
  have h_f := (pseudoMass_continuousAt hα hr hcorr).tendsto
  rw [continuousAt_def]
  intro s hs
  exact h_g (h_f hs)

/-! ## Antitonicity of pseudoMass ∘ correlation in β (Step 123) -/

/-- **Step 123**: `β ↦ pseudoMass(c(β))` is antitone in β.

When the correlation `c(β) = ⟨σ^A⟩_β` lies in `(0, 2)` for all `β > 0`,
the pseudo-mass `β ↦ pseudoMass(c(β))` is antitone (decreasing) on `Ioi 0`.

Proof: compose `correlation_monotoneOn_beta` (β ↑ → c(β) ↑) with `pseudoMass_strictAnti`
(c ↑ → pseudoMass(c) ↓).

This completes the §17.5 accessible content: higher β → larger correlation →
smaller pseudo-mass (approaching zero at β_c).

Reference: derived from `pseudoMass_strictAnti` (Step 117g) and
`correlation_monotoneOn_beta` (Step 122); implicit in the §17.5 pseudo-mass analysis
(Glimm–Jaffe §17.5, 2nd ed., pp. 311–312). -/
theorem pseudoMass_comp_corr_antitoneOn_beta
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (A : Finset ι)
    (hc_mem : ∀ β : ℝ, 0 < β →
        correlation G (⟨J, 0, β⟩ : IsingParams ℝ) A ∈ Set.Ioo 0 2) :
    AntitoneOn
      (fun β => if h : 0 < β then pseudoMass hα hr (hc_mem β h) else 0)
      (Set.Ioi 0) := by
  intro β₁ hβ₁ β₂ hβ₂ hle
  simp only [Set.mem_Ioi] at hβ₁ hβ₂
  simp only [dif_pos hβ₁, dif_pos hβ₂]
  have hcle : correlation G (⟨J, 0, β₁⟩ : IsingParams ℝ) A ≤
              correlation G (⟨J, 0, β₂⟩ : IsingParams ℝ) A :=
    correlation_monotoneOn_beta G J hJ A
      (Set.mem_Ici.mpr hβ₁.le) (Set.mem_Ici.mpr hβ₂.le) hle
  by_cases heq : correlation G (⟨J, 0, β₁⟩ : IsingParams ℝ) A =
                 correlation G (⟨J, 0, β₂⟩ : IsingParams ℝ) A
  · simp [heq]
  · exact le_of_lt
      (pseudoMass_strictAnti hα hr (hc_mem β₁ hβ₁) (hc_mem β₂ hβ₂)
        (lt_of_le_of_ne hcle heq))

/-! ## Step 117k: concrete `pseudoMassFromParamsAtPair` (Issue #1645)

Bridges the abstract `pseudoMassExt : ℝ → ℝ` to the concrete physical
parameters `(d, Λ, p, x, z)` by composing with the infinite-volume
correlation function `correlationInfinite (latticeGraph d) Λ p {x, z}`. -/

/-- **Step 117k (Issue #1645): concrete pseudo-mass from physical
parameters and a pair**.

`pseudoMassFromParamsAtPair α hα r hr d Λ p x z` is the pseudo-mass
associated to the infinite-volume correlation
`⟨σ_x σ_z⟩^∞ = correlationInfinite (latticeGraph d) Λ p {x, z}`,
returning `pseudoMass hα hr hc` if this correlation lies in `Ioo 0 2`,
else 0.

This bridges the abstract `pseudoMass : ℝ` (parameterized by `α, r, c`)
to the concrete `latticeMass : (d, Λ, p) → ENNReal` defined in
`Concrete/LatticeGraphCorrelation/Inequalities.lean` via the
correlation at a chosen pair.

For the §17.5 Lemma 17.5.2 application, the natural choice is `r = 1`
and `α` such that `2α > d` (HLS condition); see `lemma_17_5_2_constant_exists`.

**References**: Glimm–Jaffe §17.5, p. 311. -/
noncomputable def pseudoMassFromParamsAtPair {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (x z : Fin d → ℤ) : ℝ :=
  pseudoMassExt hα hr
    (Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z})

/-- **`pseudoMassFromParamsAtPair` is non-negative**. -/
theorem pseudoMassFromParamsAtPair_nonneg {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (x z : Fin d → ℤ) :
    0 ≤ pseudoMassFromParamsAtPair hα hr d Λ p x z :=
  pseudoMassExt_nonneg hα hr _

/-- **`pseudoMassFromParamsAtPair` positive when the correlation
lies in `Ioo 0 2`**. -/
theorem pseudoMassFromParamsAtPair_pos_of_corr_mem
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (x z : Fin d → ℤ)
    (hc : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z}
            ∈ Set.Ioo (0 : ℝ) 2) :
    0 < pseudoMassFromParamsAtPair hα hr d Λ p x z :=
  pseudoMassExt_pos_of_mem hα hr hc

/-- **`pseudoMassFromParamsAtPair` is zero when the correlation falls
outside `Ioo 0 2`**. -/
theorem pseudoMassFromParamsAtPair_eq_zero_of_corr_not_mem
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (x z : Fin d → ℤ)
    (hc : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z}
            ∉ Set.Ioo (0 : ℝ) 2) :
    pseudoMassFromParamsAtPair hα hr d Λ p x z = 0 :=
  pseudoMassExt_of_not_mem hα hr hc

/-- **`pseudoMassFromParamsAtPair` at `β = 0` (infinite-temperature
trivial slice)**: equals 0 because the correlation vanishes. -/
theorem pseudoMassFromParamsAtPair_beta_zero {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J h : ℝ) (x z : Fin d → ℤ) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, h, 0⟩ : IsingParams ℝ) x z = 0 := by
  have hxz_ne : ({x, z} : Finset (Fin d → ℤ)).Nonempty :=
    ⟨x, by simp⟩
  have hcorr := Ambient.correlationInfinite_beta_zero_vanish
    (IsingModel.latticeGraph d) Λ J h {x, z} hxz_ne
  unfold pseudoMassFromParamsAtPair
  rw [hcorr]
  apply pseudoMassExt_of_not_mem
  intro hmem
  exact lt_irrefl 0 hmem.1

/-- **`pseudoMassFromParamsAtPair` at `J = 0, h = 0` (trivial-coupling
slice)**: equals 0 because the correlation `tanh(β·0)^2 = 0`.

Direct corollary of `correlationInfinite_J_zero` with `h = 0`. -/
theorem pseudoMassFromParamsAtPair_J_zero_h_zero {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {β : ℝ} (hβ : 0 < β) (x z : Fin d → ℤ) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨0, 0, β⟩ : IsingParams ℝ) x z = 0 := by
  have hf : Ferromagnetic (⟨(0 : ℝ), 0, β⟩ : IsingParams ℝ) :=
    ⟨le_refl 0, le_refl 0, hβ⟩
  have hcorr := Ambient.correlationInfinite_J_zero
    (IsingModel.latticeGraph d) Λ 0 β hf {x, z}
  unfold pseudoMassFromParamsAtPair
  rw [hcorr]
  apply pseudoMassExt_of_not_mem
  intro hmem
  -- correlation = tanh(β·0)^A.card = 0^|{x,z}| = 0
  have htanh : Real.tanh (β * 0) ^ ({x, z} : Finset (Fin d → ℤ)).card = 0 := by
    rw [mul_zero, Real.tanh_zero, zero_pow]
    exact (Finset.Nonempty.card_pos ⟨x, by simp⟩).ne'
  rw [htanh] at hmem
  exact lt_irrefl 0 hmem.1

/-- **`pseudoMassFromParamsAtPair` is symmetric in `(x, z)`**: the pair
`{x, z}` as a `Finset` is unchanged under swap, hence the correlation
and the resulting pseudo-mass are unchanged. -/
theorem pseudoMassFromParamsAtPair_symm {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (x z : Fin d → ℤ) :
    pseudoMassFromParamsAtPair hα hr d Λ p x z =
      pseudoMassFromParamsAtPair hα hr d Λ p z x := by
  unfold pseudoMassFromParamsAtPair
  congr 2
  exact Finset.pair_comm x z

/-- **`pseudoMassFromParamsAtPair` at `x = z` (degenerate pair) at h = 0**:
`{x, x} = {x}` is a singleton (odd cardinality), and at h = 0 the Z₂
symmetry forces the singleton correlation = magnetization to vanish.
Hence `pseudoMassFromParamsAtPair = 0`. -/
theorem pseudoMassFromParamsAtPair_diag_h_zero {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x : Fin d → ℤ) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x x = 0 := by
  unfold pseudoMassFromParamsAtPair
  have hsing : ({x, x} : Finset (Fin d → ℤ)) = {x} := by
    ext y; simp
  rw [hsing]
  have hodd : Odd (({x} : Finset (Fin d → ℤ)).card) := by
    simp only [Finset.card_singleton]
    exact ⟨0, rfl⟩
  have hcorr := Ambient.correlationInfinite_h_zero
    (IsingModel.latticeGraph d) Λ J β {x} hodd
  rw [hcorr]
  apply pseudoMassExt_of_not_mem
  intro hmem
  exact lt_irrefl 0 hmem.1

/-- **`pseudoMassFromParamsAtPair` is positive at `J = 0, h > 0, β > 0`
for distinct sites**: the correlation equals `tanh(β·h)^2 ∈ (0, 1) ⊂ Ioo 0 2`,
hence `pseudoMassFromParamsAtPair > 0`. -/
theorem pseudoMassFromParamsAtPair_pos_at_J_zero {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    0 < pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h, β⟩ : IsingParams ℝ) x z := by
  apply pseudoMassFromParamsAtPair_pos_of_corr_mem
  -- correlation = tanh(β·h)^|{x, z}| = tanh(β·h)^2
  have hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ) := ⟨le_refl 0, hh.le, hβ⟩
  have hcorr := Ambient.correlationInfinite_J_zero
    (IsingModel.latticeGraph d) Λ h β hf {x, z}
  rw [hcorr]
  -- |{x, z}| = 2 since x ≠ z
  have hcard : ({x, z} : Finset (Fin d → ℤ)).card = 2 := by
    rw [Finset.card_pair hxz]
  rw [hcard]
  refine ⟨?_, ?_⟩
  · -- 0 < tanh(βh)^2
    have htanh_pos : 0 < Real.tanh (β * h) := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_pos (Real.sinh_pos_iff.mpr (mul_pos hβ hh)) (Real.cosh_pos _)
    positivity
  · -- tanh(βh)^2 < 2: tanh ∈ (-1, 1) so tanh^2 < 1 < 2
    have htanh_abs : |Real.tanh (β * h)| < 1 := Real.abs_tanh_lt_one _
    have hsq_lt : Real.tanh (β * h) ^ 2 < 1 := by
      have h1 : -1 < Real.tanh (β * h) := neg_lt_of_abs_lt htanh_abs
      have h2 : Real.tanh (β * h) < 1 := lt_of_abs_lt htanh_abs
      nlinarith
    linarith

/-- **`pseudoMassFromParamsAtPair` at `J = 0` explicit form**: equals
`pseudoMass` evaluated at `tanh(βh)^|{x,z}|`. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_eq {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    (x z : Fin d → ℤ) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h, β⟩ : IsingParams ℝ) x z =
      pseudoMassExt hα hr (Real.tanh (β * h) ^
                            ({x, z} : Finset (Fin d → ℤ)).card) := by
  unfold pseudoMassFromParamsAtPair
  rw [Ambient.correlationInfinite_J_zero (IsingModel.latticeGraph d) Λ h β hf {x, z}]

/-- **`pseudoMassFromParamsAtPair_at_J_zero_eq` distinct form**:
under `x ≠ z`, the cardinality is 2, giving an explicit `tanh^2`. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_eq {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    {x z : Fin d → ℤ} (hxz : x ≠ z) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h, β⟩ : IsingParams ℝ) x z =
      pseudoMassExt hα hr (Real.tanh (β * h) ^ 2) := by
  rw [pseudoMassFromParamsAtPair_at_J_zero_eq hα hr d Λ hf x z, Finset.card_pair hxz]

/-- **`pseudoMassFromParamsAtPair` at `h = 0` equals
`pseudoMassExt(truncated2Infinite)`**: at zero external field, the
unconnected pair correlation `⟨σ_x σ_z⟩` agrees with the truncated
2-point Ursell function `⟨σ_x σ_z⟩ - ⟨σ_x⟩⟨σ_z⟩`, since the spin-flip
symmetry forces `⟨σ_x⟩ = ⟨σ_z⟩ = 0`. Thus

  `pseudoMassFromParamsAtPair hα hr d Λ ⟨J, 0, β⟩ x z =
   pseudoMassExt hα hr (truncated2Infinite (latticeGraph d) Λ ⟨J,0,β⟩ x z)`.

This is the bridge identity needed to compare `pseudoMassFromParamsAtPair`
to `latticeMass`, which is defined as the supremum of validating
exponential decay rates of `truncated2Infinite`. (Step 117l support,
Issue #1645.) -/
theorem pseudoMassFromParamsAtPair_at_h_zero_eq {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z =
      pseudoMassExt hα hr
        (Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) x z) := by
  unfold pseudoMassFromParamsAtPair
  rw [Ambient.truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β x z]

/-- **At `J = 0` distinct pair, ferromagnetic, `0 < pseudoMassFromParamsAtPair`
iff `0 < h`**: under `Ferromagnetic ⟨0, h, β⟩` (which gives `0 ≤ h`, `0 < β`)
and `x ≠ z`, `0 < pseudoMassFromParamsAtPair ↔ 0 < h`. The forward
direction follows from `_at_J_zero_distinct_eq` + `pseudoMassExt_pos_iff`
(forces `tanh(β·h)^2 ∈ Ioo 0 2`, hence `tanh(β·h) ≠ 0`, hence `β·h ≠ 0`,
combined with `β > 0` gives `h ≠ 0`, then `h > 0` from `h ≥ 0`).
The reverse is `pseudoMassFromParamsAtPair_pos_at_J_zero` (already
proven). -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_pos_iff_h_pos
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    {x z : Fin d → ℤ} (hxz : x ≠ z) :
    0 < pseudoMassFromParamsAtPair hα hr d Λ
          (⟨0, h, β⟩ : IsingParams ℝ) x z ↔ 0 < h := by
  refine ⟨?_, fun hh => pseudoMassFromParamsAtPair_pos_at_J_zero hα hr d Λ hh hf.hβ hxz⟩
  intro hpos
  rw [pseudoMassFromParamsAtPair_at_J_zero_distinct_eq hα hr d Λ hf hxz] at hpos
  rw [pseudoMassExt_pos_iff hα hr] at hpos
  have htanh_sq_pos : 0 < Real.tanh (β * h) ^ 2 := hpos.1
  have htanh_ne : Real.tanh (β * h) ≠ 0 := by
    intro habs
    rw [habs] at htanh_sq_pos
    norm_num at htanh_sq_pos
  have hβh_ne : β * h ≠ 0 := by
    intro habs
    rw [habs, Real.tanh_zero] at htanh_ne
    exact htanh_ne rfl
  have hh_ne : h ≠ 0 := by
    intro h_eq
    rw [h_eq, mul_zero] at hβh_ne
    exact hβh_ne rfl
  exact lt_of_le_of_ne hf.hh (Ne.symm hh_ne)

/-- **At `J = 0` distinct pair, ferromagnetic, `pseudoMassFromParamsAtPair = 0`
iff `h = 0`**: contrapositive of `_at_J_zero_distinct_pos_iff_h_pos`,
using non-negativity to flip the strict iff. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_eq_zero_iff_h_zero
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    {x z : Fin d → ℤ} (hxz : x ≠ z) :
    pseudoMassFromParamsAtPair hα hr d Λ
        (⟨0, h, β⟩ : IsingParams ℝ) x z = 0 ↔ h = 0 := by
  have hh_nonneg : 0 ≤ h := hf.hh
  have hpm_nonneg := pseudoMassFromParamsAtPair_nonneg hα hr d Λ
                        (⟨0, h, β⟩ : IsingParams ℝ) x z
  constructor
  · intro h_eq
    by_contra h_ne
    have hh_pos : 0 < h := lt_of_le_of_ne hh_nonneg (Ne.symm h_ne)
    have hpm_pos : 0 < pseudoMassFromParamsAtPair hα hr d Λ
                          (⟨0, h, β⟩ : IsingParams ℝ) x z :=
      (pseudoMassFromParamsAtPair_at_J_zero_distinct_pos_iff_h_pos
        hα hr d Λ hf hxz).mpr hh_pos
    linarith
  · intro hh_eq
    by_contra h_pm_ne
    have hpm_pos : 0 < pseudoMassFromParamsAtPair hα hr d Λ
                          (⟨0, h, β⟩ : IsingParams ℝ) x z :=
      lt_of_le_of_ne hpm_nonneg (Ne.symm h_pm_ne)
    have hh_pos : 0 < h :=
      (pseudoMassFromParamsAtPair_at_J_zero_distinct_pos_iff_h_pos
        hα hr d Λ hf hxz).mp hpm_pos
    linarith

/-- **At `J = 0` for distinct pair, `pseudoMassFromParamsAtPair` depends
only on the product `β·h`**: for any two ferromagnetic params
`⟨0, h₁, β₁⟩` and `⟨0, h₂, β₂⟩` with `β₁·h₁ = β₂·h₂`, the bridge values
agree. Direct corollary of `pseudoMassFromParamsAtPair_at_J_zero_distinct_eq`
which gives `pseudoMassExt(tanh(β·h)^2)` — only the product enters
the right-hand side. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_eq_of_product_eq
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h₁ β₁ h₂ β₂ : ℝ}
    (hf₁ : Ferromagnetic (⟨(0 : ℝ), h₁, β₁⟩ : IsingParams ℝ))
    (hf₂ : Ferromagnetic (⟨(0 : ℝ), h₂, β₂⟩ : IsingParams ℝ))
    (hprod : β₁ * h₁ = β₂ * h₂)
    {x z : Fin d → ℤ} (hxz : x ≠ z) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h₁, β₁⟩ : IsingParams ℝ) x z =
      pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h₂, β₂⟩ : IsingParams ℝ) x z := by
  rw [pseudoMassFromParamsAtPair_at_J_zero_distinct_eq hα hr d Λ hf₁ hxz,
      pseudoMassFromParamsAtPair_at_J_zero_distinct_eq hα hr d Λ hf₂ hxz,
      hprod]

/-- **`pseudoMassFromParamsAtPair` strictly anti in `h` at `J = 0`** for
distinct pair, β > 0, h > 0: `tanh(β·h)^2` increases (in `Ioo 0 1 ⊂ Ioo 0 2`)
as h increases (β > 0 fixed), and `pseudoMassExt` is strictly antitone
on `Ioo 0 2`. Companion to `_strictAntiOn_beta_at_J_zero` (β-direction
analogue, PR #1668). -/
theorem pseudoMassFromParamsAtPair_strictAntiOn_h_at_J_zero
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {β : ℝ} (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    StrictAntiOn (fun h =>
        pseudoMassFromParamsAtPair hα hr d Λ
          (⟨0, h, β⟩ : IsingParams ℝ) x z) (Set.Ioi 0) := by
  intro h₁ hh₁ h₂ hh₂ hlt
  simp only [Set.mem_Ioi] at hh₁ hh₂
  have hf₁ : Ferromagnetic (⟨(0 : ℝ), h₁, β⟩ : IsingParams ℝ) :=
    ⟨le_refl 0, hh₁.le, hβ⟩
  have hf₂ : Ferromagnetic (⟨(0 : ℝ), h₂, β⟩ : IsingParams ℝ) :=
    ⟨le_refl 0, hh₂.le, hβ⟩
  change pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h₂, β⟩ : IsingParams ℝ) x z
        < pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h₁, β⟩ : IsingParams ℝ) x z
  rw [pseudoMassFromParamsAtPair_at_J_zero_distinct_eq hα hr d Λ hf₁ hxz,
      pseudoMassFromParamsAtPair_at_J_zero_distinct_eq hα hr d Λ hf₂ hxz]
  have htanh_pos₁ : 0 < Real.tanh (β * h₁) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (mul_pos hβ hh₁)) (Real.cosh_pos _)
  have htanh_pos₂ : 0 < Real.tanh (β * h₂) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (mul_pos hβ hh₂)) (Real.cosh_pos _)
  have htanh_mono : Real.tanh (β * h₁) < Real.tanh (β * h₂) :=
    Real.tanh_strictMono (mul_lt_mul_of_pos_left hlt hβ)
  have hsq_lt : Real.tanh (β * h₁) ^ 2 < Real.tanh (β * h₂) ^ 2 := by
    have h1 : Real.tanh (β * h₁) ^ 2 = Real.tanh (β * h₁) * Real.tanh (β * h₁) := sq _
    have h2 : Real.tanh (β * h₂) ^ 2 = Real.tanh (β * h₂) * Real.tanh (β * h₂) := sq _
    rw [h1, h2]
    exact mul_lt_mul' htanh_mono.le htanh_mono htanh_pos₁.le htanh_pos₂
  have hmem₁ : Real.tanh (β * h₁) ^ 2 ∈ Set.Ioo (0 : ℝ) 2 := by
    refine ⟨by positivity, ?_⟩
    have habs : |Real.tanh (β * h₁)| < 1 := Real.abs_tanh_lt_one _
    have h1 : -1 < Real.tanh (β * h₁) := neg_lt_of_abs_lt habs
    have h2 : Real.tanh (β * h₁) < 1 := lt_of_abs_lt habs
    nlinarith
  have hmem₂ : Real.tanh (β * h₂) ^ 2 ∈ Set.Ioo (0 : ℝ) 2 := by
    refine ⟨by positivity, ?_⟩
    have habs : |Real.tanh (β * h₂)| < 1 := Real.abs_tanh_lt_one _
    have h1 : -1 < Real.tanh (β * h₂) := neg_lt_of_abs_lt habs
    have h2 : Real.tanh (β * h₂) < 1 := lt_of_abs_lt habs
    nlinarith
  exact pseudoMassExt_strictAntiOn hα hr hmem₁ hmem₂ hsq_lt

/-- **`pseudoMassFromParamsAtPair` at `J = 0, h = 0` distinct pair = 0**:
combining `pseudoMassFromParamsAtPair_at_h_zero_eq` with
`Ambient.truncated2Infinite_J_zero_of_ne` (which gives 0 for distinct
pair under ferromagnetic, J = 0). Direct corollary at the `J = h = 0`
trivial slice. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_h_zero_eq_zero {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {β : ℝ} (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨0, 0, β⟩ : IsingParams ℝ) x z = 0 := by
  rw [pseudoMassFromParamsAtPair_at_h_zero_eq hα hr d Λ 0 β x z]
  have hf : Ferromagnetic (⟨(0 : ℝ), 0, β⟩ : IsingParams ℝ) :=
    ⟨le_refl 0, le_refl 0, hβ⟩
  rw [Ambient.truncated2Infinite_J_zero_of_ne (IsingModel.latticeGraph d) Λ 0 β hf hxz]
  apply pseudoMassExt_of_not_mem
  intro hmem
  exact lt_irrefl 0 hmem.1

/-- **`pseudoMassFromParamsAtPair > 0 at `h = 0` ↔ `0 < truncated2Infinite`**:
under ferromagnetic params, since `truncated2Infinite ∈ [0, 1] ⊂ [0, 2)`
(`truncated2Infinite_nonneg` + `truncated2Infinite_le_one`), the
`Ioo 0 2` membership of truncated2 is equivalent to strict positivity.
Combined with `pseudoMassFromParamsAtPair_at_h_zero_eq` and
`pseudoMassExt_pos_iff` to give the iff in terms of truncated2. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_pos_iff {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (x z : Fin d → ℤ) :
    0 < pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z ↔
    0 < Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) x z := by
  rw [pseudoMassFromParamsAtPair_at_h_zero_eq hα hr d Λ J β x z]
  rw [pseudoMassExt_pos_iff hα hr]
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ, le_refl 0, hβ⟩
  have hnonneg : 0 ≤ Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                        (⟨J, 0, β⟩ : IsingParams ℝ) x z :=
    Ambient.truncated2Infinite_nonneg (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) hf x z
  have hle : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) x z ≤ 1 :=
    Ambient.truncated2Infinite_le_one (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) hf x z
  refine ⟨fun h => h.1, fun h => ⟨h, by linarith⟩⟩

/-- **`pseudoMassFromParamsAtPair = 0 at `h = 0` ↔ `truncated2Infinite = 0`**:
contrapositive form of `_at_h_zero_pos_iff` under non-negativity of
truncated2 (which holds in the ferromagnetic regime). -/
theorem pseudoMassFromParamsAtPair_at_h_zero_eq_zero_iff {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (x z : Fin d → ℤ) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z = 0 ↔
    Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) x z = 0 := by
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ, le_refl 0, hβ⟩
  have hnonneg : 0 ≤ Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                        (⟨J, 0, β⟩ : IsingParams ℝ) x z :=
    Ambient.truncated2Infinite_nonneg (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) hf x z
  have hpm_nonneg : 0 ≤ pseudoMassFromParamsAtPair hα hr d Λ
                          (⟨J, 0, β⟩ : IsingParams ℝ) x z :=
    pseudoMassFromParamsAtPair_nonneg hα hr d Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) x z
  constructor
  · intro hzero
    by_contra h_t_ne
    have h_t_pos : 0 < Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                          (⟨J, 0, β⟩ : IsingParams ℝ) x z :=
      lt_of_le_of_ne hnonneg (Ne.symm h_t_ne)
    have hpos : 0 < pseudoMassFromParamsAtPair hα hr d Λ
                      (⟨J, 0, β⟩ : IsingParams ℝ) x z :=
      (pseudoMassFromParamsAtPair_at_h_zero_pos_iff hα hr d Λ hJ hβ x z).mpr h_t_pos
    linarith
  · intro hzero
    by_contra h_pm_ne
    have h_pm_pos : 0 < pseudoMassFromParamsAtPair hα hr d Λ
                          (⟨J, 0, β⟩ : IsingParams ℝ) x z :=
      lt_of_le_of_ne hpm_nonneg (Ne.symm h_pm_ne)
    have h_t_pos : 0 < Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                          (⟨J, 0, β⟩ : IsingParams ℝ) x z :=
      (pseudoMassFromParamsAtPair_at_h_zero_pos_iff hα hr d Λ hJ hβ x z).mp h_pm_pos
    linarith

/-- **`pseudoMassFromParamsAtPair` upper-bounded by `pseudoMass` at a
positive correlation lower bound**: if `c_min ≤ correlationInfinite ...`
with `c_min ∈ Ioo 0 2`, then by anti-monotonicity, `pseudoMassFromParamsAtPair
≤ pseudoMass(c_min)`. (Requires correlation also in `Ioo 0 2`.) -/
theorem pseudoMassFromParamsAtPair_le_of_corr_ge {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (x z : Fin d → ℤ)
    {c_min : ℝ} (hc_min : c_min ∈ Set.Ioo (0 : ℝ) 2)
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z}
              ∈ Set.Ioo (0 : ℝ) 2)
    (hge : c_min ≤ Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z}) :
    pseudoMassFromParamsAtPair hα hr d Λ p x z ≤ pseudoMassExt hα hr c_min := by
  unfold pseudoMassFromParamsAtPair
  by_cases heq :
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z} = c_min
  · rw [heq]
  · have hlt : c_min <
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z} :=
      lt_of_le_of_ne hge (Ne.symm heq)
    exact le_of_lt
      (pseudoMassExt_strictAntiOn hα hr hc_min hcorr hlt)

/-- **`pseudoMassFromParamsAtPair` lower-bounded by `pseudoMass` at a
correlation upper bound**: if `correlationInfinite ... ≤ c_max` with
`c_max ∈ Ioo 0 2`, then by anti-monotonicity, `pseudoMassExt c_max ≤
pseudoMassFromParamsAtPair`. -/
theorem pseudoMassFromParamsAtPair_ge_of_corr_le {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (x z : Fin d → ℤ)
    {c_max : ℝ} (hc_max : c_max ∈ Set.Ioo (0 : ℝ) 2)
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z}
              ∈ Set.Ioo (0 : ℝ) 2)
    (hle : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z}
              ≤ c_max) :
    pseudoMassExt hα hr c_max ≤ pseudoMassFromParamsAtPair hα hr d Λ p x z := by
  unfold pseudoMassFromParamsAtPair
  by_cases heq :
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z} = c_max
  · rw [heq]
  · have hlt :
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z} <
          c_max := lt_of_le_of_ne hle heq
    exact le_of_lt
      (pseudoMassExt_strictAntiOn hα hr hcorr hc_max hlt)

/-- **`pseudoMassFromParamsAtPair` strictly anti in β at `J = 0`** for
distinct pair, `h > 0`, β > 0: as β increases, `tanh(βh)^2` increases
(remaining in `Ioo 0 1 ⊂ Ioo 0 2`), and `pseudoMass` is strictly
antitone in its correlation argument. -/
theorem pseudoMassFromParamsAtPair_strictAntiOn_beta_at_J_zero
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h : ℝ} (hh : 0 < h) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    StrictAntiOn (fun β =>
        pseudoMassFromParamsAtPair hα hr d Λ
          (⟨0, h, β⟩ : IsingParams ℝ) x z) (Set.Ioi 0) := by
  intro β₁ hβ₁ β₂ hβ₂ hlt
  simp only [Set.mem_Ioi] at hβ₁ hβ₂
  have hf₁ : Ferromagnetic (⟨(0 : ℝ), h, β₁⟩ : IsingParams ℝ) :=
    ⟨le_refl 0, hh.le, hβ₁⟩
  have hf₂ : Ferromagnetic (⟨(0 : ℝ), h, β₂⟩ : IsingParams ℝ) :=
    ⟨le_refl 0, hh.le, hβ₂⟩
  change pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h, β₂⟩ : IsingParams ℝ) x z
        < pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h, β₁⟩ : IsingParams ℝ) x z
  rw [pseudoMassFromParamsAtPair_at_J_zero_distinct_eq hα hr d Λ hf₁ hxz,
      pseudoMassFromParamsAtPair_at_J_zero_distinct_eq hα hr d Λ hf₂ hxz]
  have htanh_pos₁ : 0 < Real.tanh (β₁ * h) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (mul_pos hβ₁ hh)) (Real.cosh_pos _)
  have htanh_pos₂ : 0 < Real.tanh (β₂ * h) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (mul_pos hβ₂ hh)) (Real.cosh_pos _)
  have htanh_mono : Real.tanh (β₁ * h) < Real.tanh (β₂ * h) :=
    Real.tanh_strictMono (mul_lt_mul_of_pos_right hlt hh)
  have hsq_lt : Real.tanh (β₁ * h) ^ 2 < Real.tanh (β₂ * h) ^ 2 := by
    have h1 : Real.tanh (β₁ * h) ^ 2 = Real.tanh (β₁ * h) * Real.tanh (β₁ * h) := sq _
    have h2 : Real.tanh (β₂ * h) ^ 2 = Real.tanh (β₂ * h) * Real.tanh (β₂ * h) := sq _
    rw [h1, h2]
    exact mul_lt_mul' htanh_mono.le htanh_mono htanh_pos₁.le htanh_pos₂
  have hmem₁ : Real.tanh (β₁ * h) ^ 2 ∈ Set.Ioo (0 : ℝ) 2 := by
    refine ⟨by positivity, ?_⟩
    have habs : |Real.tanh (β₁ * h)| < 1 := Real.abs_tanh_lt_one _
    have h1 : -1 < Real.tanh (β₁ * h) := neg_lt_of_abs_lt habs
    have h2 : Real.tanh (β₁ * h) < 1 := lt_of_abs_lt habs
    nlinarith
  have hmem₂ : Real.tanh (β₂ * h) ^ 2 ∈ Set.Ioo (0 : ℝ) 2 := by
    refine ⟨by positivity, ?_⟩
    have habs : |Real.tanh (β₂ * h)| < 1 := Real.abs_tanh_lt_one _
    have h1 : -1 < Real.tanh (β₂ * h) := neg_lt_of_abs_lt habs
    have h2 : Real.tanh (β₂ * h) < 1 := lt_of_abs_lt habs
    nlinarith
  exact pseudoMassExt_strictAntiOn hα hr hmem₁ hmem₂ hsq_lt

/-- **`pseudoMassFromParamsAtPair` independence of exhaustion for
ferromagnetic params**: `correlationInfinite` is exhaustion-independent
under ferromagnetic hypothesis, hence so is the bridge. -/
theorem pseudoMassFromParamsAtPair_indep_exhaustion {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ Λ' : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ'.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (x z : Fin d → ℤ) :
    pseudoMassFromParamsAtPair hα hr d Λ p x z =
      pseudoMassFromParamsAtPair hα hr d Λ' p x z := by
  unfold pseudoMassFromParamsAtPair
  congr 1
  exact Ambient.correlationInfinite_indep_exhaustion
    (IsingModel.latticeGraph d) Λ Λ' p hf {x, z}

/-- **`pseudoMassFromParamsAtPair` h-symmetry under `h → -h` for distinct
pairs**: `|{x, z}| = 2` is even, so `correlationInfinite` is unchanged
under `h ↦ -h`, hence the bridge is too. -/
theorem pseudoMassFromParamsAtPair_neg_h_distinct {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J h β : ℝ) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, -h, β⟩ : IsingParams ℝ) x z =
      pseudoMassFromParamsAtPair hα hr d Λ (⟨J, h, β⟩ : IsingParams ℝ) x z := by
  unfold pseudoMassFromParamsAtPair
  congr 1
  have heven : Even (({x, z} : Finset (Fin d → ℤ)).card) := by
    rw [Finset.card_pair hxz]
    decide
  exact Ambient.correlationInfinite_neg_h_of_even_card
    (IsingModel.latticeGraph d) Λ J h β {x, z} heven

/-- **`pseudoMassFromParamsAtPair = 0 ↔ correlation ∉ Ioo 0 2`**: lifted from
`pseudoMassExt_eq_zero_iff`. -/
theorem pseudoMassFromParamsAtPair_eq_zero_iff {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (x z : Fin d → ℤ) :
    pseudoMassFromParamsAtPair hα hr d Λ p x z = 0 ↔
    Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z}
        ∉ Set.Ioo (0 : ℝ) 2 := by
  unfold pseudoMassFromParamsAtPair
  exact pseudoMassExt_eq_zero_iff hα hr _

/-- **`pseudoMassFromParamsAtPair > 0 ↔ correlation ∈ Ioo 0 2`**: lifted from
`pseudoMassExt_pos_iff`. -/
theorem pseudoMassFromParamsAtPair_pos_iff {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (x z : Fin d → ℤ) :
    0 < pseudoMassFromParamsAtPair hα hr d Λ p x z ↔
    Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z}
        ∈ Set.Ioo (0 : ℝ) 2 := by
  unfold pseudoMassFromParamsAtPair
  exact pseudoMassExt_pos_iff hα hr _

/-- **`pseudoMassFromParamsAtPair` sandwich**: if `c_min ≤ correlation ≤ c_max`
all in `Ioo 0 2`, then `pseudoMassExt c_max ≤ pseudoMassFromParamsAtPair ≤ pseudoMassExt c_min`.

This packages `_le_of_corr_ge` and `_ge_of_corr_le` into a single sandwich
inequality, useful for the §17.5 Lemma 17.5.2 capstone. -/
theorem pseudoMassFromParamsAtPair_sandwich_of_corr_mem {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (x z : Fin d → ℤ)
    {c_min c_max : ℝ}
    (hc_min : c_min ∈ Set.Ioo (0 : ℝ) 2)
    (hc_max : c_max ∈ Set.Ioo (0 : ℝ) 2)
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z}
              ∈ Set.Ioo (0 : ℝ) 2)
    (hge : c_min ≤ Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z})
    (hle : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z}
              ≤ c_max) :
    pseudoMassExt hα hr c_max ≤ pseudoMassFromParamsAtPair hα hr d Λ p x z ∧
    pseudoMassFromParamsAtPair hα hr d Λ p x z ≤ pseudoMassExt hα hr c_min :=
  ⟨pseudoMassFromParamsAtPair_ge_of_corr_le hα hr d Λ p x z hc_max hcorr hle,
   pseudoMassFromParamsAtPair_le_of_corr_ge hα hr d Λ p x z hc_min hcorr hge⟩

/-! ### `h = 0` specialisations using `truncated2Infinite`

At zero external field, `correlationInfinite ⟨J, 0, β⟩ {x, z} = truncated2Infinite ⟨J, 0, β⟩ x z`
(spin-flip Z₂ symmetry forces the singleton magnetisations to vanish), so the
`*_of_corr_*` family of bounds for `pseudoMassFromParamsAtPair` translates to
the corresponding `*_of_truncated2_*` form in terms of the function
`latticeMass` is actually defined against.
-/

/-- **At `h = 0`, `pseudoMassFromParamsAtPair ≤ pseudoMassExt(c_min)` from
`c_min ≤ truncated2`**: h = 0 specialisation of `_le_of_corr_ge` using the
identity `correlationInfinite ⟨J, 0, β⟩ {x,z} = truncated2Infinite ⟨J,0,β⟩ x z`. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_le_of_truncated2_ge {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    {c_min : ℝ} (hc_min : c_min ∈ Set.Ioo (0 : ℝ) 2)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2)
    (hge : c_min ≤ Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) x z) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z ≤
      pseudoMassExt hα hr c_min := by
  have hbridge := Ambient.truncated2Infinite_h_zero
    (IsingModel.latticeGraph d) Λ J β x z
  rw [hbridge] at htrunc hge
  exact pseudoMassFromParamsAtPair_le_of_corr_ge hα hr d Λ
    (⟨J, 0, β⟩ : IsingParams ℝ) x z hc_min htrunc hge

/-- **At `h = 0`, `pseudoMassExt(c_max) ≤ pseudoMassFromParamsAtPair` from
`truncated2 ≤ c_max`**: h = 0 specialisation of `_ge_of_corr_le`. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_ge_of_truncated2_le {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    {c_max : ℝ} (hc_max : c_max ∈ Set.Ioo (0 : ℝ) 2)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2)
    (hle : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) x z ≤ c_max) :
    pseudoMassExt hα hr c_max ≤
      pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z := by
  have hbridge := Ambient.truncated2Infinite_h_zero
    (IsingModel.latticeGraph d) Λ J β x z
  rw [hbridge] at htrunc hle
  exact pseudoMassFromParamsAtPair_ge_of_corr_le hα hr d Λ
    (⟨J, 0, β⟩ : IsingParams ℝ) x z hc_max htrunc hle

/-- **At `h = 0`, `pseudoMassFromParamsAtPair` sandwich** combining
`_le_of_truncated2_ge` and `_ge_of_truncated2_le`: if
`c_min ≤ truncated2 ≤ c_max` with all values in `Ioo 0 2`, then
`pseudoMassExt(c_max) ≤ pseudoMassFromParamsAtPair ≤ pseudoMassExt(c_min)`. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_sandwich_of_truncated2_mem
    {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    {c_min c_max : ℝ}
    (hc_min : c_min ∈ Set.Ioo (0 : ℝ) 2)
    (hc_max : c_max ∈ Set.Ioo (0 : ℝ) 2)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2)
    (hge : c_min ≤ Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) x z)
    (hle : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) x z ≤ c_max) :
    pseudoMassExt hα hr c_max ≤
      pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z ∧
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z ≤
      pseudoMassExt hα hr c_min :=
  ⟨pseudoMassFromParamsAtPair_at_h_zero_ge_of_truncated2_le
      hα hr d Λ J β x z hc_max htrunc hle,
   pseudoMassFromParamsAtPair_at_h_zero_le_of_truncated2_ge
      hα hr d Λ J β x z hc_min htrunc hge⟩

/-- **At `h = 0`, when `truncated2Infinite ∈ Ioo 0 2`, the bridge equals
the underlying `pseudoMass`** (not the totalised `pseudoMassExt`):
combining `pseudoMassFromParamsAtPair_at_h_zero_eq` (PR #1669) with
`pseudoMassExt_of_mem`. This gives access to the implicit-function-theorem
derivative API of `pseudoMass` (`HasStrictDerivAt`, etc.) when reasoning
about the bridge in the high-temperature ferromagnetic regime where
truncated2 is positive but bounded by 1. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_eq_pseudoMass_of_truncated2_mem
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z =
      pseudoMass hα hr htrunc := by
  rw [pseudoMassFromParamsAtPair_at_h_zero_eq hα hr d Λ J β x z]
  exact pseudoMassExt_of_mem hα hr htrunc

/-- **At `h = 0`, the bridge as a `pseudoMass` upper bound from a
`truncated2` lower bound**: combining `_at_h_zero_le_of_truncated2_ge`
(PR #1671, gives `≤ pseudoMassExt(c_min)`) with `pseudoMassExt_of_mem`
(reduces to `pseudoMass(c_min)` when `c_min ∈ Ioo 0 2`). Useful for
deriving the §17.5 lower-bound `pseudoMass(...) ≤ latticeMass(...)`
direction. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_le_pseudoMass_of_truncated2_ge
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    {c_min : ℝ} (hc_min : c_min ∈ Set.Ioo (0 : ℝ) 2)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2)
    (hge : c_min ≤ Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) x z) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z ≤
      pseudoMass hα hr hc_min := by
  have hbound := pseudoMassFromParamsAtPair_at_h_zero_le_of_truncated2_ge
                    hα hr d Λ J β x z hc_min htrunc hge
  rwa [pseudoMassExt_of_mem hα hr hc_min] at hbound

/-- **At `h = 0`, the bridge as a `pseudoMass` lower bound from a
`truncated2` upper bound**: combining `_at_h_zero_ge_of_truncated2_le`
with `pseudoMassExt_of_mem`. Companion to
`_at_h_zero_le_pseudoMass_of_truncated2_ge`. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_ge_pseudoMass_of_truncated2_le
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    {c_max : ℝ} (hc_max : c_max ∈ Set.Ioo (0 : ℝ) 2)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2)
    (hle : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) x z ≤ c_max) :
    pseudoMass hα hr hc_max ≤
      pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z := by
  have hbound := pseudoMassFromParamsAtPair_at_h_zero_ge_of_truncated2_le
                    hα hr d Λ J β x z hc_max htrunc hle
  rwa [pseudoMassExt_of_mem hα hr hc_max] at hbound

/-- **At `h = 0`, `pseudoMassFromParamsAtPair > 0` from `truncated2 ∈ Ioo 0 2`**:
direct corollary of `_at_h_zero_eq_pseudoMass_of_truncated2_mem` (PR #1672)
+ `pseudoMass_pos` (PR #928 Step 117g). When the truncated 2-point function
falls in the regime `(0, 2)`, the bridge is strictly positive — the
canonical "non-vanishing" condition for `pseudoMassFromParamsAtPair`
expressed in terms of the function `latticeMass` is defined against. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_pos_of_truncated2_mem
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2) :
    0 < pseudoMassFromParamsAtPair hα hr d Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) x z := by
  rw [pseudoMassFromParamsAtPair_at_h_zero_eq_pseudoMass_of_truncated2_mem
        hα hr d Λ J β x z htrunc]
  exact pseudoMass_pos hα hr htrunc

/-- **At `h = 0`, full sandwich `pseudoMass(c_max) ≤
pseudoMassFromParamsAtPair ≤ pseudoMass(c_min)`** under
`c_min ≤ truncated2 ≤ c_max` with all values in `Ioo 0 2`. Combines
`_at_h_zero_le_pseudoMass_of_truncated2_ge` and
`_at_h_zero_ge_pseudoMass_of_truncated2_le` (PR #1677) into a single
sandwich in terms of the typed `pseudoMass`. This is the canonical
sandwich form for §17.5 Lemma 17.5.2: a uniform-in-Λ exponential
decay bound on `truncated2Infinite` plus the Lipschitz capstone
(`pseudoMass_pow_succ_lipschitz`) on the typed `pseudoMass` would
combine into the sandwich `m⁻ ≤ m ≤ const · m⁻`. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_sandwich_pseudoMass
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    {c_min c_max : ℝ}
    (hc_min : c_min ∈ Set.Ioo (0 : ℝ) 2)
    (hc_max : c_max ∈ Set.Ioo (0 : ℝ) 2)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2)
    (hge : c_min ≤ Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) x z)
    (hle : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) x z ≤ c_max) :
    pseudoMass hα hr hc_max ≤
      pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z ∧
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z ≤
      pseudoMass hα hr hc_min :=
  ⟨pseudoMassFromParamsAtPair_at_h_zero_ge_pseudoMass_of_truncated2_le
      hα hr d Λ J β x z hc_max htrunc hle,
   pseudoMassFromParamsAtPair_at_h_zero_le_pseudoMass_of_truncated2_ge
      hα hr d Λ J β x z hc_min htrunc hge⟩

/-- **At `J = 0` distinct pair, `pseudoMassFromParamsAtPair` equals
the typed `pseudoMass(tanh(β·h)^2)`** when `0 < h` and `0 < β`
(ferromagnetic with strict positivity): `tanh(β·h) ∈ (0, 1)`, so
`tanh(β·h)^2 ∈ Ioo 0 1 ⊂ Ioo 0 2`, hence the totalisation collapses
to the typed `pseudoMass`. Combines `_at_J_zero_distinct_eq` (gives
`pseudoMassExt(tanh(β·h)^2)`) with `pseudoMassExt_of_mem`. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_eq_pseudoMass
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    ∃ hmem : Real.tanh (β * h) ^ 2 ∈ Set.Ioo (0 : ℝ) 2,
      pseudoMassFromParamsAtPair hα hr d Λ
          (⟨0, h, β⟩ : IsingParams ℝ) x z = pseudoMass hα hr hmem := by
  have hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ) :=
    ⟨le_refl 0, hh.le, hβ⟩
  have habs : |Real.tanh (β * h)| < 1 := Real.abs_tanh_lt_one _
  have hlt_one : Real.tanh (β * h) < 1 := lt_of_abs_lt habs
  have hgt_neg_one : -1 < Real.tanh (β * h) := neg_lt_of_abs_lt habs
  have htanh_pos : 0 < Real.tanh (β * h) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (mul_pos hβ hh)) (Real.cosh_pos _)
  have hmem : Real.tanh (β * h) ^ 2 ∈ Set.Ioo (0 : ℝ) 2 := by
    refine ⟨by positivity, ?_⟩
    nlinarith
  refine ⟨hmem, ?_⟩
  rw [pseudoMassFromParamsAtPair_at_J_zero_distinct_eq hα hr d Λ hf hxz]
  exact pseudoMassExt_of_mem hα hr hmem

/-- **At `J = 0, h = 0` for ANY pair `(x, z)` (diag + distinct), the
bridge = 0**: combines `_diag_h_zero` (covers `x = z`, any J, β, h=0)
with `_at_J_zero_h_zero_eq_zero` (covers `x ≠ z` under `0 < β`).
At `J = h = 0`, the system is independent uniform spins for any β > 0,
so all 2-point correlations vanish identically. -/
theorem pseudoMassFromParamsAtPair_J_zero_h_zero_any_pair
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {β : ℝ} (hβ : 0 < β) (x z : Fin d → ℤ) :
    pseudoMassFromParamsAtPair hα hr d Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) x z = 0 := by
  by_cases hxz : x = z
  · subst hxz
    exact pseudoMassFromParamsAtPair_diag_h_zero hα hr d Λ 0 β x
  · exact pseudoMassFromParamsAtPair_at_J_zero_h_zero_eq_zero hα hr d Λ hβ hxz

/-- **At `J = 0` distinct pair, `pseudoMassFromParamsAtPair` is
`ContinuousAt` in `β` for `β > 0`** (with `h > 0` fixed): combines
`_at_J_zero_distinct_eq` (the bridge equals `pseudoMassExt(tanh(β·h)^2)`)
with `pseudoMassExt_tanh_sq_continuousAt_pos` (PR #1685). Useful for
showing the J=0 reference slice is continuously parametrised by β. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_continuousAt_beta_pos
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    ContinuousAt
      (fun b : ℝ => pseudoMassFromParamsAtPair hα hr d Λ
                      (⟨0, h, b⟩ : IsingParams ℝ) x z) β := by
  have hf_at : ∀ b > 0, Ferromagnetic (⟨(0 : ℝ), h, b⟩ : IsingParams ℝ) :=
    fun b hb => ⟨le_refl 0, hh.le, hb⟩
  -- Use `pseudoMassFromParamsAtPair_at_J_zero_distinct_eq` to rewrite as
  -- `pseudoMassExt(tanh(b·h)^2)`. The rewrite holds for ferromagnetic params,
  -- which requires `b > 0`. Use `Filter.EventuallyEq` on a neighborhood of β.
  have hβ_nhd : ∀ᶠ b in nhds β, 0 < b := by
    rw [Metric.eventually_nhds_iff]
    refine ⟨β / 2, by linarith, ?_⟩
    intros y hy
    rw [Real.dist_eq, abs_lt] at hy
    linarith
  have hEq : (fun b : ℝ => pseudoMassFromParamsAtPair hα hr d Λ
                              (⟨0, h, b⟩ : IsingParams ℝ) x z) =ᶠ[nhds β]
              (fun b : ℝ => pseudoMassExt hα hr (Real.tanh (b * h) ^ 2)) := by
    filter_upwards [hβ_nhd] with b hb
    exact pseudoMassFromParamsAtPair_at_J_zero_distinct_eq hα hr d Λ
            (hf_at b hb) hxz
  refine (ContinuousAt.congr ?_ hEq.symm)
  -- Continuity of `b ↦ pseudoMassExt(tanh(b·h)^2)` at β:
  -- Composition `(b ↦ b·h)` (continuous) then `pseudoMassExt(tanh(·)^2)`
  -- (continuous at β·h > 0 by PR #1685).
  have hβh_pos : 0 < β * h := mul_pos hβ hh
  have hmul : ContinuousAt (fun b : ℝ => b * h) β :=
    (continuous_id.mul continuous_const).continuousAt
  have houter : ContinuousAt
                  (fun s : ℝ => pseudoMassExt hα hr (Real.tanh s ^ 2)) (β * h) :=
    pseudoMassExt_tanh_sq_continuousAt_pos hα hr hβh_pos
  change ContinuousAt
    ((fun s : ℝ => pseudoMassExt hα hr (Real.tanh s ^ 2)) ∘ (fun b : ℝ => b * h)) β
  exact ContinuousAt.comp houter hmul

/-- **At `J = 0` distinct pair, `pseudoMassFromParamsAtPair` is
`DifferentiableAt` in `β` for `β > 0`** (with `h > 0` fixed): same
proof structure as `_continuousAt_beta_pos` (PR #1686), substituting
`pseudoMassExt_tanh_sq_differentiableAt_pos` (PR #1685) for the
ContinuousAt version. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_differentiableAt_beta_pos
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    DifferentiableAt ℝ
      (fun b : ℝ => pseudoMassFromParamsAtPair hα hr d Λ
                      (⟨0, h, b⟩ : IsingParams ℝ) x z) β := by
  have hf_at : ∀ b > 0, Ferromagnetic (⟨(0 : ℝ), h, b⟩ : IsingParams ℝ) :=
    fun b hb => ⟨le_refl 0, hh.le, hb⟩
  have hβ_nhd : ∀ᶠ b in nhds β, 0 < b := by
    rw [Metric.eventually_nhds_iff]
    refine ⟨β / 2, by linarith, ?_⟩
    intros y hy
    rw [Real.dist_eq, abs_lt] at hy
    linarith
  have hEq : (fun b : ℝ => pseudoMassFromParamsAtPair hα hr d Λ
                              (⟨0, h, b⟩ : IsingParams ℝ) x z) =ᶠ[nhds β]
              (fun b : ℝ => pseudoMassExt hα hr (Real.tanh (b * h) ^ 2)) := by
    filter_upwards [hβ_nhd] with b hb
    exact pseudoMassFromParamsAtPair_at_J_zero_distinct_eq hα hr d Λ
            (hf_at b hb) hxz
  have hdiff_alt : DifferentiableAt ℝ
                    (fun b : ℝ => pseudoMassExt hα hr (Real.tanh (b * h) ^ 2)) β := by
    have hβh_pos : 0 < β * h := mul_pos hβ hh
    have hmul : DifferentiableAt ℝ (fun b : ℝ => b * h) β :=
      (differentiable_id.mul (differentiable_const _)).differentiableAt
    have houter : DifferentiableAt ℝ
                    (fun s : ℝ => pseudoMassExt hα hr (Real.tanh s ^ 2)) (β * h) :=
      pseudoMassExt_tanh_sq_differentiableAt_pos hα hr hβh_pos
    change DifferentiableAt ℝ
      ((fun s : ℝ => pseudoMassExt hα hr (Real.tanh s ^ 2)) ∘ (fun b : ℝ => b * h)) β
    exact DifferentiableAt.comp β houter hmul
  exact hdiff_alt.congr_of_eventuallyEq hEq

/-- **At `J = 0` distinct pair, `pseudoMassFromParamsAtPair` is
`DifferentiableAt` in `h` for `h > 0`** (with `β > 0` fixed):
h-direction analogue of `_differentiableAt_beta_pos`. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_differentiableAt_h_pos
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    DifferentiableAt ℝ
      (fun y : ℝ => pseudoMassFromParamsAtPair hα hr d Λ
                      (⟨0, y, β⟩ : IsingParams ℝ) x z) h := by
  have hf_at : ∀ y > 0, Ferromagnetic (⟨(0 : ℝ), y, β⟩ : IsingParams ℝ) :=
    fun y hy => ⟨le_refl 0, hy.le, hβ⟩
  have hh_nhd : ∀ᶠ y in nhds h, 0 < y := by
    rw [Metric.eventually_nhds_iff]
    refine ⟨h / 2, by linarith, ?_⟩
    intros y hy
    rw [Real.dist_eq, abs_lt] at hy
    linarith
  have hEq : (fun y : ℝ => pseudoMassFromParamsAtPair hα hr d Λ
                              (⟨0, y, β⟩ : IsingParams ℝ) x z) =ᶠ[nhds h]
              (fun y : ℝ => pseudoMassExt hα hr (Real.tanh (β * y) ^ 2)) := by
    filter_upwards [hh_nhd] with y hy
    exact pseudoMassFromParamsAtPair_at_J_zero_distinct_eq hα hr d Λ
            (hf_at y hy) hxz
  have hdiff_alt : DifferentiableAt ℝ
                    (fun y : ℝ => pseudoMassExt hα hr (Real.tanh (β * y) ^ 2)) h := by
    have hβh_pos : 0 < β * h := mul_pos hβ hh
    have hmul : DifferentiableAt ℝ (fun y : ℝ => β * y) h :=
      ((differentiable_const _).mul differentiable_id).differentiableAt
    have houter : DifferentiableAt ℝ
                    (fun s : ℝ => pseudoMassExt hα hr (Real.tanh s ^ 2)) (β * h) :=
      pseudoMassExt_tanh_sq_differentiableAt_pos hα hr hβh_pos
    change DifferentiableAt ℝ
      ((fun s : ℝ => pseudoMassExt hα hr (Real.tanh s ^ 2)) ∘ (fun y : ℝ => β * y)) h
    exact DifferentiableAt.comp h houter hmul
  exact hdiff_alt.congr_of_eventuallyEq hEq

/-- **At `J = 0` distinct pair, `pseudoMassFromParamsAtPair` is
`ContinuousAt` in `h` for `h > 0`** (with `β > 0` fixed): h-direction
analogue of `_at_J_zero_distinct_continuousAt_beta_pos`. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_continuousAt_h_pos
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    ContinuousAt
      (fun y : ℝ => pseudoMassFromParamsAtPair hα hr d Λ
                      (⟨0, y, β⟩ : IsingParams ℝ) x z) h := by
  have hf_at : ∀ y > 0, Ferromagnetic (⟨(0 : ℝ), y, β⟩ : IsingParams ℝ) :=
    fun y hy => ⟨le_refl 0, hy.le, hβ⟩
  have hh_nhd : ∀ᶠ y in nhds h, 0 < y := by
    rw [Metric.eventually_nhds_iff]
    refine ⟨h / 2, by linarith, ?_⟩
    intros y hy
    rw [Real.dist_eq, abs_lt] at hy
    linarith
  have hEq : (fun y : ℝ => pseudoMassFromParamsAtPair hα hr d Λ
                              (⟨0, y, β⟩ : IsingParams ℝ) x z) =ᶠ[nhds h]
              (fun y : ℝ => pseudoMassExt hα hr (Real.tanh (β * y) ^ 2)) := by
    filter_upwards [hh_nhd] with y hy
    exact pseudoMassFromParamsAtPair_at_J_zero_distinct_eq hα hr d Λ
            (hf_at y hy) hxz
  refine (ContinuousAt.congr ?_ hEq.symm)
  have hβh_pos : 0 < β * h := mul_pos hβ hh
  have hmul : ContinuousAt (fun y : ℝ => β * y) h :=
    (continuous_const.mul continuous_id).continuousAt
  have houter : ContinuousAt
                  (fun s : ℝ => pseudoMassExt hα hr (Real.tanh s ^ 2)) (β * h) :=
    pseudoMassExt_tanh_sq_continuousAt_pos hα hr hβh_pos
  change ContinuousAt
    ((fun s : ℝ => pseudoMassExt hα hr (Real.tanh s ^ 2)) ∘ (fun y : ℝ => β * y)) h
  exact ContinuousAt.comp houter hmul

/-- **At `J = 0` distinct pair, `pseudoMassFromParamsAtPair` is
`ContinuousOn (Ioi 0)` in `β`**: lift `_continuousAt_beta_pos` to a
`ContinuousOn` over the open positive real interval. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_continuousOn_beta_Ioi
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h : ℝ} (hh : 0 < h) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    ContinuousOn
      (fun b : ℝ => pseudoMassFromParamsAtPair hα hr d Λ
                      (⟨0, h, b⟩ : IsingParams ℝ) x z) (Set.Ioi 0) := by
  intro β hβ
  exact (pseudoMassFromParamsAtPair_at_J_zero_distinct_continuousAt_beta_pos
            hα hr d Λ hh hβ hxz).continuousWithinAt

/-- **At `J = 0` distinct pair, `pseudoMassFromParamsAtPair` is
`ContinuousOn (Ioi 0)` in `h`**: lift `_continuousAt_h_pos`. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_continuousOn_h_Ioi
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {β : ℝ} (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    ContinuousOn
      (fun y : ℝ => pseudoMassFromParamsAtPair hα hr d Λ
                      (⟨0, y, β⟩ : IsingParams ℝ) x z) (Set.Ioi 0) := by
  intro h hh
  exact (pseudoMassFromParamsAtPair_at_J_zero_distinct_continuousAt_h_pos
            hα hr d Λ hh hβ hxz).continuousWithinAt

/-- **At `J = 0` distinct pair, `pseudoMassFromParamsAtPair` is
`DifferentiableOn (Ioi 0)` in `β`**. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_differentiableOn_beta_Ioi
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h : ℝ} (hh : 0 < h) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    DifferentiableOn ℝ
      (fun b : ℝ => pseudoMassFromParamsAtPair hα hr d Λ
                      (⟨0, h, b⟩ : IsingParams ℝ) x z) (Set.Ioi 0) := by
  intro β hβ
  exact (pseudoMassFromParamsAtPair_at_J_zero_distinct_differentiableAt_beta_pos
            hα hr d Λ hh hβ hxz).differentiableWithinAt

/-- **At `J = 0` distinct pair, `pseudoMassFromParamsAtPair` is
`DifferentiableOn (Ioi 0)` in `h`**. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_differentiableOn_h_Ioi
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {β : ℝ} (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    DifferentiableOn ℝ
      (fun y : ℝ => pseudoMassFromParamsAtPair hα hr d Λ
                      (⟨0, y, β⟩ : IsingParams ℝ) x z) (Set.Ioi 0) := by
  intro h hh
  exact (pseudoMassFromParamsAtPair_at_J_zero_distinct_differentiableAt_h_pos
            hα hr d Λ hh hβ hxz).differentiableWithinAt

/-- **At `J = 0` distinct pair, `pseudoMassFromParamsAtPair` is jointly
`DifferentiableAt` in `(β, h)` for `β > 0, h > 0`**: composition of
`(β, h) ↦ β·h` (joint differentiable) with `pseudoMassExt(tanh(t)^2)`
differentiable at `β·h > 0` (PR #1685). -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_differentiableAt_betaH_pos
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    DifferentiableAt ℝ
      (fun p : ℝ × ℝ => pseudoMassFromParamsAtPair hα hr d Λ
                          (⟨0, p.2, p.1⟩ : IsingParams ℝ) x z) (β, h) := by
  have hf_at : ∀ p : ℝ × ℝ, 0 < p.1 → 0 < p.2 →
                  Ferromagnetic (⟨(0 : ℝ), p.2, p.1⟩ : IsingParams ℝ) :=
    fun p hp1 hp2 => ⟨le_refl 0, hp2.le, hp1⟩
  have hβ_nhd : ∀ᶠ p : ℝ × ℝ in nhds (β, h), 0 < p.1 ∧ 0 < p.2 := by
    have h1 : ∀ᶠ p : ℝ × ℝ in nhds (β, h), 0 < p.1 := by
      have hcont : ContinuousAt (fun p : ℝ × ℝ => p.1) (β, h) :=
        continuous_fst.continuousAt
      exact hcont.eventually_const_lt hβ
    have h2 : ∀ᶠ p : ℝ × ℝ in nhds (β, h), 0 < p.2 := by
      have hcont : ContinuousAt (fun p : ℝ × ℝ => p.2) (β, h) :=
        continuous_snd.continuousAt
      exact hcont.eventually_const_lt hh
    filter_upwards [h1, h2] with p hp1 hp2 using ⟨hp1, hp2⟩
  have hEq : (fun p : ℝ × ℝ => pseudoMassFromParamsAtPair hα hr d Λ
                                  (⟨0, p.2, p.1⟩ : IsingParams ℝ) x z) =ᶠ[nhds (β, h)]
              (fun p : ℝ × ℝ => pseudoMassExt hα hr (Real.tanh (p.1 * p.2) ^ 2)) := by
    filter_upwards [hβ_nhd] with p ⟨hp1, hp2⟩
    exact pseudoMassFromParamsAtPair_at_J_zero_distinct_eq hα hr d Λ
            (hf_at p hp1 hp2) hxz
  have hdiff_alt : DifferentiableAt ℝ
                    (fun p : ℝ × ℝ => pseudoMassExt hα hr
                      (Real.tanh (p.1 * p.2) ^ 2)) (β, h) := by
    have hβh_pos : 0 < β * h := mul_pos hβ hh
    have hmul : DifferentiableAt ℝ (fun p : ℝ × ℝ => p.1 * p.2) (β, h) :=
      (differentiable_fst.mul differentiable_snd).differentiableAt
    have houter : DifferentiableAt ℝ
                    (fun s : ℝ => pseudoMassExt hα hr (Real.tanh s ^ 2)) (β * h) :=
      pseudoMassExt_tanh_sq_differentiableAt_pos hα hr hβh_pos
    change DifferentiableAt ℝ
      ((fun s : ℝ => pseudoMassExt hα hr (Real.tanh s ^ 2)) ∘
        (fun p : ℝ × ℝ => p.1 * p.2)) (β, h)
    exact DifferentiableAt.comp (β, h) houter hmul
  exact hdiff_alt.congr_of_eventuallyEq hEq

/-- **At `J = 0` distinct pair, `pseudoMassFromParamsAtPair` is jointly
`ContinuousAt` in `(β, h)` for `β > 0, h > 0`**: composition of
`(β, h) ↦ β·h` (joint continuous) with `pseudoMassExt(tanh(t)^2)`
continuous at `β·h > 0` (PR #1685). -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_continuousAt_betaH_pos
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    ContinuousAt
      (fun p : ℝ × ℝ => pseudoMassFromParamsAtPair hα hr d Λ
                          (⟨0, p.2, p.1⟩ : IsingParams ℝ) x z) (β, h) := by
  have hf_at : ∀ p : ℝ × ℝ, 0 < p.1 → 0 < p.2 →
                  Ferromagnetic (⟨(0 : ℝ), p.2, p.1⟩ : IsingParams ℝ) :=
    fun p hp1 hp2 => ⟨le_refl 0, hp2.le, hp1⟩
  have hβ_nhd : ∀ᶠ p : ℝ × ℝ in nhds (β, h), 0 < p.1 ∧ 0 < p.2 := by
    have h1 : ∀ᶠ p : ℝ × ℝ in nhds (β, h), 0 < p.1 := by
      have hcont : ContinuousAt (fun p : ℝ × ℝ => p.1) (β, h) :=
        continuous_fst.continuousAt
      exact hcont.eventually_const_lt hβ
    have h2 : ∀ᶠ p : ℝ × ℝ in nhds (β, h), 0 < p.2 := by
      have hcont : ContinuousAt (fun p : ℝ × ℝ => p.2) (β, h) :=
        continuous_snd.continuousAt
      exact hcont.eventually_const_lt hh
    filter_upwards [h1, h2] with p hp1 hp2 using ⟨hp1, hp2⟩
  have hEq : (fun p : ℝ × ℝ => pseudoMassFromParamsAtPair hα hr d Λ
                                  (⟨0, p.2, p.1⟩ : IsingParams ℝ) x z) =ᶠ[nhds (β, h)]
              (fun p : ℝ × ℝ => pseudoMassExt hα hr (Real.tanh (p.1 * p.2) ^ 2)) := by
    filter_upwards [hβ_nhd] with p ⟨hp1, hp2⟩
    exact pseudoMassFromParamsAtPair_at_J_zero_distinct_eq hα hr d Λ
            (hf_at p hp1 hp2) hxz
  refine (ContinuousAt.congr ?_ hEq.symm)
  have hβh_pos : 0 < β * h := mul_pos hβ hh
  have hmul : ContinuousAt (fun p : ℝ × ℝ => p.1 * p.2) (β, h) :=
    (continuous_fst.mul continuous_snd).continuousAt
  have houter : ContinuousAt
                  (fun s : ℝ => pseudoMassExt hα hr (Real.tanh s ^ 2)) (β * h) :=
    pseudoMassExt_tanh_sq_continuousAt_pos hα hr hβh_pos
  change ContinuousAt
    ((fun s : ℝ => pseudoMassExt hα hr (Real.tanh s ^ 2)) ∘
      (fun p : ℝ × ℝ => p.1 * p.2)) (β, h)
  exact ContinuousAt.comp houter hmul

/-- **At `J = 0` distinct pair with `0 < h, 0 < β`,
`pseudoMassFromParamsAtPair < log(2/tanh(β·h)^2)/r`**: strict version of
`_le_log_two_div_tanh_sq` (PR #1708). Combines
`_at_J_zero_distinct_eq_pseudoMass` (PR #1681) with
`pseudoMass_lt_log_two_div` (PR #1705). -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_lt_log_two_div_tanh_sq
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h, β⟩ : IsingParams ℝ) x z <
      Real.log (2 / Real.tanh (β * h) ^ 2) / r := by
  obtain ⟨hmem, heq⟩ :=
    pseudoMassFromParamsAtPair_at_J_zero_distinct_eq_pseudoMass
      hα hr d Λ hh hβ hxz
  rw [heq]
  exact pseudoMass_lt_log_two_div hα hr hmem

/-- **At `J = 0` distinct pair with `0 < h, 0 < β`,
`pseudoMassFromParamsAtPair ≤ log(2/tanh(β·h)^2)/r`**: explicit
quantitative upper bound on the J=0 reference slice. Combines
`_at_J_zero_distinct_eq_pseudoMass` (PR #1681, identifies bridge with
typed `pseudoMass(tanh(β·h)^2)`) with `pseudoMass_le_log_two_div`
(PR #1702). -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_le_log_two_div_tanh_sq
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h, β⟩ : IsingParams ℝ) x z ≤
      Real.log (2 / Real.tanh (β * h) ^ 2) / r := by
  obtain ⟨hmem, heq⟩ :=
    pseudoMassFromParamsAtPair_at_J_zero_distinct_eq_pseudoMass
      hα hr d Λ hh hβ hxz
  rw [heq]
  exact pseudoMass_le_log_two_div hα hr hmem

/-- **At `h = 0` with `truncated2 ∈ Ioo 0 2`,
`pseudoMassFromParamsAtPair < log(2/truncated2)/r`**: strict version
of `_at_h_zero_le_log_two_div_truncated2` (below). Combines
`_at_h_zero_eq_pseudoMass_of_truncated2_mem` (PR #1672) with
`pseudoMass_lt_log_two_div` (PR #1705). -/
theorem pseudoMassFromParamsAtPair_at_h_zero_lt_log_two_div_truncated2
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z <
      Real.log (2 / Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                       (⟨J, 0, β⟩ : IsingParams ℝ) x z) / r := by
  rw [pseudoMassFromParamsAtPair_at_h_zero_eq_pseudoMass_of_truncated2_mem
        hα hr d Λ J β x z htrunc]
  exact pseudoMass_lt_log_two_div hα hr htrunc

/-- **At `h = 0` with `truncated2 ∈ Ioo 0 2`,
`pseudoMassFromParamsAtPair ≤ log(2/truncated2)/r`**: explicit
quantitative upper bound on the bridge in terms of the truncated
2-point function. Combines `_at_h_zero_eq_pseudoMass_of_truncated2_mem`
(PR #1672, identifies bridge with typed `pseudoMass`) with
`pseudoMass_le_log_two_div` (PR #1702). The bound goes to 0 as
truncated2 → 2- and diverges as truncated2 → 0+, capturing the
expected qualitative behaviour. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_le_log_two_div_truncated2
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z ≤
      Real.log (2 / Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                       (⟨J, 0, β⟩ : IsingParams ℝ) x z) / r := by
  rw [pseudoMassFromParamsAtPair_at_h_zero_eq_pseudoMass_of_truncated2_mem
        hα hr d Λ J β x z htrunc]
  exact pseudoMass_le_log_two_div hα hr htrunc

/-- **Multiplied form: `pseudoMassFromParamsAtPair_at_h_zero · r ≤ log(2/truncated2)`**.
Direct multiplication of `_at_h_zero_le_log_two_div_truncated2` (PR #1704)
through by `r > 0`. Useful when `pm·d(x,z)` decay rates appear. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_mul_r_le_log_two_div_truncated2
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z * r ≤
      Real.log (2 / Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                       (⟨J, 0, β⟩ : IsingParams ℝ) x z) := by
  have h := pseudoMassFromParamsAtPair_at_h_zero_le_log_two_div_truncated2
              hα hr d Λ J β x z htrunc
  rw [le_div_iff₀ hr] at h
  exact h

/-- **`pseudoMassFromParamsAtPair_at_h_zero ∈ Ioo 0 (log(2/truncated2)/r)`**
when `truncated2 ∈ Ioo 0 2`: bundles `_pos_of_truncated2_mem` (PR #1679,
strict positivity) with `_lt_log_two_div_truncated2` (PR #1707, strict
upper bound) into a single membership statement. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_mem_Ioo_log_two_div
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈
      Set.Ioo (0 : ℝ)
        (Real.log (2 / Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                         (⟨J, 0, β⟩ : IsingParams ℝ) x z) / r) :=
  ⟨pseudoMassFromParamsAtPair_at_h_zero_pos_of_truncated2_mem
      hα hr d Λ J β x z htrunc,
   pseudoMassFromParamsAtPair_at_h_zero_lt_log_two_div_truncated2
      hα hr d Λ J β x z htrunc⟩

/-- **At `h = 0`, `pseudoMassFromParamsAtPair ≤ (2 - truncated2)/(truncated2 · r)`**:
sharper bound near `truncated2 = 2`, lifted from
`pseudoMass_le_two_sub_div_mul_r` (PR #1715) via bridge identity. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_le_two_sub_div_mul_r
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z ≤
      (2 - Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) x z) /
        (Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) x z * r) := by
  rw [pseudoMassFromParamsAtPair_at_h_zero_eq_pseudoMass_of_truncated2_mem
        hα hr d Λ J β x z htrunc]
  exact pseudoMass_le_two_sub_div_mul_r hα hr htrunc

/-- **Strict version**: same as above with `<`. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_lt_two_sub_div_mul_r
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z <
      (2 - Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) x z) /
        (Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) x z * r) := by
  rw [pseudoMassFromParamsAtPair_at_h_zero_eq_pseudoMass_of_truncated2_mem
        hα hr d Λ J β x z htrunc]
  exact pseudoMass_lt_two_sub_div_mul_r hα hr htrunc

/-- **Strict multiplied form**: `pseudoMassFromParamsAtPair_at_h_zero · r < log(2/truncated2)`. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_mul_r_lt_log_two_div_truncated2
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z * r <
      Real.log (2 / Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                       (⟨J, 0, β⟩ : IsingParams ℝ) x z) := by
  have h := pseudoMassFromParamsAtPair_at_h_zero_lt_log_two_div_truncated2
              hα hr d Λ J β x z htrunc
  rw [lt_div_iff₀ hr] at h
  exact h

/-- **At `J = 0` distinct, `pseudoMassFromParamsAtPair ≤
(2 - tanh(β·h)^2)/(tanh(β·h)^2 · r)`**: sharper bound near
`tanh(β·h)^2 = 1` (which never occurs since `tanh^2 < 1` strictly,
but this captures the linearly-vanishing-with-tanh^2 ↑ regime).
Combines `_at_J_zero_distinct_eq_pseudoMass` with
`pseudoMass_le_two_sub_div_mul_r` (PR #1715). -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_le_two_sub_tanh_sq
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h, β⟩ : IsingParams ℝ) x z ≤
      (2 - Real.tanh (β * h) ^ 2) / (Real.tanh (β * h) ^ 2 * r) := by
  obtain ⟨hmem, heq⟩ :=
    pseudoMassFromParamsAtPair_at_J_zero_distinct_eq_pseudoMass
      hα hr d Λ hh hβ hxz
  rw [heq]
  exact pseudoMass_le_two_sub_div_mul_r hα hr hmem

/-- **Strict version** of `_le_two_sub_tanh_sq`. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_lt_two_sub_tanh_sq
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h, β⟩ : IsingParams ℝ) x z <
      (2 - Real.tanh (β * h) ^ 2) / (Real.tanh (β * h) ^ 2 * r) := by
  obtain ⟨hmem, heq⟩ :=
    pseudoMassFromParamsAtPair_at_J_zero_distinct_eq_pseudoMass
      hα hr d Λ hh hβ hxz
  rw [heq]
  exact pseudoMass_lt_two_sub_div_mul_r hα hr hmem

/-- **Multiplied J=0 form**: `pseudoMassFromParamsAtPair_at_J_zero · r ≤ log(2/tanh^2)`. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_mul_r_le_log_two_div_tanh_sq
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h, β⟩ : IsingParams ℝ) x z * r ≤
      Real.log (2 / Real.tanh (β * h) ^ 2) := by
  have hbnd := pseudoMassFromParamsAtPair_at_J_zero_distinct_le_log_two_div_tanh_sq
                  hα hr d Λ hh hβ hxz
  rw [le_div_iff₀ hr] at hbnd
  exact hbnd

/-- **`pseudoMassFromParamsAtPair_at_J_zero_distinct ∈ Ioo 0 (log(2/tanh^2)/r)`**
when `0 < h, 0 < β`: bundles `_pos_at_J_zero` with `_lt_log_two_div_tanh_sq`
(PR #1709) into one Ioo membership statement. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_mem_Ioo_log_two_div
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h, β⟩ : IsingParams ℝ) x z ∈
      Set.Ioo (0 : ℝ) (Real.log (2 / Real.tanh (β * h) ^ 2) / r) :=
  ⟨pseudoMassFromParamsAtPair_pos_at_J_zero hα hr d Λ hh hβ hxz,
   pseudoMassFromParamsAtPair_at_J_zero_distinct_lt_log_two_div_tanh_sq
      hα hr d Λ hh hβ hxz⟩

/-- **Strict multiplied J=0 form**: `pseudoMassFromParamsAtPair_at_J_zero · r < log(2/tanh^2)`. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_mul_r_lt_log_two_div_tanh_sq
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h, β⟩ : IsingParams ℝ) x z * r <
      Real.log (2 / Real.tanh (β * h) ^ 2) := by
  have hbnd := pseudoMassFromParamsAtPair_at_J_zero_distinct_lt_log_two_div_tanh_sq
                  hα hr d Λ hh hβ hxz
  rw [lt_div_iff₀ hr] at hbnd
  exact hbnd

/-- **`pseudoMassExt` tends to 0 as `c → 2` within `Ioo 0 2`**: squeeze
between `0` (lower bound, `pseudoMassExt_nonneg`) and
`(2 - c) / (c · r)` (upper bound, `pseudoMass_le_two_sub_div_mul_r`,
PR #1715), where the upper bound tends to `0/(2·r) = 0`. -/
theorem pseudoMassExt_tendsto_zero_at_two
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) :
    Filter.Tendsto (pseudoMassExt hα hr) (nhdsWithin 2 (Set.Ioo (0 : ℝ) 2))
      (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
        (g := fun _ : ℝ => (0 : ℝ))
        (h := fun c : ℝ => (2 - c) / (c * r))
  · exact tendsto_const_nhds
  · -- (2 - c)/(c · r) → 0 as c → 2 within Ioo 0 2
    have hcont : ContinuousAt (fun c : ℝ => (2 - c) / (c * r)) 2 := by
      apply ContinuousAt.div
      · exact (continuous_const.sub continuous_id).continuousAt
      · exact (continuous_id.mul continuous_const).continuousAt
      · change (2 : ℝ) * r ≠ 0
        exact (mul_pos (by norm_num : (0 : ℝ) < 2) hr).ne'
    have hval : (2 - 2) / (2 * r) = (0 : ℝ) := by simp
    have htnd : Filter.Tendsto (fun c : ℝ => (2 - c) / (c * r)) (nhds 2) (nhds 0) := by
      rw [← hval]
      exact hcont.tendsto
    exact htnd.mono_left nhdsWithin_le_nhds
  · -- 0 ≤ pseudoMassExt(c) (eventually)
    refine Filter.Eventually.of_forall ?_
    intro c
    exact pseudoMassExt_nonneg hα hr c
  · -- pseudoMassExt(c) ≤ (2-c)/(c·r) (eventually within Ioo 0 2)
    rw [Filter.eventually_iff]
    rw [mem_nhdsWithin]
    refine ⟨Set.univ, isOpen_univ, ⟨⟩, ?_⟩
    intro c hc_pair
    have hc : c ∈ Set.Ioo (0 : ℝ) 2 := hc_pair.2
    change pseudoMassExt hα hr c ≤ (2 - c) / (c * r)
    rw [pseudoMassExt_of_mem hα hr hc]
    exact pseudoMass_le_two_sub_div_mul_r hα hr hc

/-- **At `h = 0` ferromagnetic, `pseudoMassFromParamsAtPair ≥ pseudoMass(1)`**
when `0 < truncated2`: combines `_at_h_zero_ge_pseudoMass_of_truncated2_le`
(PR #1677) with `truncated2Infinite_le_one` (ferromagnetic) to get a
uniform lower bound `pseudoMass(1)` on the bridge.

`pseudoMass(1)` here means `pseudoMass hα hr ⟨zero_lt_one, one_lt_two⟩`.

Useful uniform-in-(β, J) lower bound: as long as truncated2 is
strictly positive and bounded by 1 (ferromagnetic), the bridge is
at least `pseudoMass(1)`. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_ge_pseudoMass_one
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (x z : Fin d → ℤ)
    (htrunc_pos : 0 < Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                        (⟨J, 0, β⟩ : IsingParams ℝ) x z) :
    pseudoMass hα hr (show (1 : ℝ) ∈ Set.Ioo 0 2 from
        ⟨zero_lt_one, one_lt_two⟩) ≤
      pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z := by
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) :=
    ⟨hJ, le_refl 0, hβ⟩
  have htrunc_le_one : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                          (⟨J, 0, β⟩ : IsingParams ℝ) x z ≤ 1 :=
    Ambient.truncated2Infinite_le_one (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) hf x z
  have htrunc_mem : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                      (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2 :=
    ⟨htrunc_pos, by linarith⟩
  have hone_mem : (1 : ℝ) ∈ Set.Ioo (0 : ℝ) 2 := ⟨zero_lt_one, one_lt_two⟩
  exact pseudoMassFromParamsAtPair_at_h_zero_ge_pseudoMass_of_truncated2_le
            hα hr d Λ J β x z hone_mem htrunc_mem htrunc_le_one

/-- **At `h = 0` ferromagnetic, `0 < pseudoMassFromParamsAtPair`**
when `0 < truncated2`: avoids the explicit `Ioo 0 2` membership
hypothesis by combining `truncated2Infinite_le_one` (ferromagnetic
→ truncated2 ≤ 1 < 2) to derive membership. Useful when only
strict positivity of truncated2 is known. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_pos_of_truncated2_pos
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (x z : Fin d → ℤ)
    (htrunc_pos : 0 < Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                        (⟨J, 0, β⟩ : IsingParams ℝ) x z) :
    0 < pseudoMassFromParamsAtPair hα hr d Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) x z := by
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) :=
    ⟨hJ, le_refl 0, hβ⟩
  have htrunc_le_one : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                          (⟨J, 0, β⟩ : IsingParams ℝ) x z ≤ 1 :=
    Ambient.truncated2Infinite_le_one (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) hf x z
  have htrunc_mem : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                      (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2 :=
    ⟨htrunc_pos, by linarith⟩
  exact pseudoMassFromParamsAtPair_at_h_zero_pos_of_truncated2_mem
            hα hr d Λ J β x z htrunc_mem

/-- **At `J = 0` distinct, `pseudoMassFromParamsAtPair ≥ pseudoMass(1)`**
when `0 < h, 0 < β`: J=0 reference slice analog of
`_at_h_zero_ge_pseudoMass_one` (PR #1725). Uses
`pseudoMassFromParamsAtPair_at_J_zero_distinct_eq_pseudoMass` (PR #1681)
+ `pseudoMass_antitone` (PR #1714) with the bound `tanh(β·h)^2 ≤ 1`. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_ge_pseudoMass_one
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    pseudoMass hα hr (show (1 : ℝ) ∈ Set.Ioo 0 2 from
        ⟨zero_lt_one, one_lt_two⟩) ≤
      pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h, β⟩ : IsingParams ℝ) x z := by
  obtain ⟨hmem, heq⟩ :=
    pseudoMassFromParamsAtPair_at_J_zero_distinct_eq_pseudoMass
      hα hr d Λ hh hβ hxz
  have habs : |Real.tanh (β * h)| < 1 := Real.abs_tanh_lt_one _
  have htanh_lt : Real.tanh (β * h) < 1 := lt_of_abs_lt habs
  have htanh_gt_neg : -1 < Real.tanh (β * h) := neg_lt_of_abs_lt habs
  have htanh_sq_le_one : Real.tanh (β * h) ^ 2 ≤ 1 := by nlinarith
  have hone_mem : (1 : ℝ) ∈ Set.Ioo (0 : ℝ) 2 := ⟨zero_lt_one, one_lt_two⟩
  have hge : pseudoMass hα hr hone_mem ≤ pseudoMass hα hr hmem :=
    pseudoMass_antitone hα hr hmem hone_mem htanh_sq_le_one
  rw [heq]
  exact hge

/-- **`pseudoMassFromParamsAtPair_at_h_zero ≠ 0`** when truncated2 ∈ Ioo 0 2:
trivial corollary of `_pos_of_truncated2_mem` (PR #1679). -/
theorem pseudoMassFromParamsAtPair_at_h_zero_ne_zero_of_truncated2_mem
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMassFromParamsAtPair hα hr d Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z ≠ 0 :=
  (pseudoMassFromParamsAtPair_at_h_zero_pos_of_truncated2_mem
      hα hr d Λ J β x z htrunc).ne'

/-- **`pseudoMassFromParamsAtPair_at_h_zero ≠ 0`** when truncated2 > 0
under ferromagnetic: companion of `_ne_zero_of_truncated2_mem` using
the simpler positivity hypothesis. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_ne_zero_of_truncated2_pos
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (x z : Fin d → ℤ)
    (htrunc_pos : 0 < Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                        (⟨J, 0, β⟩ : IsingParams ℝ) x z) :
    pseudoMassFromParamsAtPair hα hr d Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z ≠ 0 :=
  (pseudoMassFromParamsAtPair_at_h_zero_pos_of_truncated2_pos
      hα hr d Λ hJ hβ x z htrunc_pos).ne'

/-- **`pseudoMassFromParamsAtPair_at_J_zero_distinct ≠ 0`** for
ferromagnetic, h>0, β>0, distinct pair: trivial from
`pseudoMassFromParamsAtPair_pos_at_J_zero`. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_ne_zero
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    pseudoMassFromParamsAtPair hα hr d Λ
        (⟨0, h, β⟩ : IsingParams ℝ) x z ≠ 0 :=
  (pseudoMassFromParamsAtPair_pos_at_J_zero hα hr d Λ hh hβ hxz).ne'

/-- **`pseudoMassFromParamsAtPair_at_h_zero < pseudoMass(c) ↔ c < truncated2`**
when both `c, truncated2 ∈ Ioo 0 2`: pseudoMass strict anti reverses the
inequality. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_lt_pseudoMass_iff_lt_truncated2
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 2)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z <
      pseudoMass hα hr hc ↔
    c < Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) x z := by
  rw [pseudoMassFromParamsAtPair_at_h_zero_eq_pseudoMass_of_truncated2_mem
        hα hr d Λ J β x z htrunc]
  refine ⟨?_, fun hlt => pseudoMass_strictAnti hα hr hc htrunc hlt⟩
  intro hlt
  by_contra h_neg
  have h_neg' : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) x z ≤ c := not_lt.mp h_neg
  exact absurd hlt (not_lt.mpr (pseudoMass_antitone hα hr htrunc hc h_neg'))

/-- **`pseudoMass(c) < pseudoMassFromParamsAtPair_at_h_zero ↔ truncated2 < c`**:
companion of `_lt_pseudoMass_iff_lt_truncated2`. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_gt_pseudoMass_iff_gt_truncated2
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 2)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMass hα hr hc <
      pseudoMassFromParamsAtPair hα hr d Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z ↔
    Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z < c := by
  rw [pseudoMassFromParamsAtPair_at_h_zero_eq_pseudoMass_of_truncated2_mem
        hα hr d Λ J β x z htrunc]
  refine ⟨?_, fun hlt => pseudoMass_strictAnti hα hr htrunc hc hlt⟩
  intro hlt
  by_contra h_neg
  have h_neg' : c ≤ Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                      (⟨J, 0, β⟩ : IsingParams ℝ) x z := not_lt.mp h_neg
  exact absurd hlt (not_lt.mpr (pseudoMass_antitone hα hr hc htrunc h_neg'))

/-- **`pseudoMassFromParamsAtPair_at_h_zero ≤ pseudoMass(c) ↔ c ≤ truncated2`**:
non-strict version of `_lt_pseudoMass_iff_lt_truncated2`. Uses
`pseudoMass_antitone` for both directions. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_le_pseudoMass_iff_le_truncated2
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 2)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z ≤
      pseudoMass hα hr hc ↔
    c ≤ Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) x z := by
  rw [pseudoMassFromParamsAtPair_at_h_zero_eq_pseudoMass_of_truncated2_mem
        hα hr d Λ J β x z htrunc]
  refine ⟨?_, fun hle => pseudoMass_antitone hα hr hc htrunc hle⟩
  intro hle
  by_contra h_neg
  have h_neg' : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) x z < c := not_le.mp h_neg
  have := pseudoMass_strictAnti hα hr htrunc hc h_neg'
  linarith

/-- **`pseudoMass(c) ≤ pseudoMassFromParamsAtPair_at_h_zero ↔ truncated2 ≤ c`**:
companion non-strict iff. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_ge_pseudoMass_iff_ge_truncated2
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 2)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMass hα hr hc ≤
      pseudoMassFromParamsAtPair hα hr d Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z ↔
    Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z ≤ c := by
  rw [pseudoMassFromParamsAtPair_at_h_zero_eq_pseudoMass_of_truncated2_mem
        hα hr d Λ J β x z htrunc]
  refine ⟨?_, fun hle => pseudoMass_antitone hα hr htrunc hc hle⟩
  intro hle
  by_contra h_neg
  have h_neg' : c < Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                      (⟨J, 0, β⟩ : IsingParams ℝ) x z := not_le.mp h_neg
  have := pseudoMass_strictAnti hα hr hc htrunc h_neg'
  linarith

/-- **`pseudoMassFromParamsAtPair_at_h_zero = pseudoMass(c) ↔ truncated2 = c`**:
combines the `_le_iff` and `_ge_iff` non-strict iff characterizations
via antisymmetry. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_eq_pseudoMass_iff_truncated2_eq
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 2)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z =
      pseudoMass hα hr hc ↔
    Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z = c := by
  refine ⟨?_, ?_⟩
  · intro heq
    have hle : pseudoMassFromParamsAtPair hα hr d Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ≤ pseudoMass hα hr hc := heq.le
    have hge : pseudoMass hα hr hc ≤ pseudoMassFromParamsAtPair hα hr d Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z := heq.ge
    have h1 := (pseudoMassFromParamsAtPair_at_h_zero_le_pseudoMass_iff_le_truncated2
                  hα hr d Λ J β x z hc htrunc).mp hle
    have h2 := (pseudoMassFromParamsAtPair_at_h_zero_ge_pseudoMass_iff_ge_truncated2
                  hα hr d Λ J β x z hc htrunc).mp hge
    linarith
  · intro heq_t
    rw [pseudoMassFromParamsAtPair_at_h_zero_eq_pseudoMass_of_truncated2_mem
          hα hr d Λ J β x z htrunc]
    congr 1

/-- **`pseudoMassFromParamsAtPair_at_J_zero_distinct < pseudoMass(c) ↔
c < tanh(β·h)^2`**: J=0 analog of `_at_h_zero_lt_pseudoMass_iff_lt_truncated2`. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_lt_pseudoMass_iff_lt_tanh_sq
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z)
    {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h, β⟩ : IsingParams ℝ) x z <
      pseudoMass hα hr hc ↔
    c < Real.tanh (β * h) ^ 2 := by
  obtain ⟨hmem, heq⟩ :=
    pseudoMassFromParamsAtPair_at_J_zero_distinct_eq_pseudoMass
      hα hr d Λ hh hβ hxz
  rw [heq]
  refine ⟨?_, fun hlt => pseudoMass_strictAnti hα hr hc hmem hlt⟩
  intro hlt
  by_contra h_neg
  have h_neg' : Real.tanh (β * h) ^ 2 ≤ c := not_lt.mp h_neg
  exact absurd hlt (not_lt.mpr (pseudoMass_antitone hα hr hmem hc h_neg'))

/-- **`pseudoMass(c) < pseudoMassFromParamsAtPair_at_J_zero_distinct ↔
tanh(β·h)^2 < c`**. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_gt_pseudoMass_iff_gt_tanh_sq
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z)
    {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMass hα hr hc <
      pseudoMassFromParamsAtPair hα hr d Λ
        (⟨0, h, β⟩ : IsingParams ℝ) x z ↔
    Real.tanh (β * h) ^ 2 < c := by
  obtain ⟨hmem, heq⟩ :=
    pseudoMassFromParamsAtPair_at_J_zero_distinct_eq_pseudoMass
      hα hr d Λ hh hβ hxz
  rw [heq]
  refine ⟨?_, fun hlt => pseudoMass_strictAnti hα hr hmem hc hlt⟩
  intro hlt
  by_contra h_neg
  have h_neg' : c ≤ Real.tanh (β * h) ^ 2 := not_lt.mp h_neg
  exact absurd hlt (not_lt.mpr (pseudoMass_antitone hα hr hc hmem h_neg'))

/-- **`pseudoMassFromParamsAtPair_at_J_zero_distinct ≤ pseudoMass(c) ↔
c ≤ tanh(β·h)^2`**: non-strict version of `_lt_pseudoMass_iff_lt_tanh_sq`. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_le_pseudoMass_iff_le_tanh_sq
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z)
    {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h, β⟩ : IsingParams ℝ) x z ≤
      pseudoMass hα hr hc ↔
    c ≤ Real.tanh (β * h) ^ 2 := by
  obtain ⟨hmem, heq⟩ :=
    pseudoMassFromParamsAtPair_at_J_zero_distinct_eq_pseudoMass
      hα hr d Λ hh hβ hxz
  rw [heq]
  refine ⟨?_, fun hle => pseudoMass_antitone hα hr hc hmem hle⟩
  intro hle
  by_contra h_neg
  have h_neg' : Real.tanh (β * h) ^ 2 < c := not_le.mp h_neg
  have := pseudoMass_strictAnti hα hr hmem hc h_neg'
  linarith

/-- **`pseudoMass(c) ≤ pseudoMassFromParamsAtPair_at_J_zero_distinct ↔
tanh(β·h)^2 ≤ c`**: companion non-strict iff. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_ge_pseudoMass_iff_ge_tanh_sq
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z)
    {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMass hα hr hc ≤
      pseudoMassFromParamsAtPair hα hr d Λ
        (⟨0, h, β⟩ : IsingParams ℝ) x z ↔
    Real.tanh (β * h) ^ 2 ≤ c := by
  obtain ⟨hmem, heq⟩ :=
    pseudoMassFromParamsAtPair_at_J_zero_distinct_eq_pseudoMass
      hα hr d Λ hh hβ hxz
  rw [heq]
  refine ⟨?_, fun hle => pseudoMass_antitone hα hr hmem hc hle⟩
  intro hle
  by_contra h_neg
  have h_neg' : c < Real.tanh (β * h) ^ 2 := not_le.mp h_neg
  have := pseudoMass_strictAnti hα hr hc hmem h_neg'
  linarith

/-- **`pseudoMassFromParamsAtPair_at_J_zero_distinct = pseudoMass(c) ↔
tanh(β·h)^2 = c`**: equality iff via antisymmetry of le/ge iff
characterizations (PR #1739). -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_eq_pseudoMass_iff_tanh_sq_eq
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z)
    {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h, β⟩ : IsingParams ℝ) x z =
      pseudoMass hα hr hc ↔
    Real.tanh (β * h) ^ 2 = c := by
  refine ⟨?_, ?_⟩
  · intro heq
    have h1 := (pseudoMassFromParamsAtPair_at_J_zero_distinct_le_pseudoMass_iff_le_tanh_sq
                  hα hr d Λ hh hβ hxz hc).mp heq.le
    have h2 := (pseudoMassFromParamsAtPair_at_J_zero_distinct_ge_pseudoMass_iff_ge_tanh_sq
                  hα hr d Λ hh hβ hxz hc).mp heq.ge
    linarith
  · intro heq_t
    obtain ⟨hmem, h_eq_pm⟩ :=
      pseudoMassFromParamsAtPair_at_J_zero_distinct_eq_pseudoMass
        hα hr d Λ hh hβ hxz
    rw [h_eq_pm]
    congr 1

/-- **`pseudoMassFromParamsAtPair_at_h_zero pos iff truncated2 ≠ 0`**:
combines `_at_h_zero_pos_iff` (PR #1670, pos iff truncated2 > 0) with
`truncated2Infinite_pos_iff_ne_zero` (PR #1748). -/
theorem pseudoMassFromParamsAtPair_at_h_zero_pos_iff_ne_zero
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (x z : Fin d → ℤ) :
    0 < pseudoMassFromParamsAtPair hα hr d Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) x z ↔
    Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z ≠ 0 := by
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) :=
    ⟨hJ, le_refl 0, hβ⟩
  rw [pseudoMassFromParamsAtPair_at_h_zero_pos_iff hα hr d Λ hJ hβ x z]
  exact Ambient.truncated2Infinite_pos_iff_ne_zero
            (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) hf x z

/-- **`0 < pseudoMassFromParamsAtPair ↔ pseudoMassFromParamsAtPair ≠ 0`**:
trivial via `pseudoMassFromParamsAtPair_nonneg`. -/
theorem pseudoMassFromParamsAtPair_pos_iff_ne_zero
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (x z : Fin d → ℤ) :
    0 < pseudoMassFromParamsAtPair hα hr d Λ p x z ↔
    pseudoMassFromParamsAtPair hα hr d Λ p x z ≠ 0 :=
  (pseudoMassFromParamsAtPair_nonneg hα hr d Λ p x z).lt_iff_ne.trans
    ⟨fun h => h.symm, fun h => h.symm⟩

/-- **At `h = 0`, `pseudoMassFromParamsAtPair ∈ Ioo 0 ((2-truncated2)/(truncated2·r))`**:
sharper Ioo membership at h=0 using `(2-c)/(c·r)`. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_mem_Ioo_zero_two_sub_div
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈
      Set.Ioo (0 : ℝ)
        ((2 - Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) x z) /
         (Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) x z * r)) :=
  ⟨pseudoMassFromParamsAtPair_at_h_zero_pos_of_truncated2_mem
      hα hr d Λ J β x z htrunc,
   pseudoMassFromParamsAtPair_at_h_zero_lt_two_sub_div_mul_r
      hα hr d Λ J β x z htrunc⟩

/-- **At `J = 0` distinct, `pseudoMassFromParamsAtPair ∈ Ioo 0 ((2-tanh^2)/(tanh^2·r))`**. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_mem_Ioo_zero_two_sub_div
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h, β⟩ : IsingParams ℝ) x z ∈
      Set.Ioo (0 : ℝ) ((2 - Real.tanh (β * h) ^ 2) / (Real.tanh (β * h) ^ 2 * r)) :=
  ⟨pseudoMassFromParamsAtPair_pos_at_J_zero hα hr d Λ hh hβ hxz,
   pseudoMassFromParamsAtPair_at_J_zero_distinct_lt_two_sub_tanh_sq
      hα hr d Λ hh hβ hxz⟩

/-- **`¬(pseudoMassFromParamsAtPair < 0)`**: trivial via nonneg. -/
theorem pseudoMassFromParamsAtPair_not_lt_zero
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (x z : Fin d → ℤ) :
    ¬ (pseudoMassFromParamsAtPair hα hr d Λ p x z < 0) :=
  not_lt.mpr (pseudoMassFromParamsAtPair_nonneg hα hr d Λ p x z)

/-- **`pseudoMassFromParamsAtPair ≤ 0 ↔ pseudoMassFromParamsAtPair = 0`**:
trivial via nonneg + antisymmetry. -/
theorem pseudoMassFromParamsAtPair_le_zero_iff_eq_zero
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (x z : Fin d → ℤ) :
    pseudoMassFromParamsAtPair hα hr d Λ p x z ≤ 0 ↔
    pseudoMassFromParamsAtPair hα hr d Λ p x z = 0 := by
  refine ⟨?_, fun h => le_of_eq h⟩
  intro hle
  exact le_antisymm hle (pseudoMassFromParamsAtPair_nonneg hα hr d Λ p x z)

/-- **`pseudoMassFromParamsAtPair < pseudoMassExt(c) ↔ c < correlation`** when both
in `Ioo 0 2`: iff form using the bridge identity. -/
theorem pseudoMassFromParamsAtPair_lt_pseudoMassExt_iff_lt_corr
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (x z : Fin d → ℤ)
    {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 2)
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z}
              ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMassFromParamsAtPair hα hr d Λ p x z <
      pseudoMassExt hα hr c ↔
    c < Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z} := by
  unfold pseudoMassFromParamsAtPair
  exact pseudoMassExt_lt_iff hα hr hc hcorr

/-- **`pseudoMassExt(c) < pseudoMassFromParamsAtPair ↔ correlation < c`**: companion. -/
theorem pseudoMassFromParamsAtPair_gt_pseudoMassExt_iff_corr_lt
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (x z : Fin d → ℤ)
    {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 2)
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z}
              ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMassExt hα hr c <
      pseudoMassFromParamsAtPair hα hr d Λ p x z ↔
    Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z} < c := by
  unfold pseudoMassFromParamsAtPair
  exact pseudoMassExt_lt_iff hα hr hcorr hc

/-- **`pseudoMassFromParamsAtPair ≤ pseudoMassExt(c) ↔ c ≤ correlation`**:
non-strict iff form. -/
theorem pseudoMassFromParamsAtPair_le_pseudoMassExt_iff_le_corr
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (x z : Fin d → ℤ)
    {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 2)
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z}
              ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMassFromParamsAtPair hα hr d Λ p x z ≤
      pseudoMassExt hα hr c ↔
    c ≤ Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z} := by
  unfold pseudoMassFromParamsAtPair
  exact pseudoMassExt_le_iff hα hr hc hcorr

/-- **`pseudoMassExt(c) ≤ pseudoMassFromParamsAtPair ↔ correlation ≤ c`**. -/
theorem pseudoMassFromParamsAtPair_ge_pseudoMassExt_iff_corr_le
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (x z : Fin d → ℤ)
    {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 2)
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z}
              ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMassExt hα hr c ≤
      pseudoMassFromParamsAtPair hα hr d Λ p x z ↔
    Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z} ≤ c := by
  unfold pseudoMassFromParamsAtPair
  exact pseudoMassExt_le_iff hα hr hcorr hc

/-- **`pseudoMassFromParamsAtPair = pseudoMassExt(c) ↔ correlation = c`**:
equality iff. -/
theorem pseudoMassFromParamsAtPair_eq_pseudoMassExt_iff_corr_eq
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (x z : Fin d → ℤ)
    {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 2)
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z}
              ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMassFromParamsAtPair hα hr d Λ p x z =
      pseudoMassExt hα hr c ↔
    Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z} = c := by
  unfold pseudoMassFromParamsAtPair
  rw [pseudoMassExt_eq_iff_of_mem hα hr hc hcorr]
  exact eq_comm

/-- **Λ-uniform `pseudoMass(1)` lower bound at h=0**: combines
`_at_h_zero_ge_pseudoMass_one` (PR #1725) with `_indep_exhaustion`
(PR #1666) to make the lower bound explicitly Λ-independent. For any
two exhaustions Λ, Λ', the bridge values are equal (under ferromagnetic),
and both bounded below by `pseudoMass(1)`. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_ge_pseudoMass_one_uniform
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ Λ' : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ'.volume n)).edgeSet]
    {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (x z : Fin d → ℤ)
    (htrunc_pos : 0 < Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                        (⟨J, 0, β⟩ : IsingParams ℝ) x z) :
    pseudoMass hα hr (show (1 : ℝ) ∈ Set.Ioo 0 2 from
        ⟨zero_lt_one, one_lt_two⟩) ≤
      pseudoMassFromParamsAtPair hα hr d Λ' (⟨J, 0, β⟩ : IsingParams ℝ) x z := by
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) :=
    ⟨hJ, le_refl 0, hβ⟩
  rw [← pseudoMassFromParamsAtPair_indep_exhaustion hα hr d Λ Λ'
        (⟨J, 0, β⟩ : IsingParams ℝ) hf x z]
  exact pseudoMassFromParamsAtPair_at_h_zero_ge_pseudoMass_one
            hα hr d Λ hJ hβ x z htrunc_pos

/-- **`pseudoMassFromParamsAtPair ∈ Ici 0`** (always): direct from
nonneg. -/
theorem pseudoMassFromParamsAtPair_mem_Ici_zero
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (x z : Fin d → ℤ) :
    pseudoMassFromParamsAtPair hα hr d Λ p x z ∈ Set.Ici (0 : ℝ) :=
  pseudoMassFromParamsAtPair_nonneg hα hr d Λ p x z

/-- **At `J = 0` distinct, `pseudoMassFromParamsAtPair ∈ Ioo 0 (log(2/tanh^2)/r)`**:
J=0 analog of `_at_h_zero_mem_Ioo_log_two_div`. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_mem_Ioo_zero_log_two_div
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h, β⟩ : IsingParams ℝ) x z ∈
      Set.Ioo (0 : ℝ) (Real.log (2 / Real.tanh (β * h) ^ 2) / r) :=
  ⟨pseudoMassFromParamsAtPair_pos_at_J_zero hα hr d Λ hh hβ hxz,
   pseudoMassFromParamsAtPair_at_J_zero_distinct_lt_log_two_div_tanh_sq
      hα hr d Λ hh hβ hxz⟩

/-- **At `h = 0` with `truncated2 ∈ Ioo 0 2`,
`pseudoMassFromParamsAtPair_at_h_zero ∈ Ioo 0 (log(2/truncated2)/r)`**:
bundles `_pos_of_truncated2_mem` (PR #1679) + `_lt_log_two_div_truncated2`
(PR #1707). -/
theorem pseudoMassFromParamsAtPair_at_h_zero_mem_Ioo_zero_log_two_div
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈
      Set.Ioo (0 : ℝ)
        (Real.log (2 / Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                         (⟨J, 0, β⟩ : IsingParams ℝ) x z) / r) :=
  ⟨pseudoMassFromParamsAtPair_at_h_zero_pos_of_truncated2_mem
      hα hr d Λ J β x z htrunc,
   pseudoMassFromParamsAtPair_at_h_zero_lt_log_two_div_truncated2
      hα hr d Λ J β x z htrunc⟩

/-- **At `h = 0` with `truncated2 ∈ Ioo 0 2`,
`pseudoMassFromParamsAtPair_at_h_zero ∈ Iio (log(2/truncated2)/r)`**. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_mem_Iio_log_two_div
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈
      Set.Iio (Real.log (2 / Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                              (⟨J, 0, β⟩ : IsingParams ℝ) x z) / r) :=
  pseudoMassFromParamsAtPair_at_h_zero_lt_log_two_div_truncated2
      hα hr d Λ J β x z htrunc

/-- **At `h = 0`, `pseudoMassFromParamsAtPair ∈ Ici 0`**: trivial. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_mem_Ici_zero
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈
      Set.Ici (0 : ℝ) :=
  pseudoMassFromParamsAtPair_nonneg hα hr d Λ _ x z

/-- **At `J = 0` distinct, `pseudoMassFromParamsAtPair ∈ Iio (log(2/tanh^2)/r)`**. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_mem_Iio_log_two_div
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h, β⟩ : IsingParams ℝ) x z ∈
      Set.Iio (Real.log (2 / Real.tanh (β * h) ^ 2) / r) :=
  pseudoMassFromParamsAtPair_at_J_zero_distinct_lt_log_two_div_tanh_sq
      hα hr d Λ hh hβ hxz

/-- **At `J = 0` distinct, `pseudoMassFromParamsAtPair ∈ Iio ((2-tanh^2)/(tanh^2·r))`**. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_mem_Iio_two_sub_tanh_sq
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h, β⟩ : IsingParams ℝ) x z ∈
      Set.Iio ((2 - Real.tanh (β * h) ^ 2) / (Real.tanh (β * h) ^ 2 * r)) :=
  pseudoMassFromParamsAtPair_at_J_zero_distinct_lt_two_sub_tanh_sq
      hα hr d Λ hh hβ hxz

/-- **`pseudoMassFromParamsAtPair ∈ Ioi 0`** when corr ∈ Ioo 0 2: -/
theorem pseudoMassFromParamsAtPair_mem_Ioi_zero_of_corr_mem
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (x z : Fin d → ℤ)
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z}
              ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMassFromParamsAtPair hα hr d Λ p x z ∈ Set.Ioi (0 : ℝ) :=
  pseudoMassFromParamsAtPair_pos_of_corr_mem hα hr d Λ p x z hcorr

/-- **`pseudoMassFromParamsAtPair ∉ Iio 0`**: trivial. -/
theorem pseudoMassFromParamsAtPair_not_mem_Iio_zero
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (x z : Fin d → ℤ) :
    pseudoMassFromParamsAtPair hα hr d Λ p x z ∉ Set.Iio (0 : ℝ) :=
  not_lt.mpr (pseudoMassFromParamsAtPair_nonneg hα hr d Λ p x z)

end IsingModel

import IsingModel.PseudoMass.ExistenceDerivative

/-!
# Pseudo-Mass Basic Properties

This module is part of the split `IsingModel.PseudoMass` development.
-/

namespace IsingModel

open Set Real Filter

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

/-- If `h` satisfies the pseudo-mass defining equation
`pseudoMassG α r (h ·) = c` locally near `β` and is differentiable at `β`,
then its derivative equals `c'(β) / g'(h(β))`, where
`g' = d/dt pseudoMassG α r`.
This is the key implicit differentiation step for the GJ §17.5 Lipschitz estimate. -/
theorem pseudoMass_deriv_formula
    (α : ℕ) {r : ℝ} (hr : 0 < r)
    {h c : ℝ → ℝ} {h' c' β : ℝ}
    (hh : HasDerivAt h h' β)
    (hc : HasDerivAt c c' β)
    (hβ : 0 ≤ h β)
    (hg_eq : (fun β' => pseudoMassG α r (h β')) =ᶠ[nhds β] c)
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
  -- But `pseudoMassG α r ∘ h` agrees with `c` near `β` (by `hg_eq`).
  have hcomp' : HasDerivAt c (g' * h') β := by
    exact hcomp.congr_of_eventuallyEq hg_eq.symm
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
  exact Filter.Eventually.of_forall fun β' => pseudoMass_spec hα hr (hc_fam β')

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

end IsingModel

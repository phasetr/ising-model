import IsingModel.PseudoMass.Profile

/-!
# Pseudo-Mass Profile Existence and Derivatives

This module is part of the split `IsingModel.PseudoMass` development.
-/

namespace IsingModel

open Set Real Filter

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

end IsingModel

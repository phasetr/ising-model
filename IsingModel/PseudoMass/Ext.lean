import IsingModel.PseudoMass.Continuity

/-!
# Pseudo-Mass Totalization

This module is part of the split `IsingModel.PseudoMass` development.
-/

namespace IsingModel

open Set Real Filter

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

/-- **Local defining equation for the totalized pseudo-mass**: if a profile
`c` stays in `Ioo 0 2` near `β`, then `pseudoMassExt hα hr ∘ c` satisfies the
implicit pseudo-mass equation near `β`. -/
theorem pseudoMassG_pseudoMassExt_eventuallyEq_of_eventually_mem
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {c : ℝ → ℝ} {β : ℝ}
    (hc : ∀ᶠ β' in nhds β, c β' ∈ Set.Ioo (0 : ℝ) 2) :
    (fun β' => pseudoMassG α r (pseudoMassExt hα hr (c β'))) =ᶠ[nhds β] c := by
  filter_upwards [hc] with β' hβ'
  rw [pseudoMassExt_of_mem hα hr hβ']
  exact pseudoMass_spec hα hr hβ'

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

end IsingModel

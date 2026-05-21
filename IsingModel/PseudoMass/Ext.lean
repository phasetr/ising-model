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


end IsingModel

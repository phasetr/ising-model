import IsingModel.PseudoMass.Lipschitz

/-!
# Pseudo-Mass Continuity

This module is part of the split `IsingModel.PseudoMass` development.
-/

namespace IsingModel

open Set Real Filter

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


end IsingModel

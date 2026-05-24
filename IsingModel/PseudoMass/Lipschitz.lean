import IsingModel.PseudoMass.Basic

/-!
# Pseudo-Mass Lipschitz Bounds

This module is part of the split `IsingModel.PseudoMass` development.
-/

namespace IsingModel

open Set Real Filter

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
    (hg_eq : (fun β' => pseudoMassG α r (h β')) =ᶠ[nhds β] c)
    (hm_pos : 0 < h β)
    (hc_pos : 0 < c β) :
    |h'| ≤ |c'| / (r * c β) := by
  set g' := (-2 * r * Real.exp (-(h β * r)) * (1 + (h β * r) ^ α) -
      2 * Real.exp (-(h β * r)) * (↑α * (h β * r) ^ (α - 1) * r)) /
     (1 + (h β * r) ^ α) ^ 2 with hg'_def
  have hform : h' = c' / g' :=
    pseudoMass_deriv_formula α hr hh hc hβ hg_eq hm_pos
  have hg'_neg : g' < 0 := pseudoMassG_deriv_neg α hm_pos hr
  have hge : r * c β ≤ |g'| := by
    have h1 := pseudoMassG_deriv_abs_ge α hβ hr
    have hg_at : pseudoMassG α r (h β) = c β := hg_eq.eq_of_nhds
    rwa [hg_at] at h1
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
    (hg_eq : (fun β' => pseudoMassG α r (h β')) =ᶠ[nhds β] c)
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
    (hg_eq : (fun β' => pseudoMassG α r (h β')) =ᶠ[nhds β] c)
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
`|(h β₂)^(2α+1) − (h β₁)^(2α+1)| ≤ ↑(2α+1)·K/r · (β₂ − β₁)`
for `β₁ ≤ β₂`.

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
    (hg_eq : ∀ β' ∈ Set.Icc β₁ β₂,
      (fun γ => pseudoMassG α r (h γ)) =ᶠ[nhds β'] c)
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
        (hβ_nn β' hβ'_mem) (hg_eq β' hβ'_mem)
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

end IsingModel

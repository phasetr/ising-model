import IsingModel.PseudoMass.Profile

/-!
# Discrete HLS pair-bound for the PseudoMass denominator form

Step 119 plan Step 5.5c capstone (GJ Theorem 17.5.1 proof trace, p. 312).

This module composes the pointwise pair bridge from
`IsingModel.PseudoMass.Profile` with the existing discrete HLS pair-sum bound
`tsum_pow_neg_conv_le_const` (`IsingModel.PolyDecay`) to obtain the infinite-sum
bound on the natural-α PseudoMass denominator form:

    ∑_z 1/(1+(M·d(x,z))^α) · 1/(1+(M·d(y,z))^α)
      ≤ (max(1, (M^α)⁻¹) · 2^α)² · ∑_z (1 + d(0,z))^(-(2α : ℝ)).

The constant prefactor `(max(1, (M^α)⁻¹) · 2^α)²` collapses to
`M^(-2α) · 4^α` (the GJ p. 312 `m⁻^(-2α)` scaling) when `M ≤ 1` and `α ≥ 1`,
and to `4^α` when `M^α ≥ 1`.

**Reference:** Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.5, p. 312.
-/

namespace IsingModel

open Real

/-- **Discrete HLS pair-bound for PseudoMass denominator form**
(Step 119 plan Step 5.5c capstone).

For `d : ℕ`, `α : ℕ` with `d < 2α`, `M > 0`, and `x y : Fin d → ℤ`:
```
∑_z 1/(1+(M·d(x,z))^α) · 1/(1+(M·d(y,z))^α)
  ≤ (max(1, (M^α)⁻¹) · 2^α)² · ∑_z (1 + d(0,z))^(-(2α : ℝ)).
```

Composition of `one_div_one_add_M_t_pow_pair_le_const_sq_mul_one_div_one_add_pow_pow`
(pair pointwise bridge) and `one_div_one_add_pow_eq_rpow_neg` (form bridge to
real-α rpow form) with the existing `tsum_pow_neg_conv_le_const`
(`IsingModel/PolyDecay.lean:207`, real-α HLS pair-sum bound).

Summability of the natural-α LHS pair is obtained by comparison with the
summable AM-GM bound `((1+d_x)^(-2α) + (1+d_y)^(-2α))/2`, paralleling the
existing PolyDecay proof.

**Reference:** Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.5, p. 312. -/
theorem tsum_pseudoMass_pair_product_le_const_pow_M
    (d : ℕ) {α : ℕ} (hαd : d < 2 * α) {M : ℝ} (hM : 0 < M)
    (x y : Fin d → ℤ) :
    ∑' z : Fin d → ℤ,
        1 / (1 + (M * (latticeDistance d x z : ℝ)) ^ α) *
        (1 / (1 + (M * (latticeDistance d y z : ℝ)) ^ α)) ≤
      (max 1 (M ^ α)⁻¹ * (2 : ℝ) ^ α) ^ 2 *
        ∑' z : Fin d → ℤ,
          (1 + (latticeDistance d 0 z : ℝ)) ^ (-((2 : ℝ) * α)) := by
  have hα_real : (d : ℝ) < 2 * (α : ℝ) := by exact_mod_cast hαd
  set C := max 1 (M ^ α)⁻¹ * (2 : ℝ) ^ α with hC_def
  have hC_pos : 0 < C :=
    mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
      (pow_pos (by norm_num) α)
  have hC_sq_nn : (0 : ℝ) ≤ C ^ 2 := sq_nonneg _
  set f : (Fin d → ℤ) → ℝ := fun z =>
      1 / (1 + (M * (latticeDistance d x z : ℝ)) ^ α) *
        (1 / (1 + (M * (latticeDistance d y z : ℝ)) ^ α)) with hf_def
  set g : (Fin d → ℤ) → ℝ := fun z =>
      (1 + (latticeDistance d x z : ℝ)) ^ (-(α : ℝ)) *
        (1 + (latticeDistance d y z : ℝ)) ^ (-(α : ℝ)) with hg_def
  -- Pointwise nonneg of `f`.
  have h_f_nn : ∀ z, 0 ≤ f z := by
    intro z
    have hMt_x_nn : (0 : ℝ) ≤ M * (latticeDistance d x z : ℝ) := by
      apply mul_nonneg hM.le; exact_mod_cast Nat.zero_le _
    have hMt_y_nn : (0 : ℝ) ≤ M * (latticeDistance d y z : ℝ) := by
      apply mul_nonneg hM.le; exact_mod_cast Nat.zero_le _
    have h1x : 0 < 1 + (M * (latticeDistance d x z : ℝ)) ^ α := by
      have : 0 ≤ (M * (latticeDistance d x z : ℝ)) ^ α := pow_nonneg hMt_x_nn α
      linarith
    have h1y : 0 < 1 + (M * (latticeDistance d y z : ℝ)) ^ α := by
      have : 0 ≤ (M * (latticeDistance d y z : ℝ)) ^ α := pow_nonneg hMt_y_nn α
      linarith
    change 0 ≤
        1 / (1 + (M * (latticeDistance d x z : ℝ)) ^ α) *
          (1 / (1 + (M * (latticeDistance d y z : ℝ)) ^ α))
    exact mul_nonneg (div_nonneg (by norm_num) h1x.le)
      (div_nonneg (by norm_num) h1y.le)
  -- Pointwise nonneg of `g`.
  have h_g_nn : ∀ z, 0 ≤ g z := fun z => by
    change 0 ≤
        (1 + (latticeDistance d x z : ℝ)) ^ (-(α : ℝ)) *
          (1 + (latticeDistance d y z : ℝ)) ^ (-(α : ℝ))
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (Real.rpow_nonneg (by positivity) _)
  -- Pointwise `f z ≤ C^2 · g z`.
  have h_f_le_Cg : ∀ z, f z ≤ C ^ 2 * g z := by
    intro z
    have hd_x_nn : (0 : ℝ) ≤ (latticeDistance d x z : ℝ) := by
      exact_mod_cast Nat.zero_le _
    have hd_y_nn : (0 : ℝ) ≤ (latticeDistance d y z : ℝ) := by
      exact_mod_cast Nat.zero_le _
    have h_pair :=
      one_div_one_add_M_t_pow_pair_le_const_sq_mul_one_div_one_add_pow_pow
        (M := M) (tx := (latticeDistance d x z : ℝ))
        (ty := (latticeDistance d y z : ℝ)) (α := α) hM hd_x_nn hd_y_nn
    have hdx_eq : 1 / (1 + (latticeDistance d x z : ℝ)) ^ α =
        (1 + (latticeDistance d x z : ℝ)) ^ (-(α : ℝ)) :=
      one_div_one_add_pow_eq_rpow_neg hd_x_nn
    have hdy_eq : 1 / (1 + (latticeDistance d y z : ℝ)) ^ α =
        (1 + (latticeDistance d y z : ℝ)) ^ (-(α : ℝ)) :=
      one_div_one_add_pow_eq_rpow_neg hd_y_nn
    change f z ≤ C ^ 2 * g z
    have h_pair' :
        f z ≤ C ^ 2 *
          (1 / (1 + (latticeDistance d x z : ℝ)) ^ α *
            (1 / (1 + (latticeDistance d y z : ℝ)) ^ α)) := h_pair
    rw [hdx_eq, hdy_eq] at h_pair'
    exact h_pair'
  -- AM-GM bound on `g`.
  have h_g_le_avg : ∀ z, g z ≤
      ((1 + (latticeDistance d x z : ℝ)) ^ (-((2 : ℝ) * α)) +
       (1 + (latticeDistance d y z : ℝ)) ^ (-((2 : ℝ) * α))) / 2 := by
    intro z
    set a := (1 + (latticeDistance d x z : ℝ)) ^ (-(α : ℝ))
    set b := (1 + (latticeDistance d y z : ℝ)) ^ (-(α : ℝ))
    have ha2 : a ^ 2 = (1 + (latticeDistance d x z : ℝ)) ^ (-((2 : ℝ) * α)) := by
      simp only [a]
      rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]
      congr 1; ring
    have hb2 : b ^ 2 = (1 + (latticeDistance d y z : ℝ)) ^ (-((2 : ℝ) * α)) := by
      simp only [b]
      rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]
      congr 1; ring
    change a * b ≤ _
    nlinarith [sq_nonneg (a - b), ha2, hb2]
  -- Summability of the AM-GM bound; uses `summable_pow_neg_translate` with
  -- exponent `2α`.
  have hSx_2α : Summable
      (fun z => (1 + (latticeDistance d x z : ℝ)) ^ (-((2 : ℝ) * α))) := by
    have hβ : (d : ℝ) < (2 : ℝ) * α := hα_real
    -- need (d : ℝ) < 2 * α to apply summable_pow_neg_translate with γ = 2α
    have hγ : (d : ℝ) < (2 : ℝ) * α := hβ
    -- summable_pow_neg_translate expects (d : ℝ) < γ; we want γ = 2α, but
    -- existing lemma only guarantees summability when γ > d (which we already
    -- have through 2α > d).
    -- We strengthen this if needed: assume hγ ≥ hα_real conservatively (true).
    -- But we actually need 2α > d which is hα_real itself.
    -- However `summable_pow_neg_translate` uses γ, not 2α specifically.
    -- We apply with γ = 2α:
    exact summable_pow_neg_translate (γ := (2 : ℝ) * α) d x hγ
  have hSy_2α : Summable
      (fun z => (1 + (latticeDistance d y z : ℝ)) ^ (-((2 : ℝ) * α))) :=
    summable_pow_neg_translate (γ := (2 : ℝ) * α) d y hα_real
  have h_avg_summable : Summable (fun z =>
      ((1 + (latticeDistance d x z : ℝ)) ^ (-((2 : ℝ) * α)) +
       (1 + (latticeDistance d y z : ℝ)) ^ (-((2 : ℝ) * α))) / 2) :=
    (hSx_2α.add hSy_2α).div_const 2
  -- Summability of `g` by comparison with the AM-GM bound.
  have h_g_summable : Summable g :=
    Summable.of_nonneg_of_le h_g_nn h_g_le_avg h_avg_summable
  -- Summability of `C^2 · g`.
  have h_Cg_summable : Summable (fun z => C ^ 2 * g z) :=
    h_g_summable.mul_left _
  -- Summability of `f` by comparison with `C^2 · g`.
  have h_f_summable : Summable f :=
    Summable.of_nonneg_of_le h_f_nn h_f_le_Cg h_Cg_summable
  -- The existing HLS pair-sum bound.
  have h_existing :=
    tsum_pow_neg_conv_le_const (α := (α : ℝ)) d hα_real x y
  -- Final chain.
  calc ∑' z, f z
      ≤ ∑' z, C ^ 2 * g z := h_f_summable.tsum_le_tsum h_f_le_Cg h_Cg_summable
    _ = C ^ 2 * ∑' z, g z := tsum_mul_left
    _ ≤ C ^ 2 *
          ∑' z, (1 + (latticeDistance d 0 z : ℝ)) ^ (-((2 : ℝ) * α)) :=
        mul_le_mul_of_nonneg_left h_existing hC_sq_nn

/-- **Discrete HLS PseudoMass convolution constant** (Step 119 plan Step 5.5c
existential constant form).

For `d, α : ℕ` with `d < 2α`, there exists a positive constant `K` such that
for all `M > 0` and `x, y : Fin d → ℤ`:
```
∑_z 1/(1+(M·d(x,z))^α) · 1/(1+(M·d(y,z))^α)
  ≤ (max(1, (M^α)⁻¹) · 2^α)² · K.
```

This packages `tsum_pseudoMass_pair_product_le_const_pow_M` with the explicit
positive witness `K = ∑_z (1 + d(0, z))^(-(2α : ℝ))`, paralleling the
real-α `discrete_hls_convolution_constant` (`IsingModel/PolyDecay.lean:254`).
Convenient interface for the GJ §17.5 Lemma 17.5.2 derivative-bound pipeline,
since the geometric-decay structure of `K` is irrelevant for downstream
algebra; only the existential positive bound matters.

**Reference:** Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.5, p. 312. -/
theorem discrete_hls_pseudoMass_convolution_constant
    (d α : ℕ) (hαd : d < 2 * α) :
    ∃ K : ℝ, 0 < K ∧
      ∀ {M : ℝ} (_ : 0 < M) (x y : Fin d → ℤ),
        ∑' z : Fin d → ℤ,
            1 / (1 + (M * (latticeDistance d x z : ℝ)) ^ α) *
            (1 / (1 + (M * (latticeDistance d y z : ℝ)) ^ α)) ≤
          (max 1 (M ^ α)⁻¹ * (2 : ℝ) ^ α) ^ 2 * K := by
  have hα_real : (d : ℝ) < 2 * (α : ℝ) := by exact_mod_cast hαd
  refine ⟨∑' z : Fin d → ℤ,
            (1 + (latticeDistance d 0 z : ℝ)) ^ (-((2 : ℝ) * α)), ?_, ?_⟩
  · -- The corner sum is positive: nonzero at z = 0 (value 1).
    exact (summable_pow_neg_latticeDistance d hα_real).tsum_pos
      (fun z => Real.rpow_nonneg (by positivity) _)
      (0 : Fin d → ℤ)
      (by simp [latticeDistance])
  · intro M hM x y
    exact tsum_pseudoMass_pair_product_le_const_pow_M d hαd hM x y

end IsingModel

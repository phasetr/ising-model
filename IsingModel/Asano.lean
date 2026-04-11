import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Powerset

/-!
# Multilinear polynomials and Asano contraction

A multilinear polynomial over `ℂ` with variables indexed by `ι` is
a function `Finset ι → ℂ` giving the coefficient of each monomial `∏_{i ∈ X} z_i`.

The Asano contraction merges two variables by keeping only the "both present"
and "both absent" parts.

Reference: Friedli–Velenik, §3.7, pp. 122–127.
-/

namespace IsingModel

open Finset Complex

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Multilinear polynomials -/

/-- A multilinear polynomial over `ℂ` with variables indexed by `ι`.
The coefficient `p X` corresponds to the monomial `∏_{i ∈ X} z_i`. -/
abbrev MultilinPoly (ι : Type*) [Fintype ι] := Finset ι → ℂ

/-- Evaluate a multilinear polynomial at `z : ι → ℂ`. -/
noncomputable def MultilinPoly.eval (p : MultilinPoly ι) (z : ι → ℂ) : ℂ :=
  ∑ X : Finset ι, p X * ∏ i ∈ X, z i

/-- The constant polynomial `1`. -/
def MultilinPoly.one : MultilinPoly ι := fun X => if X = ∅ then 1 else 0

/-- Multiply two multilinear polynomials on disjoint variable sets.
Given `p : MultilinPoly ι₁` and `q : MultilinPoly ι₂`,
the product is a polynomial on `ι₁ ⊕ ι₂`. -/
noncomputable def MultilinPoly.disjointMul {ι₁ ι₂ : Type*}
    [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (p : MultilinPoly ι₁) (q : MultilinPoly ι₂) : MultilinPoly (ι₁ ⊕ ι₂) :=
  fun X => p (X.preimage Sum.inl (by intro a b _ _ h; exact Sum.inl_injective h)) *
           q (X.preimage Sum.inr (by intro a b _ _ h; exact Sum.inr_injective h))

/-! ## Asano contraction -/

/-- Asano contraction: given a polynomial `p` on `ι` and two distinct variables
`i, j : ι`, contract `j` into `i`. The result is a polynomial on `ι` that
does not depend on `j`.

Mathematically: write `P = P_{--} z_i z_j + P_{+-} z_j + P_{-+} z_i + P_{++}`.
The contraction is `P_{--} z_i + P_{++}`.

In terms of coefficients:
- For `X` with `i ∈ X`: `(contract p i j)(X) = p(X ∪ {j})` (the `P_{--}` part)
- For `X` with `i ∉ X`: `(contract p i j)(X) = p(X)` (the `P_{++}` part)
- For `X` with `j ∈ X`: `(contract p i j)(X) = 0` (contracted variable is eliminated)

Reference: Friedli–Velenik, pp. 123–124. -/
def MultilinPoly.asanoContract (p : MultilinPoly ι) (i j : ι) (_hij : i ≠ j) :
    MultilinPoly ι :=
  fun X =>
    if j ∈ X then 0
    else if i ∈ X then p (insert j X)
    else p X

/-! ## Asano contraction preserves non-vanishing -/

/-- If an affine function `α * w + β` does not vanish on the open unit disk,
then `‖α‖ ≤ ‖β‖`. Proof: if `‖α‖ > ‖β‖`, the zero `w = -β/α` lies inside the disk. -/
private lemma affine_norm_le (α β : ℂ) (h : ∀ w : ℂ, ‖w‖ < 1 → α * w + β ≠ 0) :
    ‖α‖ ≤ ‖β‖ := by
  by_contra hlt
  push_neg at hlt
  have hα : α ≠ 0 := by
    intro h0; simp [h0] at hlt; linarith [norm_nonneg β]
  exact h (-β / α)
    (by rwa [norm_div, norm_neg, div_lt_one (norm_pos_iff.mpr hα)])
    (by have := mul_div_cancel₀ β hα; linear_combination -this)

/-- Parallelogram law for `Complex.normSq`. -/
private lemma normSq_parallelogram (x y : ℂ) :
    normSq (x + y) + normSq (x - y) = 2 * (normSq x + normSq y) := by
  simp only [normSq_apply, add_re, add_im, sub_re, sub_im]; ring

/-- A linear function `s * x + t` that is `≥ 0` for all `x ∈ [0, 1)` satisfies `s + t ≥ 0`.
Used to extract norm bounds from polydisk non-vanishing. -/
private lemma linear_nonneg_on_Ico (s t : ℝ) (ht : 0 ≤ t)
    (h : ∀ x : ℝ, 0 ≤ x → x < 1 → 0 ≤ s * x + t) :
    0 ≤ s + t := by
  by_contra hlt
  push_neg at hlt
  have hs : s < 0 := by nlinarith [h 0 le_rfl one_pos]
  have h2s : (0 : ℝ) < 2 * -s := by linarith
  have h2s_ne : (2 : ℝ) * -s ≠ 0 := ne_of_gt h2s
  have hx_nn : (0 : ℝ) ≤ (-s + t) / (2 * -s) := div_nonneg (by linarith) (by linarith)
  have hx_lt : (-s + t) / (2 * -s) < 1 := by rw [div_lt_one h2s]; linarith
  have hval := h _ hx_nn hx_lt
  have hdiv : (-s + t) / (2 * -s) * (2 * -s) = -s + t := div_mul_cancel₀ _ h2s_ne
  nlinarith [hdiv]

/-- Bilinear non-vanishing lemma: if `f(z,w) = azw + bw + cz + d` does not vanish
on the open unit bidisk `|z|,|w| < 1`, then `az + d` does not vanish on `|z| < 1`.
This is the algebraic core of Asano contraction.

The proof shows `normSq d ≥ normSq a` by combining norm bounds from the z- and
w-directions via the parallelogram law. Then `az₀ + d = 0` would require
`‖z₀‖ = ‖d/a‖ ≥ 1`, contradicting `‖z₀‖ < 1`.

Reference: Friedli–Velenik, Proposition 3.44 (algebraic core). -/
theorem bilinear_nonvanishing (a b c d : ℂ)
    (hf : ∀ z w : ℂ, ‖z‖ < 1 → ‖w‖ < 1 → a * z * w + b * w + c * z + d ≠ 0)
    (z : ℂ) (hz : ‖z‖ < 1) :
    a * z + d ≠ 0 := by
  have hd : d ≠ 0 := by intro hd; exact hf 0 0 (by simp) (by simp) (by simp [hd])
  by_cases ha : a = 0; · simp [ha, hd]
  -- Key claim: ‖a‖ ≤ ‖d‖ (then az+d=0 → ‖z‖=‖d/a‖≥1, contradiction)
  suffices hda : ‖a‖ ≤ ‖d‖ by
    intro heq
    have h1 : a * z = -d := by linear_combination heq
    have h2 : z = -d / a := by
      rw [eq_div_iff ha]; rw [mul_comm]; exact h1
    have h3 : ‖z‖ = ‖d‖ / ‖a‖ := by rw [h2, norm_div, norm_neg]
    have ha_pos : (0 : ℝ) < ‖a‖ := norm_pos_iff.mpr ha
    rw [h3] at hz
    exact not_lt.mpr (le_div_iff₀ ha_pos |>.mpr (by linarith)) hz
  -- Proof of ‖a‖ ≤ ‖d‖ via normSq a ≤ normSq d, then sqrt monotonicity.
  -- Step A: normSq(az'+b) ≤ normSq(cz'+d) for |z'| < 1
  have norm_to_normSq : ∀ x y : ℂ, ‖x‖ ≤ ‖y‖ → normSq x ≤ normSq y := by
    intro x y h
    have h2 := mul_self_le_mul_self (norm_nonneg x) h
    rwa [show ‖x‖ * ‖x‖ = normSq x from by rw [Complex.normSq_eq_norm_sq]; ring,
         show ‖y‖ * ‖y‖ = normSq y from by rw [Complex.normSq_eq_norm_sq]; ring] at h2
  have hznsq : ∀ z' : ℂ, ‖z'‖ < 1 → normSq (a * z' + b) ≤ normSq (c * z' + d) := by
    intro z' hz'
    exact norm_to_normSq _ _ (affine_norm_le _ _ (fun w hw habs =>
      hf z' w hz' hw (by linear_combination habs)))
  -- Step B: normSq(aw+c) ≤ normSq(bw+d) for |w| < 1
  have hwnsq : ∀ w : ℂ, ‖w‖ < 1 → normSq (a * w + c) ≤ normSq (b * w + d) := by
    intro w hw
    exact norm_to_normSq _ _ (affine_norm_le _ _ (fun z' hz' habs =>
      hf z' w hz' hw (by linear_combination habs)))
  -- Step C: Parallelogram identity for normSq
  have para_id : ∀ (α β : ℂ) (r : ℝ),
      normSq (α * ↑r + β) + normSq (α * ↑(-r) + β) =
      2 * (normSq α * r ^ 2 + normSq β) := by
    intro α β r
    simp only [normSq_apply, mul_re, mul_im, add_re, add_im,
      ofReal_re, ofReal_im, ofReal_neg, neg_re, neg_im,
      mul_zero, sub_zero, zero_mul, add_zero, neg_zero, mul_neg, neg_mul]
    ring
  -- Step D: norm of real cast
  have norm_real_lt : ∀ r : ℝ, 0 ≤ r → r < 1 → ‖(r : ℂ)‖ < 1 := by
    intro r hr0 hr1
    have : ‖(r : ℂ)‖ = r := by
      rw [norm_real, Real.norm_of_nonneg hr0]
    linarith
  have norm_neg_real_lt : ∀ r : ℝ, 0 ≤ r → r < 1 → ‖((-r : ℝ) : ℂ)‖ < 1 := by
    intro r hr0 hr1
    rw [ofReal_neg, norm_neg]; exact norm_real_lt r hr0 hr1
  -- Step E: Average z'=r, z'=-r: normSq a * r² + normSq b ≤ normSq c * r² + normSq d
  have havg_z : ∀ r : ℝ, 0 ≤ r → r < 1 →
      normSq a * r ^ 2 + normSq b ≤ normSq c * r ^ 2 + normSq d := by
    intro r hr0 hr1
    nlinarith [hznsq (↑r) (norm_real_lt r hr0 hr1), hznsq (↑(-r : ℝ)) (norm_neg_real_lt r hr0 hr1),
      para_id a b r, para_id c d r]
  -- Step F: Average w=r, w=-r: normSq a * r² + normSq c ≤ normSq b * r² + normSq d
  have havg_w : ∀ r : ℝ, 0 ≤ r → r < 1 →
      normSq a * r ^ 2 + normSq c ≤ normSq b * r ^ 2 + normSq d := by
    intro r hr0 hr1
    nlinarith [hwnsq (↑r) (norm_real_lt r hr0 hr1), hwnsq (↑(-r : ℝ)) (norm_neg_real_lt r hr0 hr1),
      para_id a c r, para_id b d r]
  -- Step G: Add havg_z + havg_w → combined inequality in r²
  -- havg_z + havg_w gives:
  -- (normSq b + normSq c - 2*normSq a)*r² + (2*normSq d - normSq b - normSq c) ≥ 0
  have hcomb : ∀ r : ℝ, 0 ≤ r → r < 1 →
      0 ≤ (normSq b + normSq c - 2 * normSq a) * r ^ 2 +
      (2 * normSq d - normSq b - normSq c) := by
    intro r hr0 hr1; nlinarith [havg_z r hr0 hr1, havg_w r hr0 hr1]
  -- At r=0: 2*normSq d - normSq b - normSq c ≥ 0
  have ht_nn : 0 ≤ 2 * normSq d - normSq b - normSq c := by
    nlinarith [hcomb 0 le_rfl one_pos]
  -- linear_nonneg_on_Ico with x = r²: for x ∈ [0,1), s*x + t ≥ 0
  -- s + t = (normSq b + normSq c - 2*normSq a) + (2*normSq d - normSq b - normSq c)
  --       = 2*(normSq d - normSq a)
  have hlin := linear_nonneg_on_Ico _ _ ht_nn (fun x hx0 hx1 => by
    have hsqrt_nn := Real.sqrt_nonneg x
    have hsqrt_lt : Real.sqrt x < 1 := by
      rw [← Real.sqrt_one]; exact Real.sqrt_lt_sqrt hx0 hx1
    have := hcomb (Real.sqrt x) hsqrt_nn hsqrt_lt
    rwa [Real.sq_sqrt hx0] at this)
  -- hlin gives: normSq a ≤ normSq d. Convert to ‖a‖ ≤ ‖d‖.
  have hnsq : ‖a‖ ^ 2 ≤ ‖d‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]; nlinarith [hlin]
  calc ‖a‖ = Real.sqrt (‖a‖ ^ 2) := (Real.sqrt_sq (norm_nonneg a)).symm
    _ ≤ Real.sqrt (‖d‖ ^ 2) := Real.sqrt_le_sqrt hnsq
    _ = ‖d‖ := Real.sqrt_sq (norm_nonneg d)

/-- Key property: Asano contraction preserves non-vanishing on the open unit polydisk.

Write `P = P_{--} z_i z_j + P_{+-} z_j + P_{-+} z_i + P_{++}`.
The contraction is `Q(z) = P_{--}(z) z_i + P_{++}(z)`.
If `Q(z₀) = 0` for some `z₀` with `|z₀_k| < 1 ∀k`, then
`z₀_i = -P_{++}/P_{--}`. But `P(z₀_with_j=w) = P_{--} z₀_i w + P_{+-} w + P_{-+} z₀_i + P_{++}`
is linear in `w`, and vanishes at `w = -(P_{-+} z₀_i + P_{++})/(P_{--} z₀_i + P_{+-})`.
The hypothesis says this `w` must have `|w| ≥ 1`. But by algebraic manipulation,
`|w| < 1` leads to a contradiction. -/
theorem MultilinPoly.asanoContract_nonvanishing (p : MultilinPoly ι) (i j : ι) (hij : i ≠ j)
    (hp : ∀ z : ι → ℂ, (∀ k, ‖z k‖ < 1) → p.eval z ≠ 0) :
    ∀ z : ι → ℂ, (∀ k, ‖z k‖ < 1) → (p.asanoContract i j hij).eval z ≠ 0 := by
  intro z hz
  -- Define the bilinear evaluation F(u,w) = p.eval(z[i→u, j→w])
  -- Since p is multilinear, F(u,w) = a*u*w + b*w + c*u + d
  -- and the contraction's eval Q(z) = a*(z i) + d.
  -- Define the four coefficients:
  let a := ∑ X : Finset ι, if i ∈ X ∧ j ∈ X then p X * ∏ k ∈ X.erase i |>.erase j, z k else 0
  let b := ∑ X : Finset ι, if i ∉ X ∧ j ∈ X then p X * ∏ k ∈ X.erase j, z k else 0
  let c := ∑ X : Finset ι, if i ∈ X ∧ j ∉ X then p X * ∏ k ∈ X.erase i, z k else 0
  let d := ∑ X : Finset ι, if i ∉ X ∧ j ∉ X then p X * ∏ k ∈ X, z k else 0
  -- Key identities (Finset sum decomposition; proof sketch in doc comment above)
  have hQ : (p.asanoContract i j hij).eval z = a * z i + d := by sorry
  have hF : ∀ u w : ℂ,
      p.eval (Function.update (Function.update z j w) i u) =
      a * u * w + b * w + c * u + d := by sorry
  /-  -- Helper: product decomposition for Function.update at i and j
  have prod_upd : ∀ (X : Finset ι) (u w : ℂ),
      ∏ k ∈ X, Function.update (Function.update z j w) i u k =
      (if i ∈ X then u else 1) * (if j ∈ X then w else 1) *
      ∏ k ∈ (X.erase i).erase j, z k := by
    intro X u w
    by_cases hi : i ∈ X <;> by_cases hj : j ∈ X <;> simp only [hi, hj, ite_true, ite_false,
        one_mul, mul_one]
    · -- i ∈ X, j ∈ X
      rw [← Finset.mul_prod_erase X _ hi, Function.update_self]
      congr 1
      have hj' : j ∈ X.erase i := Finset.mem_erase.mpr ⟨hij.symm, hj⟩
      rw [← Finset.mul_prod_erase _ _ hj', Function.update_of_ne hij.symm,
        Function.update_self]
      congr 1
      exact Finset.prod_congr rfl (fun k hk => by
        simp [Finset.mem_erase] at hk
        rw [Function.update_of_ne hk.1.1.symm, Function.update_of_ne hk.1.2])
    · -- i ∈ X, j ∉ X
      rw [← Finset.mul_prod_erase X _ hi, Function.update_self]
      congr 1
      have : (X.erase i).erase j = X.erase i := by
        rw [Finset.erase_eq_of_not_mem (mt Finset.mem_of_mem_erase hj)]
      rw [this]
      exact Finset.prod_congr rfl (fun k hk => by
        have hki : k ≠ i := Finset.ne_of_mem_erase hk
        have hkj : k ≠ j := fun h => hj (h ▸ Finset.mem_of_mem_erase hk)
        rw [Function.update_of_ne hki.symm, Function.update_of_ne hkj])
    · -- i ∉ X, j ∈ X
      have : X.erase i = X := Finset.erase_eq_of_not_mem hi
      rw [this, ← Finset.mul_prod_erase X _ hj]
      congr 1
      · rw [Function.update_of_ne (Ne.symm hij), Function.update_self]
      · exact Finset.prod_congr rfl (fun k hk => by
          have hkj : k ≠ j := Finset.ne_of_mem_erase hk
          have hki : k ≠ i := fun h => hi (h ▸ Finset.mem_of_mem_erase hk)
          rw [Function.update_of_ne hki.symm, Function.update_of_ne hkj])
    · -- i ∉ X, j ∉ X
      have h1 : X.erase i = X := Finset.erase_eq_of_not_mem hi
      have h2 : (X.erase i).erase j = X := by rw [h1, Finset.erase_eq_of_not_mem hj]
      rw [h2]
      exact Finset.prod_congr rfl (fun k hk => by
        have hki : k ≠ i := fun h => hi (h ▸ hk)
        have hkj : k ≠ j := fun h => hj (h ▸ hk)
        rw [Function.update_of_ne hki.symm, Function.update_of_ne hkj])
  -- Key identity 2 (easier): p.eval(z[i→u,j→w]) = a*u*w + b*w + c*u + d
  have hF : ∀ u w : ℂ,
      p.eval (Function.update (Function.update z j w) i u) =
      a * u * w + b * w + c * u + d := by
    intro u w
    simp only [MultilinPoly.eval, prod_upd, a, b, c, d]
    -- Each summand: p X * [if i∈X then u else 1] * [if j∈X then w else 1] * ∏ rest
    -- Split into 4 parts by i,j membership, factor out u*w, w, u, 1
    simp only [← Finset.sum_add_distrib]
    have : ∀ X : Finset ι,
        p X * ((if i ∈ X then u else 1) * (if j ∈ X then w else 1) *
        ∏ k ∈ (X.erase i).erase j, z k) =
        (if i ∈ X ∧ j ∈ X then p X * ∏ k ∈ (X.erase i).erase j, z k else 0) * (u * w) +
        (if i ∉ X ∧ j ∈ X then p X * ∏ k ∈ X.erase j, z k else 0) * w +
        (if i ∈ X ∧ j ∉ X then p X * ∏ k ∈ X.erase i, z k else 0) * u +
        (if i ∉ X ∧ j ∉ X then p X * ∏ k ∈ X, z k else 0) := by
      intro X
      by_cases hi : i ∈ X <;> by_cases hj : j ∈ X <;>
        simp [hi, hj, Finset.erase_eq_of_not_mem, *] <;> ring
    simp_rw [this, Finset.sum_add_distrib, ← Finset.sum_mul]
    ring
  -- Key identity 1: eval of contraction = a * z i + d
  -- Use the involution e(X) = if j∈X then X.erase j else insert j X
  have hQ : (p.asanoContract i j hij).eval z = a * z i + d := by
    -- Q(z) = ∑_X q(X) * ∏ z. Split: j∈X vanishes, rest = (i∈X,j∉X) + (i∉X,j∉X)
    simp only [MultilinPoly.eval, MultilinPoly.asanoContract]
    have split : ∀ X : Finset ι,
        (if j ∈ X then (0:ℂ) else if i ∈ X then p (insert j X) else p X) * ∏ k ∈ X, z k =
        (if i ∈ X ∧ j ∉ X then p (insert j X) * ∏ k ∈ X, z k else 0) +
        (if i ∉ X ∧ j ∉ X then p X * ∏ k ∈ X, z k else 0) := by
      intro X; by_cases hj : j ∈ X <;> by_cases hi : i ∈ X <;> simp [hi, hj]
    simp_rw [split, Finset.sum_add_distrib]
    congr 1
    -- ∑_X [if i∈X ∧ j∉X then p(insert j X)*∏ z else 0] = a * z i
    -- = ∑_Y [if i∈Y ∧ j∈Y then p Y * ∏_{(erase i)(erase j)} z else 0] * z i
    simp only [a, Finset.mul_sum, mul_ite, mul_zero]
    -- Use the involution to reindex the LHS
    let e : Finset ι ≃ Finset ι := ⟨
      fun X => if j ∈ X then X.erase j else insert j X,
      fun X => if j ∈ X then X.erase j else insert j X,
      fun X => by by_cases hj : j ∈ X <;> simp [hj, Finset.insert_erase, Finset.erase_insert],
      fun X => by by_cases hj : j ∈ X <;> simp [hj, Finset.insert_erase, Finset.erase_insert]⟩
    rw [show (∑ X : Finset ι, if i ∈ X ∧ j ∉ X then
        p (insert j X) * ∏ k ∈ X, z k else 0) =
      ∑ Y : Finset ι, if i ∈ Y ∧ j ∈ Y then
        p Y * ∏ k ∈ Y.erase j, z k else 0 from by
      rw [← Fintype.sum_equiv e]
      · apply Finset.sum_congr rfl; intro Y _
        by_cases hj : j ∈ Y <;> simp only [e, Equiv.coe_fn_mk, hj, ite_true, ite_false]
        · -- j ∈ Y: e(Y) = Y.erase j. Target: if i∈(Y.erase j) ∧ j∉(Y.erase j) then ...
          simp only [Finset.not_mem_erase, and_true]
          by_cases hi : i ∈ Y
          · simp [Finset.mem_erase.mpr ⟨hij, hi⟩, hi, Finset.insert_erase hj]
          · simp [show ¬(i ∈ Y.erase j) from mt Finset.mem_of_mem_erase hi, hi]
        · -- j ∉ Y: both sides are 0
          simp [hj, show ¬(j ∈ insert j Y) = False from by simp]
          intro hi; exact absurd (Finset.mem_insert_self j Y) (by push_neg; exact hj)
      · intro Y; rfl]
    -- Now show: ∑_Y [if i∈Y ∧ j∈Y then p Y * ∏_{Y.erase j} z else 0]
    --         = ∑_Y [if i∈Y ∧ j∈Y then p Y * ∏_{(Y.erase i).erase j} z * z i else 0]
    -- These are equal because ∏_{Y.erase j} z = z i * ∏_{(Y.erase j).erase i} z
    -- and (Y.erase j).erase i = (Y.erase i).erase j
    apply Finset.sum_congr rfl; intro Y _
    split_ifs with h
    · -- i ∈ Y, j ∈ Y
      have hi_ej : i ∈ Y.erase j := Finset.mem_erase.mpr ⟨hij, h.1⟩
      rw [← Finset.mul_prod_erase _ z hi_ej]
      have : (Y.erase j).erase i = (Y.erase i).erase j := by
        ext x; simp [Finset.mem_erase]; tauto
      rw [this]; ring
    · rfl  -/
  -- Apply bilinear_nonvanishing
  rw [hQ]
  apply bilinear_nonvanishing a b c d
  · intro u w hu hw
    rw [← hF]
    exact hp _ (fun k => by
      simp only [Function.update]
      split_ifs with hki hkj
      · subst hki; exact hu
      · subst hkj; exact hw
      · exact hz k)
  · exact hz i

/-! ## Base case: single edge -/

/-- The partition polynomial for a single edge `{i, j}` with coupling `t = e^{-2β}`:
`P(z_i, z_j) = z_i z_j + t(z_i + z_j) + 1`
where `0 ≤ t < 1`. -/
def singleEdgePoly (i j : ι) (t : ℝ) : MultilinPoly ι :=
  fun X =>
    if X = {i, j} then 1
    else if X = {i} then ↑t
    else if X = {j} then ↑t
    else if X = ∅ then 1
    else 0

/-- `‖tz + 1‖ > ‖z + t‖` when `0 ≤ t < 1` and `‖z‖ < 1`.
This is the norm inequality underlying the Möbius transformation property. -/
theorem norm_tz_add_one_gt (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (z : ℂ) (hz : ‖z‖ < 1) :
    ‖z + ↑t‖ < ‖↑t * z + 1‖ := by
  -- ‖-(tz+1)/(z+t)‖ = ‖tz+1‖/‖z+t‖
  -- Need: ‖tz+1‖ > ‖z+t‖
  -- ‖tz+1‖² - ‖z+t‖² = (t²|z|²+2t Re z+1) - (|z|²+2t Re z+t²)
  --                    = (t²-1)|z|² + (1-t²) = (1-t²)(1-|z|²) > 0
  -- ‖-(tz+1)/(z+t)‖ = ‖tz+1‖/‖z+t‖ > 1 ⟺ ‖tz+1‖ > ‖z+t‖
  -- Suffices: Complex.normSq(tz+1) > Complex.normSq(z+t)
  -- because normSq(tz+1) - normSq(z+t) = (1-t²)(1-normSq z) > 0
  -- normSq(tz+1) - normSq(z+t) = (1-t²)(1-normSq z) > 0
  -- Then ‖tz+1‖ > ‖z+t‖ → ‖-(tz+1)/(z+t)‖ > 1
  -- Show ‖z+t‖² < ‖tz+1‖², then convert to norm inequality.
  -- normSq(tz+1) - normSq(z+t) = (1-t²)(1-normSq z) > 0
  have hz_re_im : z.re ^ 2 + z.im ^ 2 < 1 := by
    have h1 : Complex.normSq z = ‖z‖ ^ 2 := Complex.normSq_eq_norm_sq z
    have h2 : Complex.normSq z = z.re * z.re + z.im * z.im := Complex.normSq_apply z
    have h3 : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z]
    nlinarith [sq_nonneg z.re, sq_nonneg z.im]
  -- normSq(z+t) < normSq(tz+1)
  have hnsq : (z.re + t) ^ 2 + z.im ^ 2 < (t * z.re + 1) ^ 2 + (t * z.im) ^ 2 := by
    -- (t*z.re+1)²+(t*z.im)² - (z.re+t)²-z.im² = (1-t²)(1-(z.re²+z.im²))
    -- Difference = (1-t²)(1-(z.re²+z.im²)) > 0
    have h_diff : (t * z.re + 1) ^ 2 + (t * z.im) ^ 2 - ((z.re + t) ^ 2 + z.im ^ 2) =
        (1 - t ^ 2) * (1 - (z.re ^ 2 + z.im ^ 2)) := by ring
    have : 0 < (1 - t ^ 2) := by nlinarith [sq_nonneg t]
    have : 0 < (1 - (z.re ^ 2 + z.im ^ 2)) := by linarith
    nlinarith [mul_pos ‹0 < 1 - t ^ 2› ‹0 < 1 - (z.re ^ 2 + z.im ^ 2)›]
  -- Convert to norm: ‖z+t‖ < ‖tz+1‖
  -- ‖z+t‖² < ‖tz+1‖² from hnsq + normSq connection
  have hn1 : Complex.normSq (z + ↑t) = (z.re + t) ^ 2 + z.im ^ 2 := by
    simp [Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im]; ring
  have hn2 : Complex.normSq (↑t * z + 1) = (t * z.re + 1) ^ 2 + (t * z.im) ^ 2 := by
    simp [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.one_im]; ring
  have hnsq' : Complex.normSq (z + ↑t) < Complex.normSq (↑t * z + 1) := by
    rw [hn1, hn2]; exact hnsq
  -- normSq < → norm <
  have h_sq : ‖z + ↑t‖ ^ 2 < ‖↑t * z + 1‖ ^ 2 := by
    rwa [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  have := abs_lt_of_sq_lt_sq h_sq (norm_nonneg _)
  rwa [abs_of_nonneg (norm_nonneg _)] at this

/-- The single-edge polynomial does not vanish on the open unit polydisk.
If `P(z_i, z_j) = 0`, then `z_i = -(tz_j+1)/(z_j+t)`, but the Möbius
transformation maps `|z_j| < 1` to `|z_i| > 1`, contradiction. -/
theorem singleEdgePoly_nonvanishing (i j : ι) (hij : i ≠ j)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (z : ι → ℂ) (hz : ∀ k, ‖z k‖ < 1) :
    (singleEdgePoly i j t).eval z ≠ 0 := by
  intro hp
  -- Step 1: eval of singleEdgePoly = z_i * z_j + t*(z_i + z_j) + 1
  have heval : (singleEdgePoly i j t).eval z =
      z i * z j + ↑t * z i + ↑t * z j + 1 := by
    simp only [MultilinPoly.eval, singleEdgePoly]
    -- Decompose coefficient: nested if → sum of 4 indicators
    have hne_ij_i : ({i, j} : Finset ι) ≠ {i} := by
      intro h
      have : j ∈ ({i, j} : Finset ι) := by simp
      rw [h, Finset.mem_singleton] at this
      exact hij this.symm
    have hne_ij_j : ({i, j} : Finset ι) ≠ {j} := by
      intro h
      have : i ∈ ({i, j} : Finset ι) := by simp
      rw [h, Finset.mem_singleton] at this
      exact hij this
    have hne_i_j : ({i} : Finset ι) ≠ {j} := by
      intro h
      have : i ∈ ({i} : Finset ι) := by simp
      rw [h, Finset.mem_singleton] at this
      exact hij this
    conv_lhs =>
      arg 2; ext X
      rw [show (if X = {i, j} then (1 : ℂ) else if X = {i} then ↑t
           else if X = {j} then ↑t else if X = ∅ then 1 else 0) =
          (if X = {i, j} then 1 else 0) + (if X = {i} then ↑t else 0) +
          (if X = {j} then ↑t else 0) + (if X = ∅ then 1 else 0) from by
        by_cases h1 : X = {i, j}
        · subst h1; simp [hne_ij_i, hne_ij_j]
        · by_cases h2 : X = {i}
          · subst h2; simp [h1, hne_i_j]
          · by_cases h3 : X = {j}
            · subst h3; simp [h1, h2]
            · simp [h1, h2, h3]]
    simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, one_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      Finset.prod_pair hij, Finset.prod_singleton, Finset.prod_empty]
  -- Step 2: P = 0 → z_i * (z_j + t) = -(t * z_j + 1)
  rw [heval] at hp
  have halg : z i * (z j + ↑t) = -(↑t * z j + 1) := by
    have h0 : z i * z j + ↑t * z i + ↑t * z j + 1 = 0 := hp
    have h1 : z i * (z j + ↑t) + (↑t * z j + 1) = z i * z j + ↑t * z i + ↑t * z j + 1 := by ring
    linear_combination h0
  -- Step 3: take norms. ‖z_i‖ * ‖z_j + t‖ = ‖t*z_j + 1‖
  have hnorm : ‖z i‖ * ‖z j + ↑t‖ = ‖↑t * z j + 1‖ := by
    rw [← norm_mul, halg, norm_neg]
  -- Step 4: ‖z_j + t‖ < ‖t*z_j + 1‖ by norm_tz_add_one_gt
  have hgt := norm_tz_add_one_gt t ht0 ht1 (z j) (hz j)
  -- Step 5: if ‖z_j + t‖ = 0 then ‖t*z_j+1‖ = 0, contradicting hgt
  -- if ‖z_j + t‖ > 0 then ‖z_i‖ > 1, contradicting hz i
  by_cases hzt : ‖z j + ↑t‖ = 0
  · linarith [hnorm.symm.trans (by rw [hzt, mul_zero])]
  · have hzt_pos : 0 < ‖z j + ↑t‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzt)
    have hzi : 1 < ‖z i‖ := by
      by_contra h
      push_neg at h
      -- ‖z_i‖ ≤ 1, ‖z_j+t‖ > 0
      -- ‖z_i‖ * ‖z_j+t‖ ≤ ‖z_j+t‖ < ‖tz_j+1‖ = ‖z_i‖ * ‖z_j+t‖, contradiction
      have := mul_le_mul_of_nonneg_right h (le_of_lt hzt_pos)
      linarith [hnorm]
    linarith [hz i]

/-! ## Lee-Yang circle theorem -/

/-- The Ising partition polynomial `P_E(z_V) = Σ_{X⊆V} a_E(X) ∏_{i∈X} z_i`
with coefficients in `[0,1]` and `a(∅) = a(V) = 1`.
This is the multilinear form of the partition function with `z = e^{-2h}`. -/
structure IsingPartitionPoly (ι : Type*) [Fintype ι] [DecidableEq ι] where
  /-- The underlying multilinear polynomial. -/
  poly : MultilinPoly ι
  /-- All coefficients are in `[0, 1]`. -/
  coeff_nonneg : ∀ X, 0 ≤ (poly X).re ∧ (poly X).re ≤ 1 ∧ (poly X).im = 0
  /-- Coefficient of the empty set is `1`. -/
  coeff_empty : poly ∅ = 1
  /-- Coefficient of the full set is `1`. -/
  coeff_full : poly Finset.univ = 1

/-- **Lee-Yang circle theorem**: The Ising partition polynomial does not vanish
on the open unit polydisk `{z : ‖z_i‖ < 1 ∀i}`.

Equivalently, all zeros of `Z(z)` (as a function of `z = e^{-2h}`) lie on `|z| = 1`.

Reference: Friedli–Velenik, Theorem 3.43, pp. 122–127.
Proof by induction on the edge set using Asano contraction. -/
theorem lee_yang_circle (p : IsingPartitionPoly ι)
    (z : ι → ℂ) (hz : ∀ k, ‖z k‖ < 1) :
    p.poly.eval z ≠ 0 := by
  -- Proof by induction on the edge set (the set of X with 0 < a(X) < 1
  -- and |X| = 2). Base case: single edge (singleEdgePoly_nonvanishing).
  -- Inductive step: add one edge using Asano contraction
  -- (asanoContract_nonvanishing) or factorization (disjointMul).
  sorry

end IsingModel

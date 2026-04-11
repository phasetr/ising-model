import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian

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
  push Not at hlt
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
  push Not at hlt
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
      ]
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
  -- Helper: product decomposition for Function.update at i and j
  have prod_upd : ∀ (X : Finset ι) (u w : ℂ),
      ∏ k ∈ X, Function.update (Function.update z j w) i u k =
      (if i ∈ X then u else 1) * (if j ∈ X then w else 1) *
      ∏ k ∈ (X.erase i).erase j, z k := by
    intro X u w
    have upd_rest : ∀ k, k ∈ (X.erase i).erase j →
        Function.update (Function.update z j w) i u k = z k := by
      intro k hk
      rw [Function.update_of_ne (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)),
          Function.update_of_ne (Finset.ne_of_mem_erase hk)]
    have hp := Finset.prod_congr rfl upd_rest
    by_cases hi : i ∈ X
    · by_cases hj : j ∈ X
      · simp only [hi, hj, ite_true]
        rw [← Finset.mul_prod_erase X _ hi, Function.update_self,
            ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨hij.symm, hj⟩),
            Function.update_of_ne hij.symm, Function.update_self, hp]; ring
      · simp only [hi, hj, ite_true, ite_false, mul_one]
        have hej : (X.erase i).erase j = X.erase i :=
              Finset.erase_eq_self.mpr (mt Finset.mem_of_mem_erase hj)
        rw [hej] at hp ⊢
        rw [← Finset.mul_prod_erase X _ hi, Function.update_self, hp]
    · by_cases hj : j ∈ X
      · simp only [hi, hj, ite_true, ite_false, one_mul]
        have hei : X.erase i = X := Finset.erase_eq_self.mpr hi
        rw [hei] at hp ⊢
        rw [← Finset.mul_prod_erase X _ hj,
            Function.update_of_ne (Ne.symm hij), Function.update_self, hp]
      · simp only [hi, hj, ite_false, one_mul]
        have h12 : (X.erase i).erase j = X := by
              rw [Finset.erase_eq_self.mpr hi, Finset.erase_eq_self.mpr hj]
        rw [h12] at hp ⊢; exact hp
  -- Key identity 2: p.eval(z[i→u,j→w]) = a*u*w + b*w + c*u + d
  have hF : ∀ u w : ℂ,
      p.eval (Function.update (Function.update z j w) i u) =
      a * u * w + b * w + c * u + d := by
    intro u w
    simp only [MultilinPoly.eval]
    -- Rewrite each product using prod_upd
    conv_lhs => arg 2; ext X; rw [prod_upd]
    -- Now each summand: p X * (if i∈X then u else 1) * (if j∈X then w else 1) * ∏ rest
    -- Split into 4 categories
    have decomp : ∀ X : Finset ι,
        p X * ((if i ∈ X then u else 1) * (if j ∈ X then w else 1) *
        ∏ k ∈ (X.erase i).erase j, z k) =
        (if i ∈ X ∧ j ∈ X then p X * ∏ k ∈ (X.erase i).erase j, z k else 0) * (u * w) +
        (if i ∉ X ∧ j ∈ X then p X * ∏ k ∈ (X.erase i).erase j, z k else 0) * w +
        (if i ∈ X ∧ j ∉ X then p X * ∏ k ∈ (X.erase i).erase j, z k else 0) * u +
        (if i ∉ X ∧ j ∉ X then p X * ∏ k ∈ (X.erase i).erase j, z k else 0) := by
      intro X; by_cases hi : i ∈ X <;> by_cases hj : j ∈ X <;> simp [hi, hj] <;> ring
    simp_rw [decomp, Finset.sum_add_distrib, ← Finset.sum_mul]
    -- Match with a, b, c, d definitions (they use erase differently for b, c, d cases)
    -- b: i∉X, j∈X → (X.erase i).erase j = X.erase j (since erase i is no-op)
    -- c: i∈X, j∉X → (X.erase i).erase j = X.erase i (since erase j is no-op)
    -- d: i∉X, j∉X → (X.erase i).erase j = X (both no-ops)
    have adj : ∀ X : Finset ι, i ∉ X → (X.erase i).erase j = X.erase j := by
      intro X hi'; rw [Finset.erase_eq_self.mpr hi']
    have adj2 : ∀ X : Finset ι, j ∉ X → (X.erase i).erase j = X.erase i := by
      intro X hj'; exact Finset.erase_eq_self.mpr (mt Finset.mem_of_mem_erase hj')
    have adj3 : ∀ X : Finset ι, i ∉ X → j ∉ X → (X.erase i).erase j = X := by
      intro X hi' hj'; rw [Finset.erase_eq_self.mpr hi', Finset.erase_eq_self.mpr hj']
    have hb_eq : (∑ X : Finset ι, if i ∉ X ∧ j ∈ X then
        p X * ∏ k ∈ (X.erase i).erase j, z k else 0) = b := by
      exact Finset.sum_congr rfl fun X _ => by
        split_ifs with h
        · rw [adj X h.1]
        · rfl
    have hc_eq : (∑ X : Finset ι, if i ∈ X ∧ j ∉ X then
        p X * ∏ k ∈ (X.erase i).erase j, z k else 0) = c := by
      exact Finset.sum_congr rfl fun X _ => by
        split_ifs with h
        · rw [adj2 X h.2]
        · rfl
    have hd_eq : (∑ X : Finset ι, if i ∉ X ∧ j ∉ X then
        p X * ∏ k ∈ (X.erase i).erase j, z k else 0) = d := by
      exact Finset.sum_congr rfl fun X _ => by
        split_ifs with h
        · rw [adj3 X h.1 h.2]
        · rfl
    rw [hb_eq, hc_eq, hd_eq]; ring
  -- Key identity 1: eval of contraction = a * z i + d
  have hQ : (p.asanoContract i j hij).eval z = a * z i + d := by
    simp only [MultilinPoly.eval, MultilinPoly.asanoContract]
    have lhs_split : ∀ X : Finset ι,
        (if j ∈ X then (0:ℂ) else if i ∈ X then p (insert j X) else p X) * ∏ k ∈ X, z k =
        (if i ∈ X ∧ j ∉ X then p (insert j X) * ∏ k ∈ X, z k else 0) +
        (if i ∉ X ∧ j ∉ X then p X * ∏ k ∈ X, z k else 0) := by
      intro X; by_cases hj : j ∈ X <;> by_cases hi : i ∈ X <;> simp [hi, hj]
    simp_rw [lhs_split, Finset.sum_add_distrib]
    congr 1
    · -- ∑ [if i∈X ∧ j∉X then p(insert j X)*∏ z else 0] = a * z i
      -- Reindex RHS via involution e
      simp only [a, Finset.sum_mul]
      let e : Finset ι ≃ Finset ι := ⟨
        fun X => if j ∈ X then X.erase j else insert j X,
        fun X => if j ∈ X then X.erase j else insert j X,
        fun X => by by_cases h : j ∈ X <;> simp [h, Finset.insert_erase],
        fun X => by by_cases h : j ∈ X <;> simp [h, Finset.insert_erase]⟩
      symm
      apply Fintype.sum_equiv e
      intro Y
      by_cases hjY : j ∈ Y
      · -- j ∈ Y: e(Y) = Y.erase j
        have hj_ej : j ∉ Y.erase j := fun h => absurd rfl (Finset.ne_of_mem_erase h)
        simp only [e, Equiv.coe_fn_mk, hjY, ite_true, hj_ej, not_false_eq_true, and_true]
        by_cases hiY : i ∈ Y
        · have hi_ej := Finset.mem_erase.mpr ⟨hij, hiY⟩
          simp only [hi_ej, ite_true, hiY, Finset.insert_erase hjY]
          rw [← Finset.mul_prod_erase _ z hi_ej]
          have : (Y.erase j).erase i = (Y.erase i).erase j := by
            ext x; simp [Finset.mem_erase]; tauto
          rw [this]; ring
        · simp [show ¬(i ∈ Y.erase j) from mt Finset.mem_of_mem_erase hiY, hiY]
      · -- j ∉ Y: both sides are 0
        simp only [e, Equiv.coe_fn_mk, hjY, ite_false]
        simp [hjY]
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
      push Not at h
      -- ‖z_i‖ ≤ 1, ‖z_j+t‖ > 0
      -- ‖z_i‖ * ‖z_j+t‖ ≤ ‖z_j+t‖ < ‖tz_j+1‖ = ‖z_i‖ * ‖z_j+t‖, contradiction
      have := mul_le_mul_of_nonneg_right h (le_of_lt hzt_pos)
      linarith [hnorm]
    linarith [hz i]

/-! ## Lee-Yang circle theorem (Harcos/Ruelle approach) -/

/-- The Lee-Yang polynomial for an `n × n` matrix `A`:
`f_A(z) = Σ_{S⊆[n]} (∏_{i∈S, j∉S} a_{ij}) · (∏_{k∈S} z_k)`.

When `A` is Hermitian with `|a_{ij}| ≤ 1`, this polynomial does not vanish on the
open unit polydisk. This is the key object in the Harcos/Ruelle proof of the
Lee-Yang circle theorem.

Reference: Harcos, based on Ruelle, Ann. of Math. 171 (2010), 589–603. -/
noncomputable def leeYangPoly {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    MultilinPoly (Fin n) :=
  fun S => ∏ i ∈ S, ∏ j ∈ Finset.univ \ S, A i j

/-- For a Hermitian matrix, `conj(A i j) = A j i`. -/
private lemma hermitian_conj_entry {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (i j : Fin n) :
    starRingEnd ℂ (A i j) = A j i := by
  have h := congr_fun (congr_fun hA.eq j) i
  simp only [Matrix.conjTranspose_apply, RCLike.star_def] at h
  exact h

/-- The complement of `T.map castSucc` in `Fin (m+1)` is
`{last} ∪ (univ \ T).map castSucc`. -/
private lemma complement_map_castSucc {m : ℕ} (T : Finset (Fin m)) :
    Finset.univ \ T.map ⟨Fin.castSucc, Fin.castSucc_injective m⟩ =
    insert (Fin.last m) ((Finset.univ \ T).map ⟨Fin.castSucc, Fin.castSucc_injective m⟩) := by
  ext j
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_map,
    Finset.mem_insert, Function.Embedding.coeFn_mk]
  constructor
  · intro hj
    induction j using Fin.lastCases with
    | last => left; rfl
    | cast i =>
      right
      exact ⟨i, fun hT => hj ⟨i, hT, rfl⟩, rfl⟩
  · rintro (rfl | ⟨x, hx, rfl⟩)
    · rintro ⟨y, _, hy⟩; exact absurd hy (Fin.castSucc_ne_last y)
    · rintro ⟨y, hy, hc⟩
      exact hx ((Fin.castSucc_injective m hc) ▸ hy)

/-- The complement of `insert last (T.map castSucc)` in `Fin (m+1)` is
`(univ \ T).map castSucc`. -/
private lemma complement_insert_last_map_castSucc {m : ℕ} (T : Finset (Fin m)) :
    Finset.univ \ insert (Fin.last m) (T.map ⟨Fin.castSucc, Fin.castSucc_injective m⟩) =
    (Finset.univ \ T).map ⟨Fin.castSucc, Fin.castSucc_injective m⟩ := by
  ext j
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_map, Function.Embedding.coeFn_mk]
  constructor
  · intro h
    have hne : j ≠ Fin.last m := fun heq => h (Or.inl heq)
    have hni : ¬∃ a ∈ T, a.castSucc = j := fun hex => h (Or.inr hex)
    induction j using Fin.lastCases with
    | last => exact absurd rfl hne
    | cast i => exact ⟨i, fun hi => hni ⟨i, hi, rfl⟩, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    intro h
    rcases h with heq | ⟨y, hy, hc⟩
    · exact absurd heq (Fin.castSucc_ne_last x)
    · exact hx ((Fin.castSucc_injective m hc) ▸ hy)

/-- Conjugation of Lee-Yang coefficients corresponds to taking the complement.
For Hermitian `A`: `conj(leeYangPoly A T) = leeYangPoly A (univ \ T)`. -/
private lemma leeYangPoly_conj_eq_compl {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (T : Finset (Fin n)) :
    starRingEnd ℂ (leeYangPoly A T) = leeYangPoly A (Finset.univ \ T) := by
  unfold leeYangPoly
  simp only [map_prod]
  simp_rw [hermitian_conj_entry A hA]
  rw [Finset.prod_comm]
  congr 1; ext j; congr 1
  ext x; simp

/-- Coefficient identity for `last ∉ S`: the Lee-Yang coefficient of `T.map castSucc`
factors into the submatrix coefficient times the coupling to the last row.

`leeYangPoly A (T.map cs) = leeYangPoly B T · ∏_{i∈T} A (cs i) last`

where `B = A.submatrix castSucc castSucc`. -/
private lemma leeYangPoly_coeff_notin {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (T : Finset (Fin m)) (z : Fin (m + 1) → ℂ) :
    leeYangPoly A (T.map ⟨Fin.castSucc, Fin.castSucc_injective m⟩) *
      ∏ k ∈ T.map ⟨Fin.castSucc, Fin.castSucc_injective m⟩, z k =
    leeYangPoly (A.submatrix Fin.castSucc Fin.castSucc) T *
      ∏ i ∈ T, (A (Fin.castSucc i) (Fin.last m) * z (Fin.castSucc i)) := by
  unfold leeYangPoly
  rw [Finset.prod_map, Finset.prod_map]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  congr 1; ext i
  rw [complement_map_castSucc T]
  have hlast_nmem : Fin.last m ∉
      (Finset.univ \ T).map ⟨Fin.castSucc, Fin.castSucc_injective m⟩ := by
    simp [Finset.mem_map, Fin.castSucc_ne_last]
  rw [Finset.prod_insert hlast_nmem, Finset.prod_map]
  simp only [Matrix.submatrix_apply, Function.Embedding.coeFn_mk]
  ring

/-- Coefficient identity for `last ∈ S`: the Lee-Yang coefficient of
`insert last (T.map castSucc)` factors into the submatrix coefficient times
the coupling from the last column.

`leeYangPoly A (insert last (T.map cs)) = leeYangPoly B T · ∏_{j∈univ\T} A last (cs j)` -/
private lemma leeYangPoly_coeff_in {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (T : Finset (Fin m)) :
    leeYangPoly A (insert (Fin.last m) (T.map ⟨Fin.castSucc, Fin.castSucc_injective m⟩)) =
    leeYangPoly (A.submatrix Fin.castSucc Fin.castSucc) T *
      ∏ j ∈ (Finset.univ \ T), A (Fin.last m) (Fin.castSucc j) := by
  unfold leeYangPoly
  rw [complement_insert_last_map_castSucc]
  have hlast_nmem : Fin.last m ∉
      T.map ⟨Fin.castSucc, Fin.castSucc_injective m⟩ := by
    simp [Finset.mem_map, Fin.castSucc_ne_last]
  rw [Finset.prod_insert hlast_nmem]
  rw [Finset.prod_map, Finset.prod_map]
  simp_rw [Finset.prod_map]
  simp only [Matrix.submatrix_apply, Function.Embedding.coeFn_mk]
  ring

/-- The ratio of the `z_last`-coefficient to the constant term in the Lee-Yang polynomial
is bounded by 1, by the maximum modulus principle.

Specifically, in `f_A(z) = β + z_last · α` where
`β = f_B(a·z)` and `α = Σ_{S : last ∈ S} coeff(S) · ∏_{k∈S\{last}} z_k`,
we have `‖α‖ ≤ ‖β‖` for `|z_k| < 1`.

Proof sketch (Harcos/Ruelle):
1. When `|a_{k,n}| < 1` (strictly), `β ≠ 0` on the closed polydisk
   (by induction, since `|a_k · z_k| ≤ |a_k| < 1`).
2. The ratio `g = α/β` is holomorphic on the closed polydisk.
3. On the torus `|z_k| = 1`: by the Hermitian property,
   `α = (∏ z_k) · conj(β)`, so `|α/β| = |∏ z_k| = 1`.
4. By iterated maximum modulus principle
   (`Complex.norm_le_of_forall_mem_frontier_norm_le`):
   `|α/β| ≤ 1` on the open polydisk.
5. Extend to `|a_{k,n}| ≤ 1` by continuity.

Reference: Harcos, based on Ruelle, Ann. of Math. 171 (2010), 589–603. -/
private lemma leeYangPoly_ratio_bound {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (hA : A.IsHermitian) (hbound : ∀ i j, ‖A i j‖ ≤ 1)
    (z : Fin (m + 1) → ℂ) (hz : ∀ k, ‖z k‖ < 1)
    (ih : ∀ (A' : Matrix (Fin m) (Fin m) ℂ), A'.IsHermitian →
      (∀ i j, ‖A' i j‖ ≤ 1) → ∀ z', (∀ k, ‖z' k‖ < 1) → (leeYangPoly A').eval z' ≠ 0) :
    ‖∑ S ∈ (Finset.univ : Finset (Finset (Fin (m + 1)))).filter (fun S => Fin.last m ∈ S),
        leeYangPoly A S * ∏ k ∈ S.erase (Fin.last m), z k‖ ≤
    ‖(leeYangPoly (A.submatrix Fin.castSucc Fin.castSucc)).eval
        (fun i => A (Fin.castSucc i) (Fin.last m) * z (Fin.castSucc i))‖ := by
  sorry

/-- **Harcos/Ruelle theorem**: For an `n × n` Hermitian matrix `A` with `|a_{ij}| ≤ 1`,
the Lee-Yang polynomial `f_A` does not vanish on the open unit polydisk.

Proof by induction on `n`:
- `n = 0`: `f_A = 1 ≠ 0`
- `n + 1`: Separate the last variable. Using `a_{ji} = conj(a_{ij})`, decompose
  `f_A(z) = f_B(a·z) + (∏z_k) · conj(f_B(a/conj(z)))`.
  First term ≠ 0 by induction. Ratio of second/first has modulus ≤ 1 by the
  maximum modulus principle (on |z_k| = 1, the ratio is exactly 1).

Reference: Harcos, "The Lee-Yang Circle Theorem",
  based on Ruelle, Ann. of Math. 171 (2010), 589–603. -/
theorem leeYangPoly_nonvanishing {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian)
    (hbound : ∀ i j, ‖A i j‖ ≤ 1)
    (z : Fin n → ℂ) (hz : ∀ k, ‖z k‖ < 1) :
    (leeYangPoly A).eval z ≠ 0 := by
  induction n with
  | zero =>
    -- f_A(z) = 1 ≠ 0 (Fin 0 is empty, only subset is ∅, all products are empty = 1)
    unfold MultilinPoly.eval leeYangPoly
    rw [Fintype.sum_eq_single (∅ : Finset (Fin 0)) (fun S hS => by
      exfalso; exact hS (Finset.eq_empty_of_isEmpty S))]
    simp
  | succ m ih =>
    -- Let B = upper m×m block of A, last = Fin.last m, aᵢ = A i last
    let B : Matrix (Fin m) (Fin m) ℂ := A.submatrix Fin.castSucc Fin.castSucc
    -- B is Hermitian since A is
    have hB : B.IsHermitian := hA.submatrix Fin.castSucc
    -- |B i j| ≤ 1
    have hBbound : ∀ i j, ‖B i j‖ ≤ 1 := fun i j => hbound _ _
    -- Key decomposition (Harcos):
    -- f_A(z) = f_B(a_{0,n}·z_0,...,a_{m-1,n}·z_{m-1})
    --        + (z_0···z_n) · conj(f_B(a_{0,n}/conj(z_0),...))
    -- where aᵢ = A (Fin.castSucc i) (Fin.last m)
    -- First term ≠ 0 by ih (since |aᵢ·zᵢ| ≤ |aᵢ|·|zᵢ| < 1)
    have h_first_nonzero : (leeYangPoly B).eval
        (fun i => A (Fin.castSucc i) (Fin.last m) * z (Fin.castSucc i)) ≠ 0 := by
      apply ih B hB hBbound
      intro k
      calc ‖A (Fin.castSucc k) (Fin.last m) * z (Fin.castSucc k)‖
          = ‖A (Fin.castSucc k) (Fin.last m)‖ * ‖z (Fin.castSucc k)‖ := norm_mul _ _
        _ ≤ 1 * ‖z (Fin.castSucc k)‖ := by
            exact mul_le_mul_of_nonneg_right (hbound _ _) (norm_nonneg _)
        _ < 1 := by linarith [hz (Fin.castSucc k)]
    -- f_A is linear in z_last: f_A(z) = β + z_last · α
    -- where β = firstTerm = f_B(a·z) and α is the z_last coefficient.
    let β := (leeYangPoly B).eval
        (fun i => A (Fin.castSucc i) (Fin.last m) * z (Fin.castSucc i))
    -- α = ∑_{S : last ∈ S} coeff(S) · ∏_{k ∈ S \ {last}} z_k
    let α := ∑ S ∈ (Finset.univ : Finset (Finset (Fin (m + 1)))).filter
        (fun S => Fin.last m ∈ S),
        leeYangPoly A S * ∏ k ∈ S.erase (Fin.last m), z k
    -- Step 1: eval = β + z_last · α (sum splitting + factoring z_last from monomial)
    have hdecomp : (leeYangPoly A).eval z = β + z (Fin.last m) * α := by
      -- Split ∑_S into ∑_{last∉S} + ∑_{last∈S}, factor z_last from the second sum
      change (∑ S : Finset (Fin (m + 1)), leeYangPoly A S * ∏ k ∈ S, z k) = β + _
      rw [show (∑ S : Finset (Fin (m + 1)), leeYangPoly A S * ∏ k ∈ S, z k) =
        ∑ S ∈ Finset.univ.filter (fun S => Fin.last m ∈ S),
          leeYangPoly A S * ∏ k ∈ S, z k +
        ∑ S ∈ Finset.univ.filter (fun S => Fin.last m ∉ S),
          leeYangPoly A S * ∏ k ∈ S, z k from
        (Finset.sum_filter_add_sum_filter_not _ _ _).symm]
      rw [add_comm]; congr 1
      · -- Σ_{last∉S} = β (bijection with Finset (Fin m))
        symm
        apply Finset.sum_nbij (fun T =>
          T.map ⟨Fin.castSucc, Fin.castSucc_injective m⟩)
        · intro T _
          simp [Finset.mem_filter, Finset.mem_map, Fin.castSucc_ne_last]
        · intro T₁ _ T₂ _ h
          exact Finset.map_injective ⟨Fin.castSucc, Fin.castSucc_injective m⟩ h
        · intro S hS
          rw [Set.mem_image]
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hS
          refine ⟨S.preimage Fin.castSucc
            (Fin.castSucc_injective m |>.injOn),
            Finset.mem_coe.mpr (Finset.mem_univ _), ?_⟩
          ext j; simp only [Finset.mem_map, Finset.mem_preimage,
            Function.Embedding.coeFn_mk]
          constructor
          · rintro ⟨k, hk, rfl⟩; exact hk
          · intro hj
            induction j using Fin.lastCases with
            | last => exact absurd hj hS
            | cast i => exact ⟨i, hj, rfl⟩
        · intro T _; exact (leeYangPoly_coeff_notin A T z).symm
      · -- Σ_{last∈S} factor: ∏_{k∈S} z_k = z_last * ∏_{k∈S\{last}} z_k
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro S hS
        rw [Finset.mem_filter] at hS
        rw [← Finset.mul_prod_erase S z hS.2]
        ring
    -- Step 2: ‖α‖ ≤ ‖β‖ (maximum modulus principle + Hermitian structure)
    -- On |z_k| = 1: α = (∏_{k<m} z_k) · conj(β), so |α| = |β|.
    -- By max modulus (iterated 1-variable): |α/β| ≤ 1 on |z_k| < 1.
    -- Uses: when |a_{k,n}| < 1, β ≠ 0 on closed polydisk (ih), so α/β holomorphic.
    -- Extends to |a_{k,n}| ≤ 1 by continuity.
    have hbound : ‖α‖ ≤ ‖β‖ :=
      leeYangPoly_ratio_bound A hA hbound z hz ih
    -- Step 3: Conclude f_A ≠ 0
    rw [hdecomp]
    intro h
    -- β + z_last · α = 0 → β = -(z_last · α)
    -- |β| = |z_last| · |α| ≤ |z_last| · |β|
    -- If β ≠ 0: 1 ≤ |z_last| < 1, contradiction.
    have hβ : β ≠ 0 := h_first_nonzero
    have : ‖β‖ ≤ ‖z (Fin.last m)‖ * ‖β‖ := by
      have heq : β = -(z (Fin.last m) * α) := by linear_combination h
      calc ‖β‖ = ‖z (Fin.last m) * α‖ := by rw [heq, norm_neg]
        _ = ‖z (Fin.last m)‖ * ‖α‖ := norm_mul _ _
        _ ≤ ‖z (Fin.last m)‖ * ‖β‖ := by
            exact mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
    have hβ_pos : 0 < ‖β‖ := norm_pos_iff.mpr hβ
    have : 1 ≤ ‖z (Fin.last m)‖ := by
      by_contra h
      push Not at h
      linarith [mul_lt_of_lt_one_left hβ_pos h]
    linarith [hz (Fin.last m)]

/-! ## Application to Ising model -/

/-- The edge weight factor for the Ising partition polynomial.
For an edge `(i, j)` with coupling `t`, the weight of subset `X` is
`t` if exactly one of `i, j` is in `X`, and `1` otherwise.

Reference: Friedli–Velenik, (3.63), p. 122. -/
def edgeWeight (i j : ι) (t : ℝ) (X : Finset ι) : ℂ :=
  if (i ∈ X) = (j ∈ X) then 1 else ↑t

/-- The Ising partition polynomial for a list of edges with couplings.
`P_E(z) = Σ_{X⊆V} (∏_e w_e(X)) ∏_{i∈X} z_i` where `w_e(X) = t_e` if
exactly one endpoint of `e` is in `X`, and `1` otherwise.

This captures the multilinear form of the Ising partition function with
`z_i = e^{-2h_i}`, `t_e = e^{-2β J_e}`.

Reference: Friedli–Velenik, (3.63)--(3.65), pp. 122--123. -/
noncomputable def isingEdgePoly (edges : List (ι × ι × ℝ)) : MultilinPoly ι :=
  fun X => (edges.map fun e => edgeWeight e.1 e.2.1 e.2.2 X).prod

/-- The sum over all subsets of the product of selected elements equals the product of (1 + z_i).
`∑_{X⊆ι} ∏_{i∈X} z_i = ∏_i (1 + z_i)`. -/
private lemma eval_one_poly {ι : Type*} [Fintype ι] (z : ι → ℂ) :
    MultilinPoly.eval (fun (_ : Finset ι) => (1 : ℂ)) z = ∏ k : ι, (1 + z k) := by
  simp only [MultilinPoly.eval, one_mul]
  have := @Finset.prod_one_add ι ℂ _ z Finset.univ
  rw [Finset.powerset_univ] at this
  exact this.symm

/-- The Ising matrix constructed from an edge list.
For vertices `i ≠ j`, `isingMatrix edges i j = ∏_{e connecting i,j} t_e`.
For `i = j`, `isingMatrix edges i i = 1`.

This matrix is real symmetric (hence Hermitian) with `|A i j| ≤ 1` when
all couplings satisfy `0 ≤ t_e < 1`. -/
noncomputable def isingMatrix (edges : List (ι × ι × ℝ)) (i j : ι) : ℂ :=
  (edges.map fun e =>
    if (e.1 = i ∧ e.2.1 = j) ∨ (e.1 = j ∧ e.2.1 = i) then (e.2.2 : ℂ) else 1).prod

omit [Fintype ι] in
/-- The Ising matrix is symmetric: `isingMatrix edges i j = isingMatrix edges j i`. -/
private lemma isingMatrix_symm (edges : List (ι × ι × ℝ)) (i j : ι) :
    isingMatrix edges i j = isingMatrix edges j i := by
  unfold isingMatrix
  congr 1
  apply List.map_congr_left
  intro e _
  simp only [or_comm]

omit [Fintype ι] in
/-- Cons decomposition of the Ising matrix. -/
private lemma isingMatrix_cons (e : ι × ι × ℝ) (edges : List (ι × ι × ℝ)) (i j : ι) :
    isingMatrix (e :: edges) i j =
    (if (e.1 = i ∧ e.2.1 = j) ∨ (e.1 = j ∧ e.2.1 = i) then (e.2.2 : ℂ) else 1) *
    isingMatrix edges i j := by
  simp [isingMatrix, List.map_cons, List.prod_cons]

/-- Pull a constant-condition `if` out of a `Finset.prod`. -/
private lemma prod_ite_const_cond {α : Type*} {S : Finset α} {p : Prop} [Decidable p]
    {f : α → ℂ} :
    ∏ j ∈ S, (if p then f j else 1) = if p then ∏ j ∈ S, f j else 1 := by
  split_ifs <;> simp_all

-- The factored condition involves 4 case splits, each with nested Finset.prod simplification
set_option maxHeartbeats 400000 in
/-- For a single edge `e`, the edge weight equals the product of the single-edge
matrix entries over all cross-boundary pairs `(i,j)` with `i ∈ X, j ∉ X`.

The proof factors the condition `(a=i ∧ b=j) ∨ (a=j ∧ b=i)` into two independent
conditions (one for each endpoint), uses `Finset.prod_ite_eq` to collapse inner/outer
products, then matches the result with `edgeWeight` by case analysis. -/
private lemma edgeWeight_eq_prod (e : ι × ι × ℝ) (hne : e.1 ≠ e.2.1) (X : Finset ι) :
    edgeWeight e.1 e.2.1 e.2.2 X =
    ∏ i ∈ X, ∏ j ∈ Finset.univ \ X,
      (if (e.1 = i ∧ e.2.1 = j) ∨ (e.1 = j ∧ e.2.1 = i) then (e.2.2 : ℂ) else 1) := by
  -- Factor: (a=i∧b=j)∨(a=j∧b=i) ↔ (a=i then b=j) × (b=i then a=j) [disjoint since a≠b]
  have h_factor : ∀ (i j : ι),
      (if (e.1 = i ∧ e.2.1 = j) ∨ (e.1 = j ∧ e.2.1 = i) then (e.2.2 : ℂ) else 1) =
      (if e.1 = i then if e.2.1 = j then ↑e.2.2 else 1 else 1) *
      (if e.2.1 = i then if e.1 = j then ↑e.2.2 else 1 else 1) := by
    intro i j; by_cases h1 : e.1 = i <;> by_cases h2 : e.2.1 = i <;> simp_all
  -- Simplify: factor products, pull constant conditions, apply prod_ite_eq
  simp_rw [h_factor, Finset.prod_mul_distrib, prod_ite_const_cond, Finset.prod_ite_eq]
  -- Result: (if a∈X then (if b∈univ\X then t else 1) else 1) * (...same with a,b swapped...)
  -- = edgeWeight by case analysis
  unfold edgeWeight
  by_cases ha : e.1 ∈ X <;> by_cases hb : e.2.1 ∈ X <;> simp_all [Finset.mem_sdiff]

private lemma isingEdgePoly_eq_leeYangCoeff (edges : List (ι × ι × ℝ))
    (hne : ∀ e ∈ edges, e.1 ≠ e.2.1) (X : Finset ι) :
    isingEdgePoly edges X =
    ∏ i ∈ X, ∏ j ∈ Finset.univ \ X, isingMatrix edges i j := by
  induction edges with
  | nil => simp [isingEdgePoly, isingMatrix]
  | cons e edges' ih =>
    have hne' := fun e' he' => hne e' (List.mem_cons_of_mem _ he')
    -- isingEdgePoly (e::edges') X = edgeWeight · isingEdgePoly edges' X
    have hcons : isingEdgePoly (e :: edges') X =
        edgeWeight e.1 e.2.1 e.2.2 X * isingEdgePoly edges' X := by
      simp [isingEdgePoly]
    rw [hcons, ih hne']
    -- Factor the RHS: isingMatrix(e::edges') = g(e) · isingMatrix(edges')
    suffices h : ∏ i ∈ X, ∏ j ∈ Finset.univ \ X, isingMatrix (e :: edges') i j =
        (∏ i ∈ X, ∏ j ∈ Finset.univ \ X,
          (if (e.1 = i ∧ e.2.1 = j) ∨ (e.1 = j ∧ e.2.1 = i) then (e.2.2 : ℂ) else 1)) *
        (∏ i ∈ X, ∏ j ∈ Finset.univ \ X, isingMatrix edges' i j) by
      rw [h]; congr 1
      exact edgeWeight_eq_prod e (hne e List.mem_cons_self) X
    simp_rw [isingMatrix_cons, Finset.prod_mul_distrib]

/-- The base case: `isingEdgePoly [] = 1` (constant polynomial). -/
private lemma isingEdgePoly_nil : isingEdgePoly (ι := ι) [] = fun _ => 1 := by
  ext X; simp [isingEdgePoly]

/-- **Lee-Yang circle theorem**: The Ising partition polynomial does not vanish
on the open unit polydisk. Reference: Friedli–Velenik, Theorem 3.43, pp. 122–127. -/
theorem lee_yang_circle (edges : List (ι × ι × ℝ))
    (hne : ∀ e ∈ edges, e.1 ≠ e.2.1)
    (ht : ∀ e ∈ edges, 0 ≤ e.2.2 ∧ e.2.2 < 1)
    (z : ι → ℂ) (hz : ∀ k, ‖z k‖ < 1) :
    (isingEdgePoly edges).eval z ≠ 0 := by
  induction edges with
  | nil =>
    -- P(z) = ∏_i (1 + z_i) ≠ 0 since each factor ≠ 0 for |z_i| < 1
    rw [show isingEdgePoly (ι := ι) [] = fun _ => 1 from isingEdgePoly_nil, eval_one_poly]
    exact Finset.prod_ne_zero_iff.mpr (fun k _ h => by
      have : z k = -1 := by linear_combination h
      linarith [hz k, show ‖z k‖ = 1 from by rw [this, norm_neg, norm_one]])
  | cons e edges' _ =>
    -- Use Harcos/Ruelle approach via the Ising matrix.
    -- Step 1: isingEdgePoly = leeYangPoly for the Ising matrix
    have hcoeff : ∀ X, isingEdgePoly (e :: edges') X =
        ∏ i ∈ X, ∏ j ∈ Finset.univ \ X, isingMatrix (e :: edges') i j :=
      fun X => isingEdgePoly_eq_leeYangCoeff _ (fun e' he' => hne e' he') X
    -- Step 2: eval identity
    have heval : (isingEdgePoly (e :: edges')).eval z =
        MultilinPoly.eval (fun S => ∏ i ∈ S, ∏ j ∈ Finset.univ \ S,
          isingMatrix (e :: edges') i j) z := by
      unfold MultilinPoly.eval
      congr 1; ext S; congr 1; exact hcoeff S
    rw [heval]
    -- Step 3: Transport to Fin n via Fintype.equivFin and apply leeYangPoly_nonvanishing
    let A : Matrix ι ι ℂ := isingMatrix (e :: edges')
    let equiv := Fintype.equivFin ι
    let A' : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ :=
      A.submatrix equiv.symm equiv.symm
    let z' : Fin (Fintype.card ι) → ℂ := z ∘ equiv.symm
    -- A is Hermitian (real symmetric: conj = id for real entries, and isingMatrix_symm)
    have hAH : A'.IsHermitian := by
      sorry -- conj(isingMatrix i j) = isingMatrix j i via real + symmetric
    -- |A' i j| ≤ 1 (product of factors in [0,1])
    have hAB : ∀ i j, ‖A' i j‖ ≤ 1 := by
      sorry -- each factor is ↑t with t ∈ [0,1) or 1
    -- The eval under reindexing matches
    have hTransport : MultilinPoly.eval (fun S => ∏ i ∈ S, ∏ j ∈ Finset.univ \ S, A i j) z =
        (leeYangPoly A').eval z' := by
      sorry -- Fintype.sum_equiv + Finset.prod_map + complement invariance
    rw [hTransport]
    exact leeYangPoly_nonvanishing A' hAH hAB z' (fun k => hz _)

end IsingModel

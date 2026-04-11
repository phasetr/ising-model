import IsingModel.GibbsMeasure
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.Finset.SymmDiff

/-!
# Non-negative correlations (HNC) framework

The `HasNonnegCorrelations` property and its preservation under multiplication
by `(a + b · σ^C)` factors. This is the shared infrastructure for GKS-I, GKS-II,
and potentially FKG.

Also includes spin product algebra (`spinProduct_mul`), configuration sum lemmas,
and the exp decomposition for ±1-valued functions.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Auxiliary: exp decomposition for ±1 spins -/

/-- For `s ∈ {+1, -1}`, `exp(α * s) = cosh(α) + s * sinh(α)`. -/
theorem exp_sign_decomp (α : ℝ) (s : Spin) :
    Real.exp (α * ↑s.toSign) = Real.cosh α + ↑s.toSign * Real.sinh α := by
  cases s with
  | up => simp [Spin.toSign, Real.cosh_add_sinh]
  | down =>
    simp only [Spin.toSign, Int.cast_neg, Int.cast_one, mul_neg, mul_one, neg_mul, one_mul]
    linarith [Real.cosh_add_sinh α, Real.sinh_add_cosh α,
              Real.cosh_add_sinh (-α), Real.sinh_add_cosh (-α),
              Real.cosh_neg α, Real.sinh_neg α]

/-! ## Sum over configurations -/

/-- The sum of `toSign(s)` over all spins is zero: `1 + (-1) = 0`. -/
theorem sum_spin_toSign : ∑ s : Spin, (↑s.toSign : ℝ) = 0 := by
  have : Fintype.elems (α := Spin) = {.up, .down} := by decide
  simp [Finset.sum, Finset.univ, this, Spin.toSign]

omit [Fintype ι] in
/-- Flipping at `j ∈ A` negates the spin product.
The factor at `j` changes sign; all other factors are unchanged. -/
theorem spinProduct_flipAt_neg (A : Finset ι) (j : ι) (hj : j ∈ A)
    (σ : Config ι) :
    spinProduct A (σ.flipAt j) = -spinProduct A σ := by
  unfold spinProduct
  rw [← Finset.mul_prod_erase _ _ hj, ← Finset.mul_prod_erase _ _ hj]
  have hj_flip : (↑((σ.flipAt j j).toSign) : ℝ) = -↑(σ j).toSign := by
    simp [Config.flipAt, Function.update_self, Spin.toSign_flip]
  have hrest : ∀ i ∈ A.erase j, (↑((σ.flipAt j i).toSign) : ℝ) = ↑(σ i).toSign := by
    intro i hi
    have hne : i ≠ j := Finset.ne_of_mem_erase hi
    simp [Config.flipAt, Function.update_of_ne hne]
  rw [hj_flip, Finset.prod_congr rfl hrest]
  ring

/-- The sum of `spinProduct A` over all configurations is zero when `A` is nonempty.
Uses the involution `flipAt j` for some `j ∈ A`: each pair `(σ, flipAt j σ)`
contributes `spinProduct A σ + spinProduct A (flipAt j σ) = 0`. -/
theorem sum_config_spinProduct_eq_zero (A : Finset ι) (hA : A.Nonempty) :
    ∑ σ : Config ι, spinProduct A σ = 0 := by
  obtain ⟨j, hj⟩ := hA
  apply Finset.sum_ninvolution (Config.flipAt j)
  · intro σ
    rw [spinProduct_flipAt_neg A j hj σ]
    ring
  · intro σ _
    exact fun h => Config.flipAt_ne j σ h
  · intro _
    exact Finset.mem_univ _
  · intro σ
    exact Config.flipAt_flipAt j σ

/-- The sum of `spinProduct ∅` over all configurations is `2^|ι|`. -/
theorem sum_config_spinProduct_empty :
    ∑ σ : Config ι, spinProduct ∅ σ = (Fintype.card (Config ι) : ℝ) := by
  simp [spinProduct_empty]

/-! ## Spin product multiplication (Fourier structure) -/

set_option linter.unusedFintypeInType false in
/-- Multiplying spin products corresponds to symmetric difference of index sets.
This follows from `s(σ_i)² = 1`: shared indices cancel. -/
theorem spinProduct_mul (A C : Finset ι) (σ : Config ι) :
    spinProduct A σ * spinProduct C σ = spinProduct (symmDiff A C) σ := by
  let s : ι → ℝ := fun i => ↑(σ i).toSign
  have hsq : ∀ i, s i * s i = 1 :=
    fun i => by simp [s, ← sq, ← Int.cast_pow, Spin.toSign_sq]
  have hprod : ∀ S : Finset ι, spinProduct S σ =
      ∏ i ∈ Finset.univ, if i ∈ S then s i else 1 := by
    intro S
    simp only [spinProduct, s]
    conv_lhs => rw [show S = Finset.univ.filter (· ∈ S) from by ext; simp]
    rw [Finset.prod_filter]
  rw [hprod A, hprod C, ← Finset.prod_mul_distrib, hprod]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Finset.mem_symmDiff]
  by_cases hiA : i ∈ A <;> by_cases hiC : i ∈ C <;> simp_all [hsq i]

/-! ## Non-negative correlations -/

/-- A function `f` on configurations has **non-negative correlations** if
`∑_σ σ^S · f(σ) ≥ 0` for every subset `S`. -/
def HasNonnegCorrelations (f : Config ι → ℝ) : Prop :=
  ∀ S : Finset ι, 0 ≤ ∑ σ : Config ι, spinProduct S σ * f σ

/-- The constant function `1` has non-negative correlations. -/
theorem hasNonnegCorrelations_one : HasNonnegCorrelations (ι := ι) (fun _ => 1) := by
  intro S
  simp only [mul_one]
  by_cases hS : S.Nonempty
  · rw [sum_config_spinProduct_eq_zero S hS]
  · simp only [not_nonempty_iff_eq_empty] at hS
    subst hS
    exact Finset.sum_nonneg fun _ _ => by norm_num

/-- If `f` has non-negative correlations, then so does `f · (a + b · σ^C)`
when `a, b ≥ 0`. This is the key inductive step. -/
theorem hasNonnegCorrelations_mul {f : Config ι → ℝ}
    (hf : HasNonnegCorrelations f)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (C : Finset ι) :
    HasNonnegCorrelations fun σ => f σ * (a + b * spinProduct C σ) := by
  intro S
  have key : ∑ σ : Config ι, spinProduct S σ * (f σ * (a + b * spinProduct C σ)) =
      a * ∑ σ : Config ι, spinProduct S σ * f σ +
      b * ∑ σ : Config ι, spinProduct (symmDiff S C) σ * f σ := by
    have : ∀ σ : Config ι, spinProduct S σ * (f σ * (a + b * spinProduct C σ)) =
        a * (spinProduct S σ * f σ) + b * (spinProduct S σ * spinProduct C σ * f σ) :=
      fun σ => by ring
    simp_rw [this]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    congr 1
    simp_rw [spinProduct_mul S C]
  rw [key]
  exact add_nonneg (mul_nonneg ha (hf S)) (mul_nonneg hb (hf (symmDiff S C)))

set_option linter.unusedDecidableInType false in
/-- Multiplying an HNC function by a product of `(a + b · σ^C)` factors preserves HNC. -/
theorem hasNonnegCorrelations_mul_prod {α : Type*} [DecidableEq α]
    (S : Finset α) {f : Config ι → ℝ} (hf : HasNonnegCorrelations f)
    (g : α → Config ι → ℝ)
    (hg : ∀ a ∈ S, ∃ c d : ℝ, ∃ C : Finset ι, 0 ≤ c ∧ 0 ≤ d ∧
      ∀ σ, g a σ = c + d * spinProduct C σ) :
    HasNonnegCorrelations fun σ => f σ * ∏ a ∈ S, g a σ := by
  induction S using Finset.induction with
  | empty => simpa using hf
  | @insert x S' hx ih =>
    rw [show (fun σ => f σ * ∏ a ∈ insert x S', g a σ) =
        fun σ => (f σ * ∏ a ∈ S', g a σ) * g x σ from by
      ext σ; rw [Finset.prod_insert hx]; ring]
    obtain ⟨c, d, C, hc, hd, hg_eq⟩ := hg x (Finset.mem_insert_self x S')
    simp_rw [hg_eq]
    exact hasNonnegCorrelations_mul
      (ih fun a ha' => hg a (Finset.mem_insert_of_mem ha')) hc hd C

set_option linter.unusedDecidableInType false in
/-- A product of `(a + b · σ^C)` factors has HNC if all `a, b ≥ 0`. -/
theorem hasNonnegCorrelations_finset_prod {α : Type*} [DecidableEq α]
    (S : Finset α)
    (g : α → Config ι → ℝ)
    (hg : ∀ a ∈ S, ∃ c d : ℝ, ∃ C : Finset ι, 0 ≤ c ∧ 0 ≤ d ∧
      ∀ σ, g a σ = c + d * spinProduct C σ) :
    HasNonnegCorrelations fun σ => ∏ a ∈ S, g a σ := by
  induction S using Finset.induction with
  | empty => simpa using hasNonnegCorrelations_one
  | @insert x S' hx ih =>
    rw [show (fun σ => ∏ a ∈ insert x S', g a σ) =
        fun σ => (∏ a ∈ S', g a σ) * g x σ from by
      ext σ; rw [Finset.prod_insert hx]; ring]
    obtain ⟨c, d, C, hc, hd, hg_eq⟩ := hg x (Finset.mem_insert_self x S')
    simp_rw [hg_eq]
    exact hasNonnegCorrelations_mul
      (ih fun a ha' => hg a (Finset.mem_insert_of_mem ha')) hc hd C

/-! ## Edge/site product HNC -/

omit [Fintype ι] [DecidableEq ι] in
/-- `edgeSpin σ e` takes values in `{-1, 1}`. -/
theorem edgeSpin_sq (σ : Config ι) (e : Sym2 ι) :
    edgeSpin (K := ℝ) σ e ^ 2 = 1 := by
  refine Sym2.ind (fun i j => ?_) e
  simp only [edgeSpin, Sym2.lift_mk, Spin.sign]
  rw [show ((↑(σ i).toSign : ℝ) * ↑(σ j).toSign) ^ 2 =
      ((↑(σ i).toSign : ℝ) ^ 2) * ((↑(σ j).toSign : ℝ) ^ 2) from by ring]
  simp [← Int.cast_pow, Spin.toSign_sq]

omit [Fintype ι] [DecidableEq ι] in
/-- `exp(α · edgeSpin σ e) = cosh α + sinh α · edgeSpin σ e` for ±1-valued edgeSpin. -/
theorem exp_edgeSpin_decomp (α : ℝ) (σ : Config ι) (e : Sym2 ι) :
    Real.exp (α * edgeSpin (K := ℝ) σ e) =
    Real.cosh α + Real.sinh α * edgeSpin σ e := by
  have hsq := edgeSpin_sq σ e
  have hpm : edgeSpin (K := ℝ) σ e = 1 ∨ edgeSpin (K := ℝ) σ e = -1 := by
    have h0 : (edgeSpin (K := ℝ) σ e - 1) * (edgeSpin (K := ℝ) σ e + 1) = 0 := by
      nlinarith [hsq]
    rcases mul_eq_zero.mp h0 with h | h
    · left; linarith
    · right; linarith
  rcases hpm with h | h
  · simp [h, Real.cosh_add_sinh]
  · simp [h]; linarith [Real.cosh_add_sinh (-α), Real.cosh_neg α, Real.sinh_neg α]

/-- A product of `exp(K_e · edgeSpin ω e)` over edges and `exp(K_i · sign(ω i))` over sites
has non-negative correlations, provided all K_e, K_i ≥ 0.
This is the common core of both GKS-I and GKS-II proofs. -/
theorem hasNonnegCorrelations_edge_site_product
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (edgeK : Sym2 ι → ℝ) (siteK : ι → ℝ)
    (hedgeK : ∀ e ∈ G.edgeFinset, 0 ≤ edgeK e)
    (hsiteK : ∀ i, 0 ≤ siteK i) :
    HasNonnegCorrelations fun σ =>
      (∏ e ∈ G.edgeFinset, Real.exp (edgeK e * edgeSpin (K := ℝ) σ e)) *
      (∏ i : ι, Real.exp (siteK i * Spin.sign ℝ (σ i))) := by
  have hedge : HasNonnegCorrelations fun σ =>
      ∏ e ∈ G.edgeFinset, Real.exp (edgeK e * edgeSpin (K := ℝ) σ e) := by
    apply hasNonnegCorrelations_finset_prod
    intro e he
    obtain ⟨⟨i, j⟩, rfl⟩ := Quot.exists_rep e
    have hne : i ≠ j := by
      intro h; subst h
      have hadj := SimpleGraph.mem_edgeFinset.mp he
      rw [SimpleGraph.mem_edgeSet] at hadj
      exact hadj.ne rfl
    exact ⟨Real.cosh (edgeK (Quot.mk _ (i, j))),
      Real.sinh (edgeK (Quot.mk _ (i, j))), {i, j},
      (Real.cosh_pos _).le, Real.sinh_nonneg_iff.mpr (hedgeK _ he), fun σ => by
        simp only [spinProduct, Finset.prod_pair hne]
        exact exp_edgeSpin_decomp (edgeK (Quot.mk _ (i, j))) σ (Quot.mk _ (i, j))⟩
  exact hasNonnegCorrelations_mul_prod Finset.univ hedge
    (fun i σ => Real.exp (siteK i * Spin.sign ℝ (σ i)))
    (fun i _ => ⟨Real.cosh (siteK i), Real.sinh (siteK i), {i},
      (Real.cosh_pos _).le, Real.sinh_nonneg_iff.mpr (hsiteK i), fun σ => by
        simp only [Spin.sign, spinProduct, Finset.prod_singleton]
        rw [exp_sign_decomp (siteK i) (σ i)]; ring⟩)

/-- GKS-I for general non-negative coupling constants.
Reference: Friedli–Velenik, Theorem 3.49 (3.54), pp. 127–128. -/
theorem hasNonnegCorrelations_general_coupling
    (couplings : Finset (Finset ι))
    (K : Finset ι → ℝ)
    (hK : ∀ C ∈ couplings, 0 ≤ K C) :
    HasNonnegCorrelations fun σ =>
      ∏ C ∈ couplings, Real.exp (K C * spinProduct C σ) := by
  apply hasNonnegCorrelations_finset_prod
  intro C hC
  have hKC := hK C hC
  refine ⟨Real.cosh (K C), Real.sinh (K C), C,
    (Real.cosh_pos _).le, Real.sinh_nonneg_iff.mpr hKC, fun σ => ?_⟩
  have hsq := spinProduct_sq C σ
  have hpm : spinProduct C σ = 1 ∨ spinProduct C σ = -1 := by
    have h0 : (spinProduct C σ - 1) * (spinProduct C σ + 1) = 0 := by nlinarith [hsq]
    rcases mul_eq_zero.mp h0 with h | h
    · left; linarith
    · right; linarith
  rcases hpm with h | h
  · simp [h, Real.cosh_add_sinh]
  · simp [h]; linarith [Real.cosh_add_sinh (-(K C)), Real.cosh_neg (K C), Real.sinh_neg (K C)]

omit [Fintype ι] [DecidableEq ι] in
/-- `1 - spinProduct B σ ≥ 0` pointwise, since `spinProduct B σ ∈ {-1, 1}`. -/
theorem one_sub_spinProduct_nonneg (B : Finset ι) (σ : Config ι) :
    0 ≤ 1 - spinProduct B σ := by
  have hsq := spinProduct_sq B σ
  have : (spinProduct B σ - 1) * (spinProduct B σ + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp this with h | h
  · linarith
  · linarith

end IsingModel

import IsingModel.ContinuousSpin.TwoComponentLebowitz.RotatedProductsDiff

/-!
# GJ Thm 4.7.1 (two-component Lebowitz) — Gibbs integrability and expectation bounds (2/2)

Structural split (2/2) of `TwoComponentLebowitz`. This child holds the monomial
integrability against the Gibbs weight and the headline expectation inequalities
`⟨t^A t^B⟩ ≥ ⟨t^A⟩⟨t^B⟩` (4.7.6), `⟨q^A q^B⟩ ≥ ⟨q^A⟩⟨q^B⟩` (4.7.7),
`⟨t^A q^B⟩ ≤ ⟨t^A⟩⟨q^B⟩` (4.7.8), and Corollary 4.7.2 (over `variable [Fintype ι]`).
It builds on the rotated-product differences in the sibling `...RotatedProductsDiff`.
See the `TwoComponentLebowitz` facade for the full overview and references.
-/

namespace IsingModel.ContinuousSpin

open MeasureTheory MvPolynomial
open scoped BigOperators

variable {ι : Type*}

/-! ## Integrability of the monomials against the Gibbs weight -/

variable [Fintype ι]

/-- `∏ᵢ xᵢ^{[i∈A]} = ∏_{i∈A} xᵢ`. -/
theorem prod_pow_ite_one [DecidableEq ι] (x : ι → ℝ) (A : Finset ι) :
    (∏ i, x i ^ (if i ∈ A then 1 else 0)) = ∏ i ∈ A, x i := by
  rw [show (∏ i, x i ^ (if i ∈ A then 1 else 0)) = ∏ i, (if i ∈ A then x i else 1) from
        Finset.prod_congr rfl fun i _ => by split <;> simp,
    Finset.prod_ite_mem, Finset.univ_inter]

/-- The `t`-monomial as a general monomial. -/
theorem vectorMonomial_t_eq_genMonomial [DecidableEq ι] (A : Finset ι) (ξ : VectorConfig ι) :
    vectorMonomial A ∅ ξ = genMonomial (fun i => if i ∈ A then 1 else 0) 0 ξ := by
  rw [genMonomial, vectorMonomial, Finset.prod_empty, mul_one]
  simp only [Pi.zero_apply, pow_zero, mul_one]
  rw [prod_pow_ite_one]
  rfl

/-- The product of two `t`-monomials is a general monomial. -/
theorem vectorMonomial_t_mul_eq_genMonomial [DecidableEq ι] (A B : Finset ι) (ξ : VectorConfig ι) :
    vectorMonomial A ∅ ξ * vectorMonomial B ∅ ξ
      = genMonomial (fun i => (if i ∈ A then 1 else 0) + (if i ∈ B then 1 else 0)) 0 ξ := by
  have hg : genMonomial (fun i => (if i ∈ A then 1 else 0) + (if i ∈ B then 1 else 0)) 0 ξ
      = (∏ i ∈ A, (ξ i).1) * ∏ i ∈ B, (ξ i).1 := by
    rw [genMonomial]
    simp only [Pi.zero_apply, pow_zero, mul_one, pow_add, Finset.prod_mul_distrib,
      prod_pow_ite_one]
  rw [hg]
  simp only [vectorMonomial, Finset.prod_empty, mul_one, vSpinT]

/-- The `q`-monomial as a general monomial. -/
theorem vectorMonomial_q_eq_genMonomial [DecidableEq ι] (B : Finset ι) (ξ : VectorConfig ι) :
    vectorMonomial ∅ B ξ = genMonomial 0 (fun i => if i ∈ B then 1 else 0) ξ := by
  rw [genMonomial, vectorMonomial, Finset.prod_empty, one_mul]
  simp only [Pi.zero_apply, pow_zero, one_mul]
  rw [prod_pow_ite_one]
  rfl

/-- The product of a `t`-monomial and a `q`-monomial is a general monomial. -/
theorem vectorMonomial_t_mul_q_eq_genMonomial [DecidableEq ι] (A B : Finset ι)
    (ξ : VectorConfig ι) :
    vectorMonomial A ∅ ξ * vectorMonomial ∅ B ξ
      = genMonomial (fun i => if i ∈ A then 1 else 0) (fun i => if i ∈ B then 1 else 0) ξ := by
  have hg : genMonomial (fun i => if i ∈ A then 1 else 0) (fun i => if i ∈ B then 1 else 0) ξ
      = (∏ i ∈ A, (ξ i).1) * ∏ i ∈ B, (ξ i).2 := by
    rw [genMonomial]
    simp only [Finset.prod_mul_distrib, prod_pow_ite_one]
  rw [hg]
  simp only [vectorMonomial, Finset.prod_empty, mul_one, one_mul, vSpinT, vSpinQ]

/-- The product of two `q`-monomials is a general monomial. -/
theorem vectorMonomial_q_mul_eq_genMonomial [DecidableEq ι] (A B : Finset ι) (ξ : VectorConfig ι) :
    vectorMonomial ∅ A ξ * vectorMonomial ∅ B ξ
      = genMonomial 0 (fun i => (if i ∈ A then 1 else 0) + (if i ∈ B then 1 else 0)) ξ := by
  have hg : genMonomial (0 : ι → ℕ) (fun i => (if i ∈ A then 1 else 0) + (if i ∈ B then 1 else 0)) ξ
      = (∏ i ∈ A, (ξ i).2) * ∏ i ∈ B, (ξ i).2 := by
    rw [genMonomial]
    simp only [Pi.zero_apply, pow_zero, one_mul, pow_add, Finset.prod_mul_distrib,
      prod_pow_ite_one]
  rw [hg]
  simp only [vectorMonomial, Finset.prod_empty, one_mul, vSpinQ]

/-! ## Integrability of the monomials against the Gibbs weight -/

/-- Integrability of a `t`-monomial against the Gibbs weight. -/
theorem integrable_vm_t_mul (Gr : SimpleGraph ι) [Fintype Gr.edgeSet] {A' : ℝ}
    (σ J h1 h2 β : ℝ) (hA : 0 < A') (A : Finset ι) :
    Integrable (fun ξ => vectorMonomial A ∅ ξ * vectorWeight Gr A' σ J h1 h2 β ξ) := by
  classical
  exact (integrable_genMonomial_mul_vectorWeight Gr σ J h1 h2 β hA
    (fun i => if i ∈ A then 1 else 0) 0).congr
    (Filter.Eventually.of_forall fun ξ => by simp only [vectorMonomial_t_eq_genMonomial])

/-- Integrability of a `q`-monomial against the Gibbs weight. -/
theorem integrable_vm_q_mul (Gr : SimpleGraph ι) [Fintype Gr.edgeSet] {A' : ℝ}
    (σ J h1 h2 β : ℝ) (hA : 0 < A') (B : Finset ι) :
    Integrable (fun ξ => vectorMonomial ∅ B ξ * vectorWeight Gr A' σ J h1 h2 β ξ) := by
  classical
  exact (integrable_genMonomial_mul_vectorWeight Gr σ J h1 h2 β hA
    0 (fun i => if i ∈ B then 1 else 0)).congr
    (Filter.Eventually.of_forall fun ξ => by simp only [vectorMonomial_q_eq_genMonomial])

/-- Integrability of a product of two `t`-monomials against the Gibbs weight. -/
theorem integrable_vm_t_t_mul (Gr : SimpleGraph ι) [Fintype Gr.edgeSet] {A' : ℝ}
    (σ J h1 h2 β : ℝ) (hA : 0 < A') (A B : Finset ι) :
    Integrable (fun ξ => vectorMonomial A ∅ ξ * vectorMonomial B ∅ ξ
      * vectorWeight Gr A' σ J h1 h2 β ξ) := by
  classical
  exact (integrable_genMonomial_mul_vectorWeight Gr σ J h1 h2 β hA
    (fun i => (if i ∈ A then 1 else 0) + (if i ∈ B then 1 else 0)) 0).congr
    (Filter.Eventually.of_forall fun ξ => by simp only [vectorMonomial_t_mul_eq_genMonomial])

/-- Integrability of a product of two `q`-monomials against the Gibbs weight. -/
theorem integrable_vm_q_q_mul (Gr : SimpleGraph ι) [Fintype Gr.edgeSet] {A' : ℝ}
    (σ J h1 h2 β : ℝ) (hA : 0 < A') (A B : Finset ι) :
    Integrable (fun ξ => vectorMonomial ∅ A ξ * vectorMonomial ∅ B ξ
      * vectorWeight Gr A' σ J h1 h2 β ξ) := by
  classical
  exact (integrable_genMonomial_mul_vectorWeight Gr σ J h1 h2 β hA
    0 (fun i => (if i ∈ A then 1 else 0) + (if i ∈ B then 1 else 0))).congr
    (Filter.Eventually.of_forall fun ξ => by simp only [vectorMonomial_q_mul_eq_genMonomial])

/-- Integrability of a product of a `t`-monomial and a `q`-monomial against the Gibbs weight. -/
theorem integrable_vm_t_q_mul (Gr : SimpleGraph ι) [Fintype Gr.edgeSet] {A' : ℝ}
    (σ J h1 h2 β : ℝ) (hA : 0 < A') (A B : Finset ι) :
    Integrable (fun ξ => vectorMonomial A ∅ ξ * vectorMonomial ∅ B ξ
      * vectorWeight Gr A' σ J h1 h2 β ξ) := by
  classical
  exact (integrable_genMonomial_mul_vectorWeight Gr σ J h1 h2 β hA
    (fun i => if i ∈ A then 1 else 0) (fun i => if i ∈ B then 1 else 0)).congr
    (Filter.Eventually.of_forall fun ξ => by simp only [vectorMonomial_t_mul_q_eq_genMonomial])

/-! ## The second/third inequalities of Theorem 4.7.1 -/

/-- `vectorExpectation` is odd under negation of the observable. -/
theorem vectorExpectation_neg (Gr : SimpleGraph ι) [Fintype Gr.edgeSet]
    (A' σ J h1 h2 β : ℝ) (F : VectorConfig ι → ℝ) :
    vectorExpectation Gr A' σ J h1 h2 β (fun ξ => -F ξ)
      = -vectorExpectation Gr A' σ J h1 h2 β F := by
  simp only [vectorExpectation]
  rw [show (fun ξ => -F ξ * vectorWeight Gr A' σ J h1 h2 β ξ)
      = fun ξ => -(F ξ * vectorWeight Gr A' σ J h1 h2 β ξ) from funext fun ξ => by ring,
    integral_neg]
  ring

/-- **GJ Theorem 4.7.1 (4.7.6): the `t`-correlations are positively associated**:
`⟨t^A⟩·⟨t^B⟩ ≤ ⟨t^A · t^B⟩`. -/
theorem vectorExpectation_t_mul_le (Gr : SimpleGraph ι) [Fintype Gr.edgeSet] {A' : ℝ}
    (σ J h1 h2 β : ℝ) (hA : 0 < A') (hβJ : 0 ≤ β * J) (hh1 : 0 ≤ β * h1) (hh2 : 0 ≤ β * h2)
    (A B : Finset ι) :
    vectorExpectation Gr A' σ J h1 h2 β (vectorMonomial A ∅)
        * vectorExpectation Gr A' σ J h1 h2 β (vectorMonomial B ∅)
      ≤ vectorExpectation Gr A' σ J h1 h2 β
          (fun ξ => vectorMonomial A ∅ ξ * vectorMonomial B ∅ ξ) := by
  classical
  have hcα : 0 ≤ Real.sqrt 2 * β * h1 := by
    rw [mul_assoc]; exact mul_nonneg (Real.sqrt_nonneg 2) hh1
  have hcγ : 0 ≤ Real.sqrt 2 * β * h2 := by
    rw [mul_assoc]; exact mul_nonneg (Real.sqrt_nonneg 2) hh2
  refine vectorExpectation_mul_le_of_doubled_nonneg Gr σ J h1 h2 β hA
    (integrable_vm_t_mul Gr σ J h1 h2 β hA A) (integrable_vm_t_mul Gr σ J h1 h2 β hA B)
    (integrable_vm_t_t_mul Gr σ J h1 h2 β hA A B)
    (doubled_integral_nonneg Gr hA hβJ hcα hcγ
      (obs := C ((Real.sqrt 2 / 2) ^ A.card) * (plusProd A 0 1 - minusProd A 0 1)
        * (C ((Real.sqrt 2 / 2) ^ B.card) * (plusProd B 0 1 - minusProd B 0 1)))
      (((NonnegCoeffs.C (by positivity)).mul (nncoeffs_oddDiff A 0 1)).mul
        ((NonnegCoeffs.C (by positivity)).mul (nncoeffs_oddDiff B 0 1)))
      (fun ξ ξ' => by rw [tMon_diff A ξ ξ', tMon_diff B ξ ξ', ← dSpinEval_mul]))

/-- **GJ Theorem 4.7.1 (4.7.7): the `q`-correlations are positively associated**:
`⟨q^A⟩·⟨q^B⟩ ≤ ⟨q^A · q^B⟩`. -/
theorem vectorExpectation_q_mul_le (Gr : SimpleGraph ι) [Fintype Gr.edgeSet] {A' : ℝ}
    (σ J h1 h2 β : ℝ) (hA : 0 < A') (hβJ : 0 ≤ β * J) (hh1 : 0 ≤ β * h1) (hh2 : 0 ≤ β * h2)
    (A B : Finset ι) :
    vectorExpectation Gr A' σ J h1 h2 β (vectorMonomial ∅ A)
        * vectorExpectation Gr A' σ J h1 h2 β (vectorMonomial ∅ B)
      ≤ vectorExpectation Gr A' σ J h1 h2 β
          (fun ξ => vectorMonomial ∅ A ξ * vectorMonomial ∅ B ξ) := by
  classical
  have hcα : 0 ≤ Real.sqrt 2 * β * h1 := by
    rw [mul_assoc]; exact mul_nonneg (Real.sqrt_nonneg 2) hh1
  have hcγ : 0 ≤ Real.sqrt 2 * β * h2 := by
    rw [mul_assoc]; exact mul_nonneg (Real.sqrt_nonneg 2) hh2
  refine vectorExpectation_mul_le_of_doubled_nonneg Gr σ J h1 h2 β hA
    (integrable_vm_q_mul Gr σ J h1 h2 β hA A) (integrable_vm_q_mul Gr σ J h1 h2 β hA B)
    (integrable_vm_q_q_mul Gr σ J h1 h2 β hA A B)
    (doubled_integral_nonneg Gr hA hβJ hcα hcγ
      (obs := C ((Real.sqrt 2 / 2) ^ A.card) * (plusProd A 2 3 - minusProd A 2 3)
        * (C ((Real.sqrt 2 / 2) ^ B.card) * (plusProd B 2 3 - minusProd B 2 3)))
      (((NonnegCoeffs.C (by positivity)).mul (nncoeffs_oddDiff A 2 3)).mul
        ((NonnegCoeffs.C (by positivity)).mul (nncoeffs_oddDiff B 2 3)))
      (fun ξ ξ' => by
        rw [qMon_diff A ξ ξ', qMon_diff B ξ ξ', ← dSpinEval_mul]
        congr 1
        ring))

/-- **GJ Theorem 4.7.1 (4.7.8): the `t`–`q` correlations are negatively associated**:
`⟨t^A · q^B⟩ ≤ ⟨t^A⟩·⟨q^B⟩`. -/
theorem vectorExpectation_t_mul_q_le (Gr : SimpleGraph ι) [Fintype Gr.edgeSet] {A' : ℝ}
    (σ J h1 h2 β : ℝ) (hA : 0 < A') (hβJ : 0 ≤ β * J) (hh1 : 0 ≤ β * h1) (hh2 : 0 ≤ β * h2)
    (A B : Finset ι) :
    vectorExpectation Gr A' σ J h1 h2 β
          (fun ξ => vectorMonomial A ∅ ξ * vectorMonomial ∅ B ξ)
      ≤ vectorExpectation Gr A' σ J h1 h2 β (vectorMonomial A ∅)
          * vectorExpectation Gr A' σ J h1 h2 β (vectorMonomial ∅ B) := by
  classical
  have hcα : 0 ≤ Real.sqrt 2 * β * h1 := by
    rw [mul_assoc]; exact mul_nonneg (Real.sqrt_nonneg 2) hh1
  have hcγ : 0 ≤ Real.sqrt 2 * β * h2 := by
    rw [mul_assoc]; exact mul_nonneg (Real.sqrt_nonneg 2) hh2
  have hGW : Integrable (fun ξ => (fun ξ => -vectorMonomial ∅ B ξ) ξ
      * vectorWeight Gr A' σ J h1 h2 β ξ) :=
    ((integrable_vm_q_mul Gr σ J h1 h2 β hA B).neg).congr
      (Filter.Eventually.of_forall fun ξ => by simp)
  have hFGW : Integrable (fun ξ => vectorMonomial A ∅ ξ * (fun ξ => -vectorMonomial ∅ B ξ) ξ
      * vectorWeight Gr A' σ J h1 h2 β ξ) :=
    ((integrable_vm_t_q_mul Gr σ J h1 h2 β hA A B).neg).congr
      (Filter.Eventually.of_forall fun ξ => by simp)
  have hkey := vectorExpectation_mul_le_of_doubled_nonneg Gr σ J h1 h2 β hA
    (F := vectorMonomial A ∅) (G := fun ξ => -vectorMonomial ∅ B ξ)
    (integrable_vm_t_mul Gr σ J h1 h2 β hA A) hGW hFGW
    (doubled_integral_nonneg Gr hA hβJ hcα hcγ
      (F := vectorMonomial A ∅) (G := fun ξ => -vectorMonomial ∅ B ξ)
      (obs := C ((Real.sqrt 2 / 2) ^ A.card) * (plusProd A 0 1 - minusProd A 0 1)
        * (C ((Real.sqrt 2 / 2) ^ B.card) * (plusProd B 2 3 - minusProd B 2 3)))
      (((NonnegCoeffs.C (by positivity)).mul (nncoeffs_oddDiff A 0 1)).mul
        ((NonnegCoeffs.C (by positivity)).mul (nncoeffs_oddDiff B 2 3)))
      (fun ξ ξ' => by
        have hq : -vectorMonomial ∅ B ξ - -vectorMonomial ∅ B ξ'
            = -(vectorMonomial ∅ B ξ - vectorMonomial ∅ B ξ') := by ring
        rw [tMon_diff A ξ ξ', hq, qMon_diff B ξ ξ', mul_neg, ← dSpinEval_mul, ← dSpinEval_neg]
        congr 1
        ring))
  have e1 : vectorExpectation Gr A' σ J h1 h2 β (fun ξ => -vectorMonomial ∅ B ξ)
      = -vectorExpectation Gr A' σ J h1 h2 β (vectorMonomial ∅ B) :=
    vectorExpectation_neg Gr A' σ J h1 h2 β (vectorMonomial ∅ B)
  have e2 : vectorExpectation Gr A' σ J h1 h2 β
        (fun ξ => vectorMonomial A ∅ ξ * -vectorMonomial ∅ B ξ)
      = -vectorExpectation Gr A' σ J h1 h2 β
          (fun ξ => vectorMonomial A ∅ ξ * vectorMonomial ∅ B ξ) := by
    rw [← vectorExpectation_neg]
    congr 1
    funext ξ
    ring
  rw [e1, e2, mul_neg] at hkey
  linarith [hkey]

/-! ## Corollary 4.7.2 (pairwise specializations) -/

/-- **GJ Corollary 4.7.2 (pairwise `t`)**: `⟨tᵢ⟩·⟨tⱼ⟩ ≤ ⟨tᵢ·tⱼ⟩`. -/
theorem vectorExpectation_t_pair_le (Gr : SimpleGraph ι) [Fintype Gr.edgeSet]
    {A' : ℝ} (σ J h1 h2 β : ℝ) (hA : 0 < A') (hβJ : 0 ≤ β * J) (hh1 : 0 ≤ β * h1)
    (hh2 : 0 ≤ β * h2) (i j : ι) :
    vectorExpectation Gr A' σ J h1 h2 β (vectorMonomial {i} ∅)
        * vectorExpectation Gr A' σ J h1 h2 β (vectorMonomial {j} ∅)
      ≤ vectorExpectation Gr A' σ J h1 h2 β
          (fun ξ => vectorMonomial {i} ∅ ξ * vectorMonomial {j} ∅ ξ) :=
  vectorExpectation_t_mul_le Gr σ J h1 h2 β hA hβJ hh1 hh2 {i} {j}

/-- **GJ Corollary 4.7.2 (pairwise `q`)**: `⟨qᵢ⟩·⟨qⱼ⟩ ≤ ⟨qᵢ·qⱼ⟩`. -/
theorem vectorExpectation_q_pair_le (Gr : SimpleGraph ι) [Fintype Gr.edgeSet]
    {A' : ℝ} (σ J h1 h2 β : ℝ) (hA : 0 < A') (hβJ : 0 ≤ β * J) (hh1 : 0 ≤ β * h1)
    (hh2 : 0 ≤ β * h2) (i j : ι) :
    vectorExpectation Gr A' σ J h1 h2 β (vectorMonomial ∅ {i})
        * vectorExpectation Gr A' σ J h1 h2 β (vectorMonomial ∅ {j})
      ≤ vectorExpectation Gr A' σ J h1 h2 β
          (fun ξ => vectorMonomial ∅ {i} ξ * vectorMonomial ∅ {j} ξ) :=
  vectorExpectation_q_mul_le Gr σ J h1 h2 β hA hβJ hh1 hh2 {i} {j}

/-- **GJ Corollary 4.7.2 (pairwise `t`–`q`)**: `⟨tᵢ·qⱼ⟩ ≤ ⟨tᵢ⟩·⟨qⱼ⟩`. -/
theorem vectorExpectation_t_q_pair_le (Gr : SimpleGraph ι) [Fintype Gr.edgeSet]
    {A' : ℝ} (σ J h1 h2 β : ℝ) (hA : 0 < A') (hβJ : 0 ≤ β * J) (hh1 : 0 ≤ β * h1)
    (hh2 : 0 ≤ β * h2) (i j : ι) :
    vectorExpectation Gr A' σ J h1 h2 β
          (fun ξ => vectorMonomial {i} ∅ ξ * vectorMonomial ∅ {j} ξ)
      ≤ vectorExpectation Gr A' σ J h1 h2 β (vectorMonomial {i} ∅)
          * vectorExpectation Gr A' σ J h1 h2 β (vectorMonomial ∅ {j}) :=
  vectorExpectation_t_mul_q_le Gr σ J h1 h2 β hA hβJ hh1 hh2 {i} {j}


end IsingModel.ContinuousSpin

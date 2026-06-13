import IsingModel.ContinuousSpin.TwoComponentChangeOfVariables
import IsingModel.ContinuousSpin.TwoComponentDoubling

/-!
# The second/third inequalities of GJ Theorem 4.7.1 (Lebowitz for two-component spins)

The difference-observable non-negative-coefficient expansion completing the
duplicate-variable proof of the second/third inequalities of GJ Theorem 4.7.1
(4.7.6)–(4.7.8), pp. 70–71.

In the §4.7 block rotation, the single-copy spins are recovered from the rotated
coordinates by `tᵢ = (αᵢ + βᵢ)/√2`, `tᵢ' = (αᵢ − βᵢ)/√2`, `qᵢ = (γᵢ − δᵢ)/√2`,
`qᵢ' = (γᵢ + δᵢ)/√2`.  Hence the difference of a `t`- (resp. `q`-) monomial across
the duplicate is `(√2/2)^{|A|}` times the difference of the `±` products of the
rotated coordinates, which expands (`plusProd − minusProd`) with **non-negative
coefficients** (mutual induction `nncoeffs_evenSum_oddDiff`).  Feeding the product
of two such differences to `doubled_integral_nonneg` and combining with the GKS-II
doubling consequence gives the headline inequalities
`⟨t^A t^B⟩ ≥ ⟨t^A⟩⟨t^B⟩` (4.7.6), `⟨q^A q^B⟩ ≥ ⟨q^A⟩⟨q^B⟩` (4.7.7), and
`⟨t^A q^B⟩ ≤ ⟨t^A⟩⟨q^B⟩` (4.7.8), and Corollary 4.7.2.

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §4.7, Theorem 4.7.1, Cor 4.7.2, pp. 70–71
-/

namespace IsingModel.ContinuousSpin

open MeasureTheory MvPolynomial
open scoped BigOperators

variable {ι : Type*}

/-! ## The `±` products of two rotated coordinate slots -/

/-- The product `∏_{i∈S} (X(i,s) + X(i,t))` of summed coordinate slots. -/
noncomputable def plusProd (S : Finset ι) (s t : Fin 4) : MvPolynomial (ι × Fin 4) ℝ :=
  ∏ i ∈ S, (X (i, s) + X (i, t))

/-- The product `∏_{i∈S} (X(i,s) − X(i,t))` of differenced coordinate slots. -/
noncomputable def minusProd (S : Finset ι) (s t : Fin 4) : MvPolynomial (ι × Fin 4) ℝ :=
  ∏ i ∈ S, (X (i, s) - X (i, t))

/-- The summed product has non-negative coefficients. -/
theorem nncoeffs_plusProd (S : Finset ι) (s t : Fin 4) : NNCoeffs (plusProd S s t) :=
  NNCoeffs.prod fun _ _ => (NNCoeffs.X _).add (NNCoeffs.X _)

/-- **Mutual non-negativity of the even sum and the odd difference**: both
`plusProd + minusProd` and `plusProd − minusProd` have non-negative coefficients.
This is the combinatorial core of (4.7.6)–(4.7.8): the difference of `±` products
expands with non-negative coefficients. -/
theorem nncoeffs_evenSum_oddDiff (S : Finset ι) (s t : Fin 4) :
    NNCoeffs (plusProd S s t + minusProd S s t)
      ∧ NNCoeffs (plusProd S s t - minusProd S s t) := by
  classical
  induction S using Finset.induction with
  | empty =>
    refine ⟨?_, ?_⟩
    · simpa only [plusProd, minusProd, Finset.prod_empty] using
        (NNCoeffs.one (ι := ι)).add NNCoeffs.one
    · simpa only [plusProd, minusProd, Finset.prod_empty, sub_self] using
        (NNCoeffs.zero (ι := ι))
  | insert i S hi ih =>
    obtain ⟨ihe, iho⟩ := ih
    have hP : plusProd (insert i S) s t = (X (i, s) + X (i, t)) * plusProd S s t := by
      rw [plusProd, plusProd, Finset.prod_insert hi]
    have hM : minusProd (insert i S) s t = (X (i, s) - X (i, t)) * minusProd S s t := by
      rw [minusProd, minusProd, Finset.prod_insert hi]
    refine ⟨?_, ?_⟩
    · have heq : plusProd (insert i S) s t + minusProd (insert i S) s t
          = X (i, s) * (plusProd S s t + minusProd S s t)
            + X (i, t) * (plusProd S s t - minusProd S s t) := by rw [hP, hM]; ring
      rw [heq]
      exact ((NNCoeffs.X _).mul ihe).add ((NNCoeffs.X _).mul iho)
    · have heq : plusProd (insert i S) s t - minusProd (insert i S) s t
          = X (i, s) * (plusProd S s t - minusProd S s t)
            + X (i, t) * (plusProd S s t + minusProd S s t) := by rw [hP, hM]; ring
      rw [heq]
      exact ((NNCoeffs.X _).mul iho).add ((NNCoeffs.X _).mul ihe)

/-- The odd difference `plusProd − minusProd` has non-negative coefficients. -/
theorem nncoeffs_oddDiff (S : Finset ι) (s t : Fin 4) :
    NNCoeffs (plusProd S s t - minusProd S s t) :=
  (nncoeffs_evenSum_oddDiff S s t).2

/-! ## Evaluation of the `±` products -/

/-- The evaluation of `plusProd` at a configuration. -/
theorem dSpinEval_plusProd (S : Finset ι) (s t : Fin 4) (cfg : ι → Fin 4 → ℝ) :
    dSpinEval (plusProd S s t) cfg = ∏ i ∈ S, (cfg i s + cfg i t) := by
  simp only [dSpinEval, plusProd, map_prod, map_add, eval_X, dSpinVal]

/-- The evaluation of `minusProd` at a configuration. -/
theorem dSpinEval_minusProd (S : Finset ι) (s t : Fin 4) (cfg : ι → Fin 4 → ℝ) :
    dSpinEval (minusProd S s t) cfg = ∏ i ∈ S, (cfg i s - cfg i t) := by
  simp only [dSpinEval, minusProd, map_prod, map_sub, eval_X, dSpinVal]

/-- `dSpinEval` is multiplicative. -/
theorem dSpinEval_mul (p q : MvPolynomial (ι × Fin 4) ℝ) (cfg : ι → Fin 4 → ℝ) :
    dSpinEval (p * q) cfg = dSpinEval p cfg * dSpinEval q cfg := by
  simp only [dSpinEval, map_mul]

/-- `dSpinEval` of a constant times a difference. -/
theorem dSpinEval_C_mul_sub (c : ℝ) (p q : MvPolynomial (ι × Fin 4) ℝ) (cfg : ι → Fin 4 → ℝ) :
    dSpinEval (C c * (p - q)) cfg = c * (dSpinEval p cfg - dSpinEval q cfg) := by
  simp only [dSpinEval, map_mul, map_sub, eval_C]

/-- `dSpinEval` is odd under negation. -/
theorem dSpinEval_neg (p : MvPolynomial (ι × Fin 4) ℝ) (cfg : ι → Fin 4 → ℝ) :
    dSpinEval (-p) cfg = -dSpinEval p cfg := by
  simp only [dSpinEval, map_neg]

/-! ## Recovery of the single-copy spins from the rotated coordinates -/

/-- `tᵢ = (αᵢ + βᵢ)/√2`. -/
theorem vSpinT_eq_rot (ξ ξ' : VectorConfig ι) (i : ι) :
    (ξ i).1 = Real.sqrt 2 / 2 * (rotLin (dCoord ξ ξ' i) 0 + rotLin (dCoord ξ ξ' i) 1) := by
  obtain ⟨h0, h1, _, _⟩ := rotLin_dCoord ξ ξ' i
  rw [h0, h1, bAlpha, bBeta]
  linear_combination (-2 * (ξ i).1) * sqrt2_half_mul_self

/-- `tᵢ' = (αᵢ − βᵢ)/√2`. -/
theorem vSpinT'_eq_rot (ξ ξ' : VectorConfig ι) (i : ι) :
    (ξ' i).1 = Real.sqrt 2 / 2 * (rotLin (dCoord ξ ξ' i) 0 - rotLin (dCoord ξ ξ' i) 1) := by
  obtain ⟨h0, h1, _, _⟩ := rotLin_dCoord ξ ξ' i
  rw [h0, h1, bAlpha, bBeta]
  linear_combination (-2 * (ξ' i).1) * sqrt2_half_mul_self

/-- `qᵢ = (γᵢ − δᵢ)/√2`. -/
theorem vSpinQ_eq_rot (ξ ξ' : VectorConfig ι) (i : ι) :
    (ξ i).2 = Real.sqrt 2 / 2 * (rotLin (dCoord ξ ξ' i) 2 - rotLin (dCoord ξ ξ' i) 3) := by
  obtain ⟨_, _, h2, h3⟩ := rotLin_dCoord ξ ξ' i
  rw [h2, h3, bGamma, bDelta]
  linear_combination (-2 * (ξ i).2) * sqrt2_half_mul_self

/-- `qᵢ' = (γᵢ + δᵢ)/√2`. -/
theorem vSpinQ'_eq_rot (ξ ξ' : VectorConfig ι) (i : ι) :
    (ξ' i).2 = Real.sqrt 2 / 2 * (rotLin (dCoord ξ ξ' i) 2 + rotLin (dCoord ξ ξ' i) 3) := by
  obtain ⟨_, _, h2, h3⟩ := rotLin_dCoord ξ ξ' i
  rw [h2, h3, bGamma, bDelta]
  linear_combination (-2 * (ξ' i).2) * sqrt2_half_mul_self

/-! ## Monomial expansion and the difference identities -/

/-- The `t`-monomial of the first copy expands as `(√2/2)^{|A|}` times `plusProd`. -/
theorem vectorMonomial_t_eq (A : Finset ι) (ξ ξ' : VectorConfig ι) :
    vectorMonomial A ∅ ξ
      = (Real.sqrt 2 / 2) ^ A.card
        * dSpinEval (plusProd A 0 1) (fun i => rotLin (dCoord ξ ξ' i)) := by
  rw [dSpinEval_plusProd, vectorMonomial, Finset.prod_empty, mul_one]
  calc ∏ i ∈ A, vSpinT ξ i
      = ∏ i ∈ A, Real.sqrt 2 / 2
          * (rotLin (dCoord ξ ξ' i) 0 + rotLin (dCoord ξ ξ' i) 1) :=
        Finset.prod_congr rfl fun i _ => vSpinT_eq_rot ξ ξ' i
    _ = (Real.sqrt 2 / 2) ^ A.card
          * ∏ i ∈ A, (rotLin (dCoord ξ ξ' i) 0 + rotLin (dCoord ξ ξ' i) 1) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]

/-- The `t`-monomial of the second copy expands as `(√2/2)^{|A|}` times `minusProd`. -/
theorem vectorMonomial_t'_eq (A : Finset ι) (ξ ξ' : VectorConfig ι) :
    vectorMonomial A ∅ ξ'
      = (Real.sqrt 2 / 2) ^ A.card
        * dSpinEval (minusProd A 0 1) (fun i => rotLin (dCoord ξ ξ' i)) := by
  rw [dSpinEval_minusProd, vectorMonomial, Finset.prod_empty, mul_one]
  calc ∏ i ∈ A, vSpinT ξ' i
      = ∏ i ∈ A, Real.sqrt 2 / 2
          * (rotLin (dCoord ξ ξ' i) 0 - rotLin (dCoord ξ ξ' i) 1) :=
        Finset.prod_congr rfl fun i _ => vSpinT'_eq_rot ξ ξ' i
    _ = (Real.sqrt 2 / 2) ^ A.card
          * ∏ i ∈ A, (rotLin (dCoord ξ ξ' i) 0 - rotLin (dCoord ξ ξ' i) 1) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]

/-- The `q`-monomial of the first copy expands as `(√2/2)^{|B|}` times `minusProd` on `2,3`. -/
theorem vectorMonomial_q_eq (B : Finset ι) (ξ ξ' : VectorConfig ι) :
    vectorMonomial ∅ B ξ
      = (Real.sqrt 2 / 2) ^ B.card
        * dSpinEval (minusProd B 2 3) (fun i => rotLin (dCoord ξ ξ' i)) := by
  rw [dSpinEval_minusProd, vectorMonomial, Finset.prod_empty, one_mul]
  calc ∏ j ∈ B, vSpinQ ξ j
      = ∏ j ∈ B, Real.sqrt 2 / 2
          * (rotLin (dCoord ξ ξ' j) 2 - rotLin (dCoord ξ ξ' j) 3) :=
        Finset.prod_congr rfl fun j _ => vSpinQ_eq_rot ξ ξ' j
    _ = (Real.sqrt 2 / 2) ^ B.card
          * ∏ j ∈ B, (rotLin (dCoord ξ ξ' j) 2 - rotLin (dCoord ξ ξ' j) 3) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]

/-- The `q`-monomial of the second copy expands as `(√2/2)^{|B|}` times `plusProd` on `2,3`. -/
theorem vectorMonomial_q'_eq (B : Finset ι) (ξ ξ' : VectorConfig ι) :
    vectorMonomial ∅ B ξ'
      = (Real.sqrt 2 / 2) ^ B.card
        * dSpinEval (plusProd B 2 3) (fun i => rotLin (dCoord ξ ξ' i)) := by
  rw [dSpinEval_plusProd, vectorMonomial, Finset.prod_empty, one_mul]
  calc ∏ j ∈ B, vSpinQ ξ' j
      = ∏ j ∈ B, Real.sqrt 2 / 2
          * (rotLin (dCoord ξ ξ' j) 2 + rotLin (dCoord ξ ξ' j) 3) :=
        Finset.prod_congr rfl fun j _ => vSpinQ'_eq_rot ξ ξ' j
    _ = (Real.sqrt 2 / 2) ^ B.card
          * ∏ j ∈ B, (rotLin (dCoord ξ ξ' j) 2 + rotLin (dCoord ξ ξ' j) 3) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]

/-- The `t`-monomial difference across the duplicate is `dSpinEval` of a constant times the
odd difference `plusProd − minusProd` on slots `0, 1`. -/
theorem tMon_diff (A : Finset ι) (ξ ξ' : VectorConfig ι) :
    vectorMonomial A ∅ ξ - vectorMonomial A ∅ ξ'
      = dSpinEval (C ((Real.sqrt 2 / 2) ^ A.card) * (plusProd A 0 1 - minusProd A 0 1))
          (fun i => rotLin (dCoord ξ ξ' i)) := by
  rw [vectorMonomial_t_eq A ξ ξ', vectorMonomial_t'_eq A ξ ξ', dSpinEval_C_mul_sub]; ring

/-- The `q`-monomial difference across the duplicate is `dSpinEval` of a constant times
`minusProd − plusProd` on slots `2, 3`. -/
theorem qMon_diff (B : Finset ι) (ξ ξ' : VectorConfig ι) :
    vectorMonomial ∅ B ξ - vectorMonomial ∅ B ξ'
      = dSpinEval (C ((Real.sqrt 2 / 2) ^ B.card) * (minusProd B 2 3 - plusProd B 2 3))
          (fun i => rotLin (dCoord ξ ξ' i)) := by
  rw [vectorMonomial_q_eq B ξ ξ', vectorMonomial_q'_eq B ξ ξ', dSpinEval_C_mul_sub]; ring

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
      (((NNCoeffs.C (by positivity)).mul (nncoeffs_oddDiff A 0 1)).mul
        ((NNCoeffs.C (by positivity)).mul (nncoeffs_oddDiff B 0 1)))
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
      (((NNCoeffs.C (by positivity)).mul (nncoeffs_oddDiff A 2 3)).mul
        ((NNCoeffs.C (by positivity)).mul (nncoeffs_oddDiff B 2 3)))
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
      (((NNCoeffs.C (by positivity)).mul (nncoeffs_oddDiff A 0 1)).mul
        ((NNCoeffs.C (by positivity)).mul (nncoeffs_oddDiff B 2 3)))
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

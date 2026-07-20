import IsingModel.ContinuousSpin.TwoComponentChangeOfVariables
import IsingModel.ContinuousSpin.TwoComponentDoubling

/-!
# GJ Thm 4.7.1 (two-component Lebowitz) — rotated `±` products and their differences (1/2)

Structural split (1/2) of `TwoComponentLebowitz`. This child holds the `±` products of
the rotated coordinate slots, the `vectorMonomial` differences, and the non-negative
coefficient expansion of `plusProd − minusProd` (over `variable {ι}`, no finiteness).
The Gibbs-weight integrability and the headline expectation inequalities live in the
sibling `...GibbsIntegrability`. See the `TwoComponentLebowitz` facade for the full
overview and references (GJ §4.7, Thm 4.7.1 / Cor 4.7.2, pp. 70–71).
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
theorem nncoeffs_plusProd (S : Finset ι) (s t : Fin 4) : NonnegCoeffs (plusProd S s t) :=
  NonnegCoeffs.prod fun _ _ => (NonnegCoeffs.X _).add (NonnegCoeffs.X _)

/-- **Mutual non-negativity of the even sum and the odd difference**: both
`plusProd + minusProd` and `plusProd − minusProd` have non-negative coefficients.
This is the combinatorial core of (4.7.6)–(4.7.8): the difference of `±` products
expands with non-negative coefficients. -/
theorem nncoeffs_evenSum_oddDiff (S : Finset ι) (s t : Fin 4) :
    NonnegCoeffs (plusProd S s t + minusProd S s t)
      ∧ NonnegCoeffs (plusProd S s t - minusProd S s t) := by
  classical
  induction S using Finset.induction with
  | empty =>
    refine ⟨?_, ?_⟩
    · simpa only [plusProd, minusProd, Finset.prod_empty] using
        (NonnegCoeffs.one (σ := ι × Fin 4)).add NonnegCoeffs.one
    · simpa only [plusProd, minusProd, Finset.prod_empty, sub_self] using
        (NonnegCoeffs.zero (σ := ι × Fin 4))
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
      exact ((NonnegCoeffs.X _).mul ihe).add ((NonnegCoeffs.X _).mul iho)
    · have heq : plusProd (insert i S) s t - minusProd (insert i S) s t
          = X (i, s) * (plusProd S s t - minusProd S s t)
            + X (i, t) * (plusProd S s t + minusProd S s t) := by rw [hP, hM]; ring
      rw [heq]
      exact ((NonnegCoeffs.X _).mul iho).add ((NonnegCoeffs.X _).mul ihe)

/-- The odd difference `plusProd − minusProd` has non-negative coefficients. -/
theorem nncoeffs_oddDiff (S : Finset ι) (s t : Fin 4) :
    NonnegCoeffs (plusProd S s t - minusProd S s t) :=
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


end IsingModel.ContinuousSpin

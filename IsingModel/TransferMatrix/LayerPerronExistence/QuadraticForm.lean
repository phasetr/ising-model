import IsingModel.TransferMatrix.LayerPerron

/-!
# Quadratic-form helpers for signed positive columns (GJ §17.1)

The pre-namespace analytic helpers underpinning the signed-positive dominant
column construction: the squared Euclidean norm and matrix quadratic form, the
absolute-value comparison of the quadratic form for an entrywise positive
matrix, and the sign-orientation lemma
(`exists_sign_vectorNonnegative_of_abs_defect_zero`) that turns a zero
sign-defect into a coordinatewise nonnegative reorientation.  Part of the
`LayerPerronExistence` signed-positive dominant column split.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.1, pp. 304--306.
-/

namespace IsingModel

namespace TransferMatrix

open Matrix

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The squared Euclidean norm of a finite real vector, written as a finite
sum so it can be used without normed-space coercions in the transfer-matrix
spectral calculations. -/
noncomputable def vectorSqNorm (v : Ω → ℝ) : ℝ :=
  ∑ i, v i ^ 2

/-- The real quadratic form associated to a finite matrix, written as a double
sum. -/
noncomputable def matrixQuadraticForm (M : Matrix Ω Ω ℝ) (v : Ω → ℝ) : ℝ :=
  ∑ i, ∑ j, v i * M i j * v j

omit [Fintype Ω] [DecidableEq Ω] in
/-- A product is bounded by the product of absolute values. -/
theorem mul_le_abs_mul_abs (a b : ℝ) : a * b ≤ |a| * |b| := by
  have ha_pos : a ≤ |a| := le_abs_self a
  have ha_neg : -a ≤ |a| := neg_le_abs a
  have hb_pos : b ≤ |b| := le_abs_self b
  have hb_neg : -b ≤ |b| := neg_le_abs b
  nlinarith [mul_nonneg (sub_nonneg.mpr ha_pos) (sub_nonneg.mpr hb_pos),
    mul_nonneg (sub_nonneg.mpr ha_neg) (sub_nonneg.mpr hb_neg)]

omit [DecidableEq Ω] in
/-- Applying an entrywise positive matrix to a nonnegative nonzero vector gives
a strictly positive vector. -/
theorem matrixEntrywisePositive_mulVec_pos_of_nonnegative_nonzero [Nonempty Ω]
    {M : Matrix Ω Ω ℝ} {v : Ω → ℝ}
    (hM : MatrixEntrywisePositive M) (hv_nonneg : VectorNonnegative v)
    (hv_ne : v ≠ 0) :
    VectorPositive (M.mulVec v) := by
  obtain ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
    by_contra h
    apply hv_ne
    ext k
    by_contra hk
    exact h ⟨k, hk⟩
  have hvk_pos : 0 < v k := lt_of_le_of_ne (hv_nonneg k) (Ne.symm hk)
  intro i
  rw [Matrix.mulVec, dotProduct]
  exact Finset.sum_pos' (fun j _ => mul_nonneg (hM i j).le (hv_nonneg j))
    ⟨k, Finset.mem_univ k, mul_pos (hM i k) hvk_pos⟩

omit [DecidableEq Ω] in
/-- A nonnegative nonzero eigenvector of an entrywise positive matrix is
strictly positive. -/
theorem matrixEntrywisePositive_eigenvector_pos_of_nonnegative_nonzero
    [Nonempty Ω] {M : Matrix Ω Ω ℝ} {lam : ℝ} {v : Ω → ℝ}
    (hM : MatrixEntrywisePositive M)
    (hv_eig : M.mulVec v = lam • v)
    (hv_nonneg : VectorNonnegative v) (hv_ne : v ≠ 0) :
    VectorPositive v := by
  have hMv_pos : VectorPositive (M.mulVec v) :=
    matrixEntrywisePositive_mulVec_pos_of_nonnegative_nonzero hM hv_nonneg hv_ne
  intro i
  have hvi_ne : v i ≠ 0 := by
    intro hzero
    have hMv_zero : M.mulVec v i = 0 := by
      have h := congr_fun hv_eig i
      simpa [Pi.smul_apply, smul_eq_mul, hzero] using h
    exact (hMv_pos i).ne' hMv_zero
  exact lt_of_le_of_ne (hv_nonneg i) (Ne.symm hvi_ne)

omit [DecidableEq Ω] in
/-- Replacing a vector by its coordinatewise absolute value does not decrease
the quadratic form of an entrywise positive matrix. -/
theorem matrixQuadraticForm_le_abs {M : Matrix Ω Ω ℝ}
    (hM : MatrixEntrywisePositive M) (v : Ω → ℝ) :
    matrixQuadraticForm M v
      ≤ matrixQuadraticForm M (fun i => |v i|) := by
  unfold matrixQuadraticForm
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have hle : v i * v j ≤ |v i| * |v j| :=
    mul_le_abs_mul_abs (v i) (v j)
  have hle' : M i j * (v i * v j) ≤ M i j * (|v i| * |v j|) :=
    mul_le_mul_of_nonneg_left hle (hM i j).le
  nlinarith

omit [DecidableEq Ω] in
/-- The difference between the absolute-value quadratic form and the original
quadratic form is the finite sum of the entrywise sign-defects. -/
theorem matrixQuadraticForm_abs_sub {M : Matrix Ω Ω ℝ} (v : Ω → ℝ) :
    matrixQuadraticForm M (fun i => |v i|) - matrixQuadraticForm M v =
      ∑ i, ∑ j, M i j * (|v i| * |v j| - v i * v j) := by
  unfold matrixQuadraticForm
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [DecidableEq Ω] in
/-- Equality in the absolute-value quadratic-form comparison forces every
coordinate pair to have zero sign-defect. -/
theorem abs_defect_eq_zero_of_matrixQuadraticForm_abs_eq
    {M : Matrix Ω Ω ℝ} {v : Ω → ℝ}
    (hM : MatrixEntrywisePositive M)
    (heq :
      matrixQuadraticForm M (fun i => |v i|) = matrixQuadraticForm M v)
    (i j : Ω) :
    |v i| * |v j| - v i * v j = 0 := by
  let defect : Ω → Ω → ℝ := fun i j => |v i| * |v j| - v i * v j
  have hdef_nonneg : ∀ i j, 0 ≤ defect i j := by
    intro i j
    exact sub_nonneg.mpr (mul_le_abs_mul_abs (v i) (v j))
  have hsum_zero : ∑ i, ∑ j, M i j * defect i j = 0 := by
    have h := matrixQuadraticForm_abs_sub (M := M) v
    dsimp [defect]
    rw [heq] at h
    simpa using h.symm
  have hterm_nonneg : ∀ i j, 0 ≤ M i j * defect i j := by
    intro i j
    exact mul_nonneg (hM i j).le (hdef_nonneg i j)
  have hterm_le_zero : M i j * defect i j ≤ 0 := by
    calc
      M i j * defect i j ≤ ∑ j', M i j' * defect i j' :=
        Finset.single_le_sum (fun j' _ => hterm_nonneg i j')
          (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', M i' j' * defect i' j' :=
        Finset.single_le_sum
          (fun i' _ => Finset.sum_nonneg fun j' _ => hterm_nonneg i' j')
          (Finset.mem_univ i)
      _ = 0 := hsum_zero
  have hterm_zero : M i j * defect i j = 0 :=
    le_antisymm hterm_le_zero (hterm_nonneg i j)
  rcases mul_eq_zero.mp hterm_zero with hMzero | hdef
  · exact False.elim ((hM i j).ne' hMzero)
  · exact hdef

omit [Fintype Ω] [DecidableEq Ω] in
/-- If all sign-defects against one nonzero coordinate vanish, then the vector
can be oriented to be coordinatewise nonnegative. -/
theorem exists_sign_vectorNonnegative_of_abs_defect_zero
    {v : Ω → ℝ} {i0 : Ω}
    (hi0 : v i0 ≠ 0)
    (hdef : ∀ j, |v i0| * |v j| - v i0 * v j = 0) :
    ∃ s : ℝ, s * s = 1 ∧ VectorNonnegative (fun j => s * v j) := by
  by_cases hi0_nonneg : 0 ≤ v i0
  · refine ⟨1, by norm_num, ?_⟩
    intro j
    by_cases hj : v j = 0
    · simp [hj]
    · have hi0_pos : 0 < v i0 := lt_of_le_of_ne hi0_nonneg (Ne.symm hi0)
      have h := hdef j
      have hmul : |v j| = v j := by
        have hzero : |v i0| * |v j| = v i0 * v j := by linarith
        rw [abs_of_pos hi0_pos] at hzero
        exact mul_left_cancel₀ hi0 hzero
      simpa using (abs_eq_self.mp hmul)
  · refine ⟨-1, by norm_num, ?_⟩
    intro j
    by_cases hj : v j = 0
    · simp [hj]
    · have hi0_neg : v i0 < 0 := lt_of_not_ge hi0_nonneg
      have h := hdef j
      have hmul : |v j| = -v j := by
        have hzero : |v i0| * |v j| = v i0 * v j := by linarith
        rw [abs_of_neg hi0_neg] at hzero
        have hzero' : v i0 * (-|v j|) = v i0 * v j := by nlinarith
        have hcancel : -|v j| = v j := mul_left_cancel₀ hi0 hzero'
        linarith
      have hvj_nonpos : v j ≤ 0 := abs_eq_neg_self.mp hmul
      nlinarith

end TransferMatrix

end IsingModel

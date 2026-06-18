import IsingModel.TransferMatrix.LayerPerron

/-!
# Signed positive dominant columns for finite layer transfer matrices

This file records the sign-invariant interface and the finite maximal-column
construction needed for the Perron-facing layer route.  A real orthogonal
spectral column is only determined up to sign, so the useful statement is that a
chosen column is positive after multiplication by a scalar sign with square one.

The file connects such signed-positive columns to the positive-column radius,
simplicity, strict-ratio, and spin-cancellation API developed in
`LayerPerron.lean`, and proves that the finite maximal spectral column has such
an orientation for an entrywise positive matrix with explicit real orthogonal
spectral data.  It still does not discharge the finite-cardinality prefactor
condition in the certificates, open-slab geometry, thermodynamic limits, or
final hyperplane exponential decay.

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

namespace RealOrthogonalSpectralData

/-- A spectral-data index where the finite eigenvalue family attains its
maximum. -/
noncomputable def maxEigenIndex [Nonempty Ω] {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) : Ω :=
  Classical.choose
    (Finset.exists_max_image (Finset.univ : Finset Ω) E.eigenvalue
      Finset.univ_nonempty)

/-- The eigenvalue at `maxEigenIndex` is maximal among the finite spectral-data
eigenvalues. -/
theorem eigenvalue_le_maxEigenIndex [Nonempty Ω] {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (i : Ω) :
    E.eigenvalue i ≤ E.eigenvalue E.maxEigenIndex :=
  (Classical.choose_spec
    (Finset.exists_max_image (Finset.univ : Finset Ω) E.eigenvalue
      Finset.univ_nonempty)).2 i (Finset.mem_univ i)

/-- Spectral coordinates of a vector in the explicit real orthogonal basis. -/
noncomputable def spectralCoord {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (v : Ω → ℝ) (i : Ω) : ℝ :=
  ∑ x, E.changeOfBasis x i * v x

omit [DecidableEq Ω] in
/-- Move the third index of a finite triple sum to the outside. -/
theorem triple_sum_comm (f : Ω → Ω → Ω → ℝ) :
    (∑ i, ∑ j, ∑ k, f i j k) = ∑ k, ∑ i, ∑ j, f i j k := by
  calc
    (∑ i, ∑ j, ∑ k, f i j k) = ∑ j, ∑ i, ∑ k, f i j k := by
      rw [Finset.sum_comm]
    _ = ∑ j, ∑ k, ∑ i, f i j k := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
    _ = ∑ k, ∑ j, ∑ i, f i j k := by
      rw [Finset.sum_comm]
    _ = ∑ k, ∑ i, ∑ j, f i j k := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]

omit [DecidableEq Ω] in
/-- Square of a finite sum as a double sum. -/
theorem sq_sum_eq_double_sum (a : Ω → ℝ) :
    (∑ i, a i) ^ 2 = ∑ i, ∑ j, a i * a j := by
  rw [pow_two]
  calc
    (∑ i, a i) * ∑ j, a j = ∑ i, a i * ∑ j, a j := by
      rw [Finset.sum_mul]
    _ = ∑ i, ∑ j, a i * a j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]

omit [DecidableEq Ω] in
/-- Pull a scalar through the square of a finite sum in double-sum form. -/
theorem double_sum_mul_eq_mul_sq_sum (lam : ℝ) (a : Ω → ℝ) :
    ∑ i, ∑ j, lam * a i * a j = lam * (∑ i, a i) ^ 2 := by
  calc
    ∑ i, ∑ j, lam * a i * a j
        = ∑ i, (lam * a i) * ∑ j, a j := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
    _ = (∑ i, lam * a i) * ∑ j, a j := by
          rw [Finset.sum_mul]
    _ = lam * (∑ i, a i) ^ 2 := by
          rw [← Finset.mul_sum]
          ring

/-- Entrywise expansion of the matrix represented by real orthogonal spectral
data. -/
theorem matrix_apply_eq_sum {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (i j : Ω) :
    M i j = ∑ k,
      E.changeOfBasis i k * E.eigenvalue k * E.changeOfBasis j k := by
  have h := congr_fun (congr_fun E.diagonalizes i) j
  rw [Matrix.mul_apply] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro k _
  simp [Matrix.mul_diagonal, Matrix.transpose_apply, mul_assoc]

/-- Quadratic form expansion in the explicit real orthogonal spectral basis. -/
theorem matrixQuadraticForm_eq_sum_spectralCoord_sq {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (v : Ω → ℝ) :
    matrixQuadraticForm M v =
      ∑ k, E.eigenvalue k * (E.spectralCoord v k) ^ 2 := by
  unfold matrixQuadraticForm spectralCoord
  simp_rw [E.matrix_apply_eq_sum]
  calc
    (∑ i, ∑ j,
        v i
          * (∑ k, E.changeOfBasis i k * E.eigenvalue k * E.changeOfBasis j k)
          * v j)
        = ∑ i, ∑ j, ∑ k,
            E.eigenvalue k * (E.changeOfBasis i k * v i)
              * (E.changeOfBasis j k * v j) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro k _
          ring
    _ = ∑ k, ∑ i, ∑ j,
          E.eigenvalue k * (E.changeOfBasis i k * v i)
            * (E.changeOfBasis j k * v j) := by
          exact triple_sum_comm (Ω := Ω)
            (fun i j k => E.eigenvalue k * (E.changeOfBasis i k * v i)
              * (E.changeOfBasis j k * v j))
    _ = ∑ k, E.eigenvalue k * (∑ i, E.changeOfBasis i k * v i) ^ 2 := by
          apply Finset.sum_congr rfl
          intro k _
          exact double_sum_mul_eq_mul_sq_sum (Ω := Ω) (E.eigenvalue k)
            (fun i => E.changeOfBasis i k * v i)

/-- Orthogonal spectral coordinates preserve the squared Euclidean norm. -/
theorem sum_spectralCoord_sq {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (v : Ω → ℝ) :
    (∑ k, (E.spectralCoord v k) ^ 2) = vectorSqNorm v := by
  unfold spectralCoord vectorSqNorm
  calc
    (∑ k, (∑ i, E.changeOfBasis i k * v i) ^ 2)
        = ∑ k, ∑ i, ∑ j,
            (E.changeOfBasis i k * v i) * (E.changeOfBasis j k * v j) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [sq_sum_eq_double_sum]
    _ = ∑ i, ∑ j, ∑ k,
          (E.changeOfBasis i k * v i) * (E.changeOfBasis j k * v j) := by
          exact (triple_sum_comm (Ω := Ω)
            (fun i j k => (E.changeOfBasis i k * v i)
              * (E.changeOfBasis j k * v j))).symm
    _ = ∑ i, ∑ j, ((E.changeOfBasis * E.changeOfBasisᵀ) i j) * v i * v j := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          rw [Matrix.mul_apply]
          rw [Finset.sum_mul]
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro k _
          simp [Matrix.transpose_apply]
          ring
    _ = ∑ i, v i ^ 2 := by
          rw [E.orthogonal_right]
          simp [Matrix.one_apply, pow_two]

/-- The squared norm of a spectral-data column is one. -/
theorem vectorSqNorm_changeOfBasis_column {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (i : Ω) :
    vectorSqNorm (fun x => E.changeOfBasis x i) = 1 := by
  unfold vectorSqNorm
  have h := congr_fun (congr_fun E.orthogonal_left i) i
  simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, pow_two,
    mul_comm] using h

omit [DecidableEq Ω] in
/-- The squared norm is unchanged by coordinatewise absolute values. -/
theorem vectorSqNorm_abs (v : Ω → ℝ) :
    vectorSqNorm (fun i => |v i|) = vectorSqNorm v := by
  unfold vectorSqNorm
  simp [sq_abs]

/-- Rayleigh upper bound by the maximal spectral-data eigenvalue. -/
theorem matrixQuadraticForm_le_maxEigenIndex [Nonempty Ω]
    {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M) (v : Ω → ℝ) :
    matrixQuadraticForm M v
      ≤ E.eigenvalue E.maxEigenIndex * vectorSqNorm v := by
  rw [E.matrixQuadraticForm_eq_sum_spectralCoord_sq v]
  calc
    ∑ k, E.eigenvalue k * (E.spectralCoord v k) ^ 2
        ≤ ∑ k, E.eigenvalue E.maxEigenIndex * (E.spectralCoord v k) ^ 2 := by
          exact Finset.sum_le_sum fun k _ =>
            mul_le_mul_of_nonneg_right (E.eigenvalue_le_maxEigenIndex k)
              (sq_nonneg _)
    _ = E.eigenvalue E.maxEigenIndex * ∑ k, (E.spectralCoord v k) ^ 2 := by
          rw [Finset.mul_sum]
    _ = E.eigenvalue E.maxEigenIndex * vectorSqNorm v := by
          rw [E.sum_spectralCoord_sq v]

omit [DecidableEq Ω] in
/-- The quadratic form of a right eigenvector is its eigenvalue times its
squared norm. -/
theorem matrixQuadraticForm_eq_eigenvalue_mul_sqNorm
    {M : Matrix Ω Ω ℝ} (v : Ω → ℝ) {lam : ℝ}
    (hv_eig : M.mulVec v = lam • v) :
    matrixQuadraticForm M v = lam * vectorSqNorm v := by
  unfold matrixQuadraticForm vectorSqNorm
  calc
    ∑ i, ∑ j, v i * M i j * v j
        = ∑ i, v i * M.mulVec v i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = ∑ i, v i * (lam * v i) := by
          apply Finset.sum_congr rfl
          intro i _
          have h := congr_fun hv_eig i
          simpa [Pi.smul_apply, smul_eq_mul] using congrArg (fun t => v i * t) h
    _ = ∑ i, lam * v i ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = lam * ∑ i, v i ^ 2 := by
          rw [Finset.mul_sum]

/-- A spectral-data column that becomes strictly positive after multiplying by
a scalar sign.  Orthogonal eigenvectors are only fixed up to sign, so this is
the sign-invariant positivity package used by the Perron-facing layer API. -/
structure SignedPositiveColumn {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (top : Ω) where
  /-- The scalar sign used to orient the spectral column. -/
  sign : ℝ
  /-- The sign has square one. -/
  sign_mul_self : sign * sign = 1
  /-- The oriented top column is strictly positive. -/
  positive : VectorPositive (fun x => sign * E.changeOfBasis x top)

namespace SignedPositiveColumn

/-- The sign in a signed-positive column is nonzero. -/
theorem sign_ne_zero {M : Matrix Ω Ω ℝ}
    {E : RealOrthogonalSpectralData M} {top : Ω}
    (h : E.SignedPositiveColumn top) : h.sign ≠ 0 := by
  intro hzero
  have : (0 : ℝ) = 1 := by
    simpa [hzero] using h.sign_mul_self
  norm_num at this

/-- The oriented column of a signed-positive column is an eigenvector with the
same eigenvalue as the raw spectral column. -/
theorem mulVec_signedColumn {M : Matrix Ω Ω ℝ}
    {E : RealOrthogonalSpectralData M} {top : Ω}
    (h : E.SignedPositiveColumn top) :
    M.mulVec (fun x => h.sign * E.changeOfBasis x top)
      = E.eigenvalue top • (fun x => h.sign * E.changeOfBasis x top) := by
  change M.mulVec (h.sign • (fun x => E.changeOfBasis x top))
      = E.eigenvalue top • (h.sign • (fun x => E.changeOfBasis x top))
  rw [Matrix.mulVec_smul, E.mulVec_changeOfBasis_column top]
  ext x
  simp [Pi.smul_apply, smul_eq_mul, mul_left_comm]

/-- A signed-positive column gives a strictly positive right eigenpair. -/
theorem strictPositiveRightEigenpair {M : Matrix Ω Ω ℝ}
    {E : RealOrthogonalSpectralData M} {top : Ω}
    (h : E.SignedPositiveColumn top) :
    StrictPositiveRightEigenpair M (E.eigenvalue top)
      (fun x => h.sign * E.changeOfBasis x top) :=
  ⟨h.positive, h.mulVec_signedColumn⟩

/-- If a vector is a scalar multiple of the oriented column, then it is also a
scalar multiple of the raw spectral column. -/
theorem smul_signedColumn_eq_smul_raw {M : Matrix Ω Ω ℝ}
    {E : RealOrthogonalSpectralData M} {top : Ω}
    (h : E.SignedPositiveColumn top) {w : Ω → ℝ} {c : ℝ}
    (hw : w = c • (fun x => h.sign * E.changeOfBasis x top)) :
    ∃ c' : ℝ, w = c' • (fun x => E.changeOfBasis x top) := by
  refine ⟨c * h.sign, ?_⟩
  ext x
  have hx := congr_fun hw x
  simpa [Pi.smul_apply, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using hx

end SignedPositiveColumn

/-- For an entrywise positive matrix with explicit real orthogonal spectral
data, the finite maximal eigenvalue column has a signed-positive orientation. -/
noncomputable def signedPositiveColumn_maxEigenIndex [Nonempty Ω]
    {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M)
    (hM : MatrixEntrywisePositive M) :
    E.SignedPositiveColumn E.maxEigenIndex := by
  let top : Ω := E.maxEigenIndex
  let v : Ω → ℝ := fun x => E.changeOfBasis x top
  have hv_ne : v ≠ 0 := by
    dsimp [v, top]
    exact E.changeOfBasis_column_ne_zero E.maxEigenIndex
  have hexists_i0 : ∃ i, v i ≠ 0 := by
    by_contra h
    apply hv_ne
    ext i
    by_contra hi
    exact h ⟨i, hi⟩
  let i0 : Ω := Classical.choose hexists_i0
  have hi0 : v i0 ≠ 0 := Classical.choose_spec hexists_i0
  have hv_eig : M.mulVec v = E.eigenvalue top • v := by
    dsimp [v, top]
    exact E.mulVec_changeOfBasis_column E.maxEigenIndex
  have hnorm_v : vectorSqNorm v = 1 := by
    dsimp [v, top]
    exact E.vectorSqNorm_changeOfBasis_column E.maxEigenIndex
  have hq_v :
      matrixQuadraticForm M v = E.eigenvalue top := by
    rw [matrixQuadraticForm_eq_eigenvalue_mul_sqNorm v hv_eig, hnorm_v]
    ring
  have hnorm_abs :
      vectorSqNorm (fun i => |v i|) = 1 := by
    rw [vectorSqNorm_abs, hnorm_v]
  have hq_abs_le_top :
      matrixQuadraticForm M (fun i => |v i|) ≤ E.eigenvalue top := by
    have hle := E.matrixQuadraticForm_le_maxEigenIndex (fun i => |v i|)
    simpa [top, hnorm_abs] using hle
  have hq_abs_eq :
      matrixQuadraticForm M (fun i => |v i|) = matrixQuadraticForm M v := by
    exact le_antisymm (by simpa [hq_v] using hq_abs_le_top)
      (matrixQuadraticForm_le_abs hM v)
  have hdef_i0 : ∀ j, |v i0| * |v j| - v i0 * v j = 0 := by
    intro j
    exact abs_defect_eq_zero_of_matrixQuadraticForm_abs_eq hM hq_abs_eq i0 j
  let signData :=
    exists_sign_vectorNonnegative_of_abs_defect_zero hi0 hdef_i0
  let s : ℝ := Classical.choose signData
  have hs_data :
      s * s = 1 ∧ VectorNonnegative (fun j => s * v j) :=
    Classical.choose_spec signData
  have hs_sq : s * s = 1 := hs_data.1
  have hs_nonneg : VectorNonnegative (fun j => s * v j) := hs_data.2
  have hs_ne : s ≠ 0 := by
    intro hs_zero
    have : (0 : ℝ) = 1 := by
      simp [hs_zero] at hs_sq
    norm_num at this
  let w : Ω → ℝ := fun x => s * v x
  have hw_nonneg : VectorNonnegative w := hs_nonneg
  have hw_ne : w ≠ 0 := by
    intro hw_zero
    apply hv_ne
    ext i
    have h := congr_fun hw_zero i
    dsimp [w] at h
    have h' : s * v i = s * 0 := by
      simpa using h
    exact mul_left_cancel₀ hs_ne h'
  have hw_eig : M.mulVec w = E.eigenvalue top • w := by
    change M.mulVec (s • v) = E.eigenvalue top • (s • v)
    rw [Matrix.mulVec_smul, hv_eig]
    ext i
    simp [Pi.smul_apply, smul_eq_mul, mul_assoc, mul_comm]
  refine ⟨s, hs_sq, ?_⟩
  have hw_pos : VectorPositive w :=
    matrixEntrywisePositive_eigenvector_pos_of_nonnegative_nonzero hM hw_eig
      hw_nonneg hw_ne
  simpa [w, v, top] using hw_pos

/-- A signed-positive top column has a positive eigenvalue. -/
theorem eigenvalue_pos_of_signedPositiveColumn [Nonempty Ω]
    {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M)
    (hM : MatrixEntrywisePositive M) (top : Ω)
    (hpos : E.SignedPositiveColumn top) :
    0 < E.eigenvalue top :=
  eigenvalue_pos_of_strictPositiveRightEigenpair hM
    hpos.strictPositiveRightEigenpair

/-- A signed-positive top column bounds every spectral-data eigenvalue in
absolute value. -/
theorem eigenvalue_abs_le_of_signedPositiveColumn [Nonempty Ω]
    {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M)
    (hM : MatrixEntrywisePositive M) (top i : Ω)
    (hpos : E.SignedPositiveColumn top) :
    |E.eigenvalue i| ≤ E.eigenvalue top :=
  abs_eigenvalue_le_of_entrywisePositive_positive_eigenpair hM
    hpos.strictPositiveRightEigenpair
    (E.changeOfBasis_column_ne_zero i)
    (E.mulVec_changeOfBasis_column i)

/-- A signed-positive top column spans the eigenspace for its eigenvalue. -/
theorem eigenspace_simple_of_signedPositiveColumn [Nonempty Ω]
    {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M)
    (hM : MatrixEntrywisePositive M) (top : Ω)
    (hpos : E.SignedPositiveColumn top)
    {w : Ω → ℝ} (hw_eig : M.mulVec w = E.eigenvalue top • w) :
    ∃ c : ℝ, w = c • (fun x => E.changeOfBasis x top) := by
  rcases eigenvector_smul_of_entrywisePositive_positive_eigenpair hM
      hpos.strictPositiveRightEigenpair hw_eig with
    ⟨c, hc⟩
  exact hpos.smul_signedColumn_eq_smul_raw hc

/-- A signed-positive top spectral column gives strict absolute inequality for
every different spectral-data column. -/
theorem eigenvalue_abs_lt_of_signedPositiveColumn [Nonempty Ω]
    {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M)
    (hM : MatrixEntrywisePositive M) (top i : Ω) (hi : i ≠ top)
    (hpos : E.SignedPositiveColumn top) :
    |E.eigenvalue i| < E.eigenvalue top := by
  have hne : E.eigenvalue i ≠ E.eigenvalue top := by
    intro heq
    have hi_eig :
        M.mulVec (fun x => E.changeOfBasis x i)
          = E.eigenvalue top • (fun x => E.changeOfBasis x i) := by
      simpa [heq] using E.mulVec_changeOfBasis_column i
    rcases E.eigenspace_simple_of_signedPositiveColumn hM top hpos hi_eig with
      ⟨c, hc⟩
    exact E.changeOfBasis_columns_not_smul hi c hc
  exact abs_eigenvalue_lt_of_entrywisePositive_positive_eigenpair hM
    hpos.strictPositiveRightEigenpair
    (E.changeOfBasis_column_ne_zero i)
    (E.mulVec_changeOfBasis_column i) hne

/-- A signed-positive spectral-data top column gives some strict finite
subdominant ratio for all non-top spectral-data eigenvalues.  The finite
certificate prefactor condition remains a separate quantitative input. -/
theorem exists_subdominant_abs_ratio_of_signedPositiveColumn [Nonempty Ω]
    {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M)
    (hM : MatrixEntrywisePositive M) (top : Ω)
    (hpos : E.SignedPositiveColumn top) :
    ∃ theta : ℝ, 0 ≤ theta ∧ theta < 1 ∧
      ∀ i, i ≠ top → |E.eigenvalue i| ≤ theta * E.eigenvalue top := by
  let rest : Finset Ω := Finset.univ.erase top
  have htop_pos : 0 < E.eigenvalue top :=
    E.eigenvalue_pos_of_signedPositiveColumn hM top hpos
  by_cases hrest : rest = ∅
  · refine ⟨0, le_rfl, zero_lt_one, ?_⟩
    intro i hi
    have himem : i ∈ rest := by
      exact Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩
    rw [hrest] at himem
    simp at himem
  · obtain ⟨i0, hi0, hmax⟩ :=
      Finset.exists_max_image rest (fun i => |E.eigenvalue i| / E.eigenvalue top)
        (Finset.nonempty_iff_ne_empty.mpr hrest)
    refine ⟨|E.eigenvalue i0| / E.eigenvalue top, ?_, ?_, ?_⟩
    · exact div_nonneg (abs_nonneg _) htop_pos.le
    · have hi0_ne : i0 ≠ top := (Finset.mem_erase.mp hi0).1
      have hlt := E.eigenvalue_abs_lt_of_signedPositiveColumn hM top i0 hi0_ne hpos
      exact (div_lt_one htop_pos).mpr hlt
    · intro i hi
      have himem : i ∈ rest := Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩
      exact (div_le_iff₀ htop_pos).mp (hmax i himem)

/-- The maximal spectral-data column has a positive eigenvalue for an
entrywise positive matrix. -/
theorem eigenvalue_pos_maxEigenIndex [Nonempty Ω]
    {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M)
    (hM : MatrixEntrywisePositive M) :
    0 < E.eigenvalue E.maxEigenIndex :=
  E.eigenvalue_pos_of_signedPositiveColumn hM E.maxEigenIndex
    (E.signedPositiveColumn_maxEigenIndex hM)

/-- The eigenvalue at the maximal signed-positive column bounds all
spectral-data eigenvalues in absolute value. -/
theorem eigenvalue_abs_le_maxEigenIndex [Nonempty Ω]
    {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M)
    (hM : MatrixEntrywisePositive M) (i : Ω) :
    |E.eigenvalue i| ≤ E.eigenvalue E.maxEigenIndex :=
  E.eigenvalue_abs_le_of_signedPositiveColumn hM E.maxEigenIndex i
    (E.signedPositiveColumn_maxEigenIndex hM)

/-- The maximal signed-positive column spans its eigenspace. -/
theorem eigenspace_simple_maxEigenIndex [Nonempty Ω]
    {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M)
    (hM : MatrixEntrywisePositive M) {w : Ω → ℝ}
    (hw_eig : M.mulVec w = E.eigenvalue E.maxEigenIndex • w) :
    ∃ c : ℝ, w = c • (fun x => E.changeOfBasis x E.maxEigenIndex) :=
  E.eigenspace_simple_of_signedPositiveColumn hM E.maxEigenIndex
    (E.signedPositiveColumn_maxEigenIndex hM) hw_eig

/-- Every non-maximal spectral-data column has strictly smaller absolute
eigenvalue than the maximal signed-positive column. -/
theorem eigenvalue_abs_lt_maxEigenIndex [Nonempty Ω]
    {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M)
    (hM : MatrixEntrywisePositive M) (i : Ω) (hi : i ≠ E.maxEigenIndex) :
    |E.eigenvalue i| < E.eigenvalue E.maxEigenIndex :=
  E.eigenvalue_abs_lt_of_signedPositiveColumn hM E.maxEigenIndex i hi
    (E.signedPositiveColumn_maxEigenIndex hM)

/-- A canonical finite subdominant ratio attached to the maximal signed-positive
spectral-data column.  The quantitative certificate prefactor smallness
condition remains a separate hypothesis. -/
noncomputable def subdominantRatio_maxEigenIndex [Nonempty Ω]
    {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M)
    (hM : MatrixEntrywisePositive M) : ℝ :=
  Classical.choose
    (E.exists_subdominant_abs_ratio_of_signedPositiveColumn hM E.maxEigenIndex
      (E.signedPositiveColumn_maxEigenIndex hM))

/-- Specification of the canonical finite subdominant ratio at
`maxEigenIndex`. -/
theorem subdominantRatio_maxEigenIndex_spec [Nonempty Ω]
    {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M)
    (hM : MatrixEntrywisePositive M) :
    0 ≤ E.subdominantRatio_maxEigenIndex hM ∧
      E.subdominantRatio_maxEigenIndex hM < 1 ∧
      ∀ i, i ≠ E.maxEigenIndex →
        |E.eigenvalue i| ≤
          E.subdominantRatio_maxEigenIndex hM * E.eigenvalue E.maxEigenIndex :=
  Classical.choose_spec
    (E.exists_subdominant_abs_ratio_of_signedPositiveColumn hM E.maxEigenIndex
      (E.signedPositiveColumn_maxEigenIndex hM))

/-- Nonnegativity of the canonical finite subdominant ratio at
`maxEigenIndex`. -/
theorem subdominantRatio_maxEigenIndex_nonneg [Nonempty Ω]
    {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M)
    (hM : MatrixEntrywisePositive M) :
    0 ≤ E.subdominantRatio_maxEigenIndex hM :=
  (E.subdominantRatio_maxEigenIndex_spec hM).1

/-- The canonical finite subdominant ratio at `maxEigenIndex` is strictly
smaller than one. -/
theorem subdominantRatio_maxEigenIndex_lt_one [Nonempty Ω]
    {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M)
    (hM : MatrixEntrywisePositive M) :
    E.subdominantRatio_maxEigenIndex hM < 1 :=
  (E.subdominantRatio_maxEigenIndex_spec hM).2.1

/-- The canonical finite subdominant ratio bounds every non-maximal spectral
eigenvalue in absolute value. -/
theorem eigenvalue_abs_le_subdominantRatio_maxEigenIndex [Nonempty Ω]
    {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M)
    (hM : MatrixEntrywisePositive M) (i : Ω) (hi : i ≠ E.maxEigenIndex) :
    |E.eigenvalue i| ≤
      E.subdominantRatio_maxEigenIndex hM * E.eigenvalue E.maxEigenIndex :=
  (E.subdominantRatio_maxEigenIndex_spec hM).2.2 i hi

end RealOrthogonalSpectralData

/-! ## Layer wrappers for signed-positive columns -/

/-- The maximal column of the Hermitian spectral data for a positive balanced
layer transfer matrix has a signed-positive orientation. -/
noncomputable def layerSymmetricTransfer_signedPositiveColumn_maxEigenIndex
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (hk_symm : ∀ ω η, k ω η = k η ω) :
    let E := layerSymmetricTransferOrthogonalSpectralData u k hk_symm
    E.SignedPositiveColumn E.maxEigenIndex := by
  letI : Nonempty (LayerState S) := ⟨default⟩
  let E := layerSymmetricTransferOrthogonalSpectralData u k hk_symm
  exact E.signedPositiveColumn_maxEigenIndex
    (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos)

/-- The canonical finite subdominant ratio attached to the maximal
signed-positive column of the Hermitian spectral data for the balanced layer
transfer matrix. -/
noncomputable def layerSymmetricTransfer_subdominantRatio_maxEigenIndex
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (hk_symm : ∀ ω η, k ω η = k η ω) : ℝ := by
  letI : Nonempty (LayerState S) := ⟨default⟩
  let E := layerSymmetricTransferOrthogonalSpectralData u k hk_symm
  exact E.subdominantRatio_maxEigenIndex
    (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos)

/-- The canonical finite subdominant ratio for the Hermitian balanced layer
transfer matrix is strictly smaller than one. -/
theorem layerSymmetricTransfer_subdominantRatio_maxEigenIndex_lt_one
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (hk_symm : ∀ ω η, k ω η = k η ω) :
    layerSymmetricTransfer_subdominantRatio_maxEigenIndex u k hu hk_pos hk_symm < 1 := by
  letI : Nonempty (LayerState S) := ⟨default⟩
  let E := layerSymmetricTransferOrthogonalSpectralData u k hk_symm
  simpa [layerSymmetricTransfer_subdominantRatio_maxEigenIndex, E] using
    E.subdominantRatio_maxEigenIndex_lt_one
      (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos)

/-- A signed-positive balanced-layer spectral column bounds every spectral-data
eigenvalue in absolute value. -/
theorem layerSymmetricTransfer_eigenvalue_abs_le_of_signedPositiveColumn
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (top i : LayerState S) (hpos : E.SignedPositiveColumn top) :
    |E.eigenvalue i| ≤ E.eigenvalue top := by
  letI : Nonempty (LayerState S) := ⟨top⟩
  exact E.eigenvalue_abs_le_of_signedPositiveColumn
    (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos) top i hpos

/-- A signed-positive balanced-layer spectral column spans its eigenspace. -/
theorem layerSymmetricTransfer_signedPositiveColumn_eigenspace_simple
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (top : LayerState S) (hpos : E.SignedPositiveColumn top)
    {w : LayerState S → ℝ}
    (hw_eig : (layerSymmetricTransferMatrix u k).mulVec w =
      E.eigenvalue top • w) :
    ∃ c : ℝ, w = c • (fun ω => E.changeOfBasis ω top) := by
  letI : Nonempty (LayerState S) := ⟨top⟩
  exact E.eigenspace_simple_of_signedPositiveColumn
    (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos) top hpos hw_eig

/-- A signed-positive balanced-layer spectral column gives strict absolute
inequality for each different spectral-data column. -/
theorem layerSymmetricTransfer_eigenvalue_abs_lt_of_signedPositiveColumn
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (top i : LayerState S) (hi : i ≠ top)
    (hpos : E.SignedPositiveColumn top) :
    |E.eigenvalue i| < E.eigenvalue top := by
  letI : Nonempty (LayerState S) := ⟨top⟩
  exact E.eigenvalue_abs_lt_of_signedPositiveColumn
    (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos) top i hi hpos

/-- A signed-positive balanced-layer spectral column gives some strict finite
subdominant ratio for all non-top spectral-data eigenvalues. -/
theorem layerSymmetricTransfer_exists_subdominant_abs_ratio_of_signedPositiveColumn
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (top : LayerState S) (hpos : E.SignedPositiveColumn top) :
    ∃ theta : ℝ, 0 ≤ theta ∧ theta < 1 ∧
      ∀ i, i ≠ top → |E.eigenvalue i| ≤ theta * E.eigenvalue top := by
  letI : Nonempty (LayerState S) := ⟨top⟩
  exact E.exists_subdominant_abs_ratio_of_signedPositiveColumn
    (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos) top hpos

/-! ## Signed-positive spin-observable certificate constructors -/

/-- A signed-positive spectral column of a balanced layer transfer matrix is
flip-even when the layer weights and transition weights are invariant under
global spin flip. -/
theorem layerSymmetricTransfer_signedPositiveColumn_flip_even
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (top : LayerState S) (hpos : E.SignedPositiveColumn top) :
    ∀ ω : LayerState S,
      E.changeOfBasis (layerStateFlipEquiv S ω) top = E.changeOfBasis ω top := by
  letI : Nonempty (LayerState S) := ⟨top⟩
  let v : LayerState S → ℝ := fun ω => hpos.sign * E.changeOfBasis ω top
  have hveig :
      (layerSymmetricTransferMatrix u k).mulVec v = E.eigenvalue top • v :=
    hpos.mulVec_signedColumn
  have hsimple :
      ∀ w : LayerState S → ℝ,
        (layerSymmetricTransferMatrix u k).mulVec w = E.eigenvalue top • w →
          ∃ c : ℝ, w = c • v := by
    intro w hw
    exact eigenvector_smul_of_entrywisePositive_positive_eigenpair
      (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos)
      hpos.strictPositiveRightEigenpair hw
  have hsigned_even :
      ∀ ω : LayerState S,
        v (layerStateFlipEquiv S ω) = v ω :=
    vectorPositive_eigenvector_flip_even_of_simple_eigenspace
      (layerStateFlipEquiv S)
      (fun ω => layerStateFlipEquiv_involutive S ω)
      hpos.positive hveig
      (layerSymmetricTransferMatrix_mulVec_comp_equiv u k (layerStateFlipEquiv S)
        hu_flip hk_flip)
      hsimple
  intro ω
  exact mul_left_cancel₀ hpos.sign_ne_zero (hsigned_even ω)

/-- Spin-observable constructor using a signed-positive dominant column.  The
flip-even marked-channel cancellation is derived after orienting the spectral
column by its sign. -/
noncomputable def
    layerBalancedMinSpectralGapCertificate_of_orthogonalDominantBounds_signedPositiveColumnFlipSpin
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (top : LayerState S) (scale theta : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (partitionPrefactor_small :
      (((Fintype.card (LayerState S) - 1 : ℕ) : ℝ) * theta) < 1)
    (dominant_eigenvalue : E.eigenvalue top = scale)
    (subdominant_abs_le : ∀ i, i ≠ top → |E.eigenvalue i| ≤ theta * scale)
    (dominant_column_signed_pos : E.SignedPositiveColumn top) :
    LayerBalancedMinSpectralGapCertificate u k (layerSpinAt x) :=
  layerBalancedMinSpectralGapCertificate_of_orthogonalDominantBounds_flipEvenSpin
    u k x E top scale theta scale_pos theta_nonneg theta_lt_one
    partitionPrefactor_small dominant_eigenvalue subdominant_abs_le
    (layerSymmetricTransfer_signedPositiveColumn_flip_even
      u k hu hk_pos hu_flip hk_flip E top dominant_column_signed_pos)

/-- Spin-observable constructor using a signed-positive dominant column with
the transfer scale fixed to that column's eigenvalue. -/
noncomputable def
layerBalancedMinSpectralGapCertificate_of_orthogonalSubdominantBounds_signedPositiveColumnFlipSpin
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (top : LayerState S) (theta : ℝ)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (partitionPrefactor_small :
      (((Fintype.card (LayerState S) - 1 : ℕ) : ℝ) * theta) < 1)
    (subdominant_abs_le :
      ∀ i, i ≠ top → |E.eigenvalue i| ≤ theta * E.eigenvalue top)
    (dominant_column_signed_pos : E.SignedPositiveColumn top) :
    LayerBalancedMinSpectralGapCertificate u k (layerSpinAt x) := by
  letI : Nonempty (LayerState S) := ⟨top⟩
  exact
    layerBalancedMinSpectralGapCertificate_of_orthogonalDominantBounds_signedPositiveColumnFlipSpin
      u k x hu hk_pos hu_flip hk_flip E top (E.eigenvalue top) theta
      (E.eigenvalue_pos_of_signedPositiveColumn
        (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos) top
        dominant_column_signed_pos)
      theta_nonneg theta_lt_one partitionPrefactor_small rfl subdominant_abs_le
      dominant_column_signed_pos

/-! ## Maximal-column certificate constructors -/

/-- Orthogonal spectral-data constructor with the transfer scale and
subdominant ratio fixed by the maximal signed-positive spectral column.

The finite prefactor condition
`((Fintype.card Ω - 1) * theta) < 1` remains an explicit quantitative input. -/
noncomputable def layerBalancedMinSpectralGapCertificate_of_orthogonalMaxEigenIndex
    [Nonempty Ω]
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (hu : ∀ a, 0 < u a) (hk_pos : ∀ a b, 0 < k a b)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (partitionPrefactor_small :
      (((Fintype.card Ω - 1 : ℕ) : ℝ) *
        E.subdominantRatio_maxEigenIndex
          (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos)) < 1)
    (dominant_markedDiagonal_zero :
      E.markedMatrix f E.maxEigenIndex E.maxEigenIndex = 0) :
    LayerBalancedMinSpectralGapCertificate u k f := by
  let hM := layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos
  exact layerBalancedMinSpectralGapCertificate_of_orthogonalDominantBounds
    u k f E E.maxEigenIndex (E.eigenvalue E.maxEigenIndex)
    (E.subdominantRatio_maxEigenIndex hM)
    (E.eigenvalue_pos_maxEigenIndex hM)
    (E.subdominantRatio_maxEigenIndex_nonneg hM)
    (E.subdominantRatio_maxEigenIndex_lt_one hM)
    partitionPrefactor_small rfl
    (E.eigenvalue_abs_le_subdominantRatio_maxEigenIndex hM)
    dominant_markedDiagonal_zero

/-- Hermitian spectral-data constructor with the transfer scale and
subdominant ratio fixed by the maximal signed-positive spectral column. -/
noncomputable def layerBalancedMinSpectralGapCertificate_of_layerHermitianMaxEigenIndex
    [Nonempty Ω]
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (hu : ∀ a, 0 < u a) (hk_pos : ∀ a b, 0 < k a b)
    (hk : ∀ a b, k a b = k b a)
    (partitionPrefactor_small :
      (((Fintype.card Ω - 1 : ℕ) : ℝ) *
        (layerSymmetricTransferOrthogonalSpectralData u k hk).subdominantRatio_maxEigenIndex
          (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos)) < 1)
    (dominant_markedDiagonal_zero :
      (layerSymmetricTransferOrthogonalSpectralData u k hk).markedMatrix f
        (layerSymmetricTransferOrthogonalSpectralData u k hk).maxEigenIndex
        (layerSymmetricTransferOrthogonalSpectralData u k hk).maxEigenIndex = 0) :
    LayerBalancedMinSpectralGapCertificate u k f :=
  layerBalancedMinSpectralGapCertificate_of_orthogonalMaxEigenIndex u k f hu hk_pos
    (layerSymmetricTransferOrthogonalSpectralData u k hk)
    partitionPrefactor_small dominant_markedDiagonal_zero

/-- Orthogonal max-index certificate whose finite prefactor smallness is
discharged by a one-element state space. -/
noncomputable def layerBalancedMinSpectralGapCertificate_of_orthogonalMaxEigenIndex_cardOne
    [Nonempty Ω]
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (hu : ∀ a, 0 < u a) (hk_pos : ∀ a b, 0 < k a b)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (hcard : Fintype.card Ω = 1)
    (dominant_markedDiagonal_zero :
      E.markedMatrix f E.maxEigenIndex E.maxEigenIndex = 0) :
    LayerBalancedMinSpectralGapCertificate u k f :=
  layerBalancedMinSpectralGapCertificate_of_orthogonalMaxEigenIndex u k f hu hk_pos E
    (finiteSpectralPartitionPrefactor_small_of_card_eq_one Ω hcard)
    dominant_markedDiagonal_zero

/-- Orthogonal max-index certificate whose finite prefactor smallness is
discharged by an inverse-cardinality bound on the canonical subdominant
ratio. -/
noncomputable def
    layerBalancedMinSpectralGapCertificate_of_orthogonalMaxEigenIndex_ratioSmall
    [Nonempty Ω]
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (hu : ∀ a, 0 < u a) (hk_pos : ∀ a b, 0 < k a b)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (hcard : 1 < Fintype.card Ω)
    (hratio :
      E.subdominantRatio_maxEigenIndex
          (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos)
        < (((Fintype.card Ω - 1 : ℕ) : ℝ))⁻¹)
    (dominant_markedDiagonal_zero :
      E.markedMatrix f E.maxEigenIndex E.maxEigenIndex = 0) :
    LayerBalancedMinSpectralGapCertificate u k f :=
  layerBalancedMinSpectralGapCertificate_of_orthogonalMaxEigenIndex u k f hu hk_pos E
    (finiteSpectralPartitionPrefactor_small_of_lt_inv_cardSubOne Ω hcard hratio)
    dominant_markedDiagonal_zero

/-- Hermitian max-index certificate whose finite prefactor smallness is
discharged by a one-element state space. -/
noncomputable def layerBalancedMinSpectralGapCertificate_of_layerHermitianMaxEigenIndex_cardOne
    [Nonempty Ω]
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (hu : ∀ a, 0 < u a) (hk_pos : ∀ a b, 0 < k a b)
    (hk : ∀ a b, k a b = k b a)
    (hcard : Fintype.card Ω = 1)
    (dominant_markedDiagonal_zero :
      (layerSymmetricTransferOrthogonalSpectralData u k hk).markedMatrix f
        (layerSymmetricTransferOrthogonalSpectralData u k hk).maxEigenIndex
        (layerSymmetricTransferOrthogonalSpectralData u k hk).maxEigenIndex = 0) :
    LayerBalancedMinSpectralGapCertificate u k f :=
  layerBalancedMinSpectralGapCertificate_of_layerHermitianMaxEigenIndex
    u k f hu hk_pos hk
    (finiteSpectralPartitionPrefactor_small_of_card_eq_one Ω hcard)
    dominant_markedDiagonal_zero

/-- Hermitian max-index certificate whose finite prefactor smallness is
discharged by an inverse-cardinality bound on the canonical subdominant
ratio. -/
noncomputable def
    layerBalancedMinSpectralGapCertificate_of_layerHermitianMaxEigenIndex_ratioSmall
    [Nonempty Ω]
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (hu : ∀ a, 0 < u a) (hk_pos : ∀ a b, 0 < k a b)
    (hk : ∀ a b, k a b = k b a)
    (hcard : 1 < Fintype.card Ω)
    (hratio :
      (layerSymmetricTransferOrthogonalSpectralData u k hk).subdominantRatio_maxEigenIndex
          (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos)
        < (((Fintype.card Ω - 1 : ℕ) : ℝ))⁻¹)
    (dominant_markedDiagonal_zero :
      (layerSymmetricTransferOrthogonalSpectralData u k hk).markedMatrix f
        (layerSymmetricTransferOrthogonalSpectralData u k hk).maxEigenIndex
        (layerSymmetricTransferOrthogonalSpectralData u k hk).maxEigenIndex = 0) :
    LayerBalancedMinSpectralGapCertificate u k f :=
  layerBalancedMinSpectralGapCertificate_of_layerHermitianMaxEigenIndex
    u k f hu hk_pos hk
    (finiteSpectralPartitionPrefactor_small_of_lt_inv_cardSubOne Ω hcard hratio)
    dominant_markedDiagonal_zero

/-- Spin-observable constructor using the maximal signed-positive spectral
column.  The signed-positive column gives flip-even dominant-channel
cancellation before entering the min-separation certificate route. -/
noncomputable def
    layerBalancedMinSpectralGapCertificate_of_orthogonalMaxEigenIndexFlipSpin
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (partitionPrefactor_small :
      (((Fintype.card (LayerState S) - 1 : ℕ) : ℝ) *
        E.subdominantRatio_maxEigenIndex
          (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos)) < 1) :
    LayerBalancedMinSpectralGapCertificate u k (layerSpinAt x) := by
  letI : Nonempty (LayerState S) := ⟨default⟩
  let hM := layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos
  exact
    layerBalancedMinSpectralGapCertificate_of_orthogonalDominantBounds_signedPositiveColumnFlipSpin
      u k x hu hk_pos hu_flip hk_flip E E.maxEigenIndex
      (E.eigenvalue E.maxEigenIndex)
      (E.subdominantRatio_maxEigenIndex hM)
      (E.eigenvalue_pos_maxEigenIndex hM)
      (E.subdominantRatio_maxEigenIndex_nonneg hM)
      (E.subdominantRatio_maxEigenIndex_lt_one hM)
      partitionPrefactor_small rfl
      (E.eigenvalue_abs_le_subdominantRatio_maxEigenIndex hM)
      (E.signedPositiveColumn_maxEigenIndex hM)

/-- Hermitian spin-observable constructor using the maximal signed-positive
spectral column of the balanced layer transfer matrix. -/
noncomputable def
    layerBalancedMinSpectralGapCertificate_of_layerHermitianMaxEigenIndexFlipSpin
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (hk : ∀ ω η, k ω η = k η ω)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (partitionPrefactor_small :
      (((Fintype.card (LayerState S) - 1 : ℕ) : ℝ) *
        layerSymmetricTransfer_subdominantRatio_maxEigenIndex u k hu hk_pos hk) < 1) :
    LayerBalancedMinSpectralGapCertificate u k (layerSpinAt x) := by
  letI : Nonempty (LayerState S) := ⟨default⟩
  let E := layerSymmetricTransferOrthogonalSpectralData u k hk
  exact
    layerBalancedMinSpectralGapCertificate_of_orthogonalMaxEigenIndexFlipSpin
      u k x hu hk_pos hu_flip hk_flip E
      (by
        simpa [layerSymmetricTransfer_subdominantRatio_maxEigenIndex, E] using
          partitionPrefactor_small)

/-- Orthogonal max-index spin certificate whose finite prefactor smallness is
discharged by a one-element layer-state space. -/
noncomputable def
    layerBalancedMinSpectralGapCertificate_of_orthogonalMaxEigenIndexFlipSpin_cardOne
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (hcard : Fintype.card (LayerState S) = 1) :
    LayerBalancedMinSpectralGapCertificate u k (layerSpinAt x) :=
  layerBalancedMinSpectralGapCertificate_of_orthogonalMaxEigenIndexFlipSpin
    u k x hu hk_pos hu_flip hk_flip E
    (finiteSpectralPartitionPrefactor_small_of_card_eq_one (LayerState S) hcard)

/-- Orthogonal max-index spin certificate whose finite prefactor smallness is
discharged by an inverse-cardinality bound on the canonical subdominant
ratio. -/
noncomputable def
    layerBalancedMinSpectralGapCertificate_of_orthogonalMaxEigenIndexFlipSpin_ratioSmall
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (hcard : 1 < Fintype.card (LayerState S))
    (hratio :
      E.subdominantRatio_maxEigenIndex
          (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos)
        < (((Fintype.card (LayerState S) - 1 : ℕ) : ℝ))⁻¹) :
    LayerBalancedMinSpectralGapCertificate u k (layerSpinAt x) :=
  layerBalancedMinSpectralGapCertificate_of_orthogonalMaxEigenIndexFlipSpin
    u k x hu hk_pos hu_flip hk_flip E
    (finiteSpectralPartitionPrefactor_small_of_lt_inv_cardSubOne
      (LayerState S) hcard hratio)

/-- Orthogonal max-index spin certificate for a one-site transverse layer.  In
this two-state layer case, the already proved strict canonical ratio `< 1`
discharges the finite prefactor smallness condition. -/
noncomputable def
    layerBalancedMinSpectralGapCertificate_of_orthogonalMaxEigenIndexFlipSpin_oneSite
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (hcard : Fintype.card S = 1) :
    LayerBalancedMinSpectralGapCertificate u k (layerSpinAt x) := by
  letI : Nonempty (LayerState S) := ⟨default⟩
  let hM := layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos
  exact
    layerBalancedMinSpectralGapCertificate_of_orthogonalMaxEigenIndexFlipSpin
      u k x hu hk_pos hu_flip hk_flip E
      (finiteSpectralPartitionPrefactor_small_of_layerState_card_eq_one S hcard
        (E.subdominantRatio_maxEigenIndex_lt_one hM))

/-- Hermitian max-index spin certificate whose finite prefactor smallness is
discharged by a one-element layer-state space. -/
noncomputable def
    layerBalancedMinSpectralGapCertificate_of_layerHermitianMaxEigenIndexFlipSpin_cardOne
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (hk : ∀ ω η, k ω η = k η ω)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (hcard : Fintype.card (LayerState S) = 1) :
    LayerBalancedMinSpectralGapCertificate u k (layerSpinAt x) :=
  layerBalancedMinSpectralGapCertificate_of_layerHermitianMaxEigenIndexFlipSpin
    u k x hu hk_pos hk hu_flip hk_flip
    (finiteSpectralPartitionPrefactor_small_of_card_eq_one (LayerState S) hcard)

/-- Hermitian max-index spin certificate whose finite prefactor smallness is
discharged by an inverse-cardinality bound on the canonical subdominant
ratio. -/
noncomputable def
    layerBalancedMinSpectralGapCertificate_of_layerHermitianMaxEigenIndexFlipSpin_ratioSmall
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (hk : ∀ ω η, k ω η = k η ω)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (hcard : 1 < Fintype.card (LayerState S))
    (hratio :
      layerSymmetricTransfer_subdominantRatio_maxEigenIndex u k hu hk_pos hk
        < (((Fintype.card (LayerState S) - 1 : ℕ) : ℝ))⁻¹) :
    LayerBalancedMinSpectralGapCertificate u k (layerSpinAt x) :=
  layerBalancedMinSpectralGapCertificate_of_layerHermitianMaxEigenIndexFlipSpin
    u k x hu hk_pos hk hu_flip hk_flip
    (finiteSpectralPartitionPrefactor_small_of_lt_inv_cardSubOne
      (LayerState S) hcard hratio)

/-- Hermitian max-index spin certificate for a one-site transverse layer.  In
this two-state layer case, the already proved strict canonical ratio `< 1`
discharges the finite prefactor smallness condition. -/
noncomputable def
    layerBalancedMinSpectralGapCertificate_of_layerHermitianMaxEigenIndexFlipSpin_oneSite
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (hk : ∀ ω η, k ω η = k η ω)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (hcard : Fintype.card S = 1) :
    LayerBalancedMinSpectralGapCertificate u k (layerSpinAt x) :=
  layerBalancedMinSpectralGapCertificate_of_layerHermitianMaxEigenIndexFlipSpin
    u k x hu hk_pos hk hu_flip hk_flip
    (finiteSpectralPartitionPrefactor_small_of_layerState_card_eq_one S hcard
      (layerSymmetricTransfer_subdominantRatio_maxEigenIndex_lt_one
        u k hu hk_pos hk))

end TransferMatrix

end IsingModel

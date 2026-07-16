import IsingModel.TransferMatrix.LayerPerron
import IsingModel.TransferMatrix.LayerPerronExistence.QuadraticForm

/-!
# Real orthogonal spectral data and signed positive columns (GJ §17.1)

The `RealOrthogonalSpectralData` namespace: the maximal eigen-index, spectral
coordinates and the Rayleigh bound, the `SignedPositiveColumn` structure
recording the sign-invariant positivity package, and the construction of a
signed-positive orientation for the maximal spectral column of an entrywise
positive matrix together with its simplicity, strict-ratio and canonical
subdominant-ratio consequences.  Part of the `LayerPerronExistence`
signed-positive dominant column split.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.1, pp. 304--306.
-/

namespace IsingModel

namespace TransferMatrix

open Matrix

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

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

end TransferMatrix

end IsingModel

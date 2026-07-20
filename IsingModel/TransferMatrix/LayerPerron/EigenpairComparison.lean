import IsingModel.TransferMatrix.LayerSpectral.Positivity
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Positive/simple Perron bridge (1/5): Collatz--Wielandt eigenvalue comparison

Structural split (1/5) of `TransferMatrix.LayerPerron`.  This child holds the
Collatz--Wielandt-style comparison of an arbitrary real eigenvector against a strictly
positive one: the optimal attained relative scale (in absolute value and one-sided), the
one-dimensionality of the eigenspace of a strictly positive eigenpair of an entrywise
positive matrix, and the resulting weak and strict absolute bounds on all real eigenvalues.
See the `IsingModel.TransferMatrix.LayerPerron` facade module for the full contents
overview.
-/

namespace IsingModel

namespace TransferMatrix

open Matrix

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-! ## Positive-column eigenvalue bounds -/

omit [Fintype Ω] [DecidableEq Ω] in
/-- A finite nonzero vector is bounded in absolute value by a positive vector,
with the optimal relative scale attained at some coordinate. -/
theorem exists_positive_vector_abs_bound_attained [Finite Ω] [Nonempty Ω]
    {v w : Ω → ℝ} (hv : VectorPositive v) (hw : w ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ (∀ i, |w i| ≤ C * v i) ∧ ∃ i, |w i| = C * v i := by
  classical
  letI := Fintype.ofFinite Ω
  obtain ⟨i0, hi0⟩ : ∃ i, w i ≠ 0 := by
    by_contra h
    apply hw
    ext i
    by_contra hwi
    exact h ⟨i, hwi⟩
  obtain ⟨i, _hi, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset Ω) (fun j => |w j| / v j)
      Finset.univ_nonempty
  refine ⟨|w i| / v i, ?_, ?_, ⟨i, ?_⟩⟩
  · have hratio0 : 0 < |w i0| / v i0 := div_pos (abs_pos.mpr hi0) (hv i0)
    exact hratio0.trans_le (hmax i0 (Finset.mem_univ i0))
  · intro j
    exact (div_le_iff₀ (hv j)).mp (hmax j (Finset.mem_univ j))
  · exact (div_mul_cancel₀ |w i| (hv i).ne').symm

omit [Fintype Ω] [DecidableEq Ω] in
/-- A finite vector is bounded above by a scalar multiple of a positive vector,
with the optimal relative scale attained at some coordinate. -/
theorem exists_positive_vector_upper_bound_attained [Finite Ω] [Nonempty Ω]
    {v w : Ω → ℝ} (hv : VectorPositive v) :
    ∃ C : ℝ, (∀ i, w i ≤ C * v i) ∧ ∃ i, w i = C * v i := by
  classical
  letI := Fintype.ofFinite Ω
  obtain ⟨i, _hi, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset Ω) (fun j => w j / v j)
      Finset.univ_nonempty
  refine ⟨w i / v i, ?_, ⟨i, ?_⟩⟩
  · intro j
    exact (div_le_iff₀ (hv j)).mp (hmax j (Finset.mem_univ j))
  · exact (div_mul_cancel₀ (w i) (hv i).ne').symm

omit [DecidableEq Ω] in
/-- For an entrywise positive matrix, a strictly positive right eigenvector
spans the whole eigenspace for its eigenvalue. -/
theorem eigenvector_smul_of_entrywisePositive_positive_eigenpair [Nonempty Ω]
    {M : Matrix Ω Ω ℝ} (hM : MatrixEntrywisePositive M)
    {lam : ℝ} {v : Ω → ℝ} (hv : StrictPositiveRightEigenpair M lam v)
    {w : Ω → ℝ} (hw_eig : M.mulVec w = lam • w) :
    ∃ C : ℝ, w = C • v := by
  rcases exists_positive_vector_upper_bound_attained (v := v) (w := w) hv.1 with
    ⟨C, hbound, ⟨i0, hatt⟩⟩
  let z : Ω → ℝ := fun i => C * v i - w i
  have hz_nonneg : ∀ i, 0 ≤ z i := by
    intro i
    dsimp [z]
    linarith [hbound i]
  have hz_i0 : z i0 = 0 := by
    dsimp [z]
    linarith [hatt]
  have hz_eig : M.mulVec z = lam • z := by
    ext i
    have hv_i := congr_fun hv.2 i
    have hw_i := congr_fun hw_eig i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hv_i hw_i ⊢
    calc
      ∑ j, M i j * (C * v j - w j)
          = C * (∑ j, M i j * v j) - ∑ j, M i j * w j := by
            rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro j _hj
            ring
      _ = lam * (C * v i - w i) := by
            rw [hv_i, hw_i]
            ring
  have hsum_zero : ∑ j, M i0 j * z j = 0 := by
    have h := congr_fun hz_eig i0
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
    rw [hz_i0] at h
    simpa using h
  have hz_zero : ∀ j, z j = 0 := by
    intro j
    have hterm_nonneg : ∀ k, 0 ≤ M i0 k * z k := by
      intro k
      exact mul_nonneg (hM i0 k).le (hz_nonneg k)
    have hterm_le_zero : M i0 j * z j ≤ 0 := by
      calc
        M i0 j * z j ≤ ∑ k, M i0 k * z k :=
          Finset.single_le_sum (fun k _hk => hterm_nonneg k) (Finset.mem_univ j)
        _ = 0 := hsum_zero
    have hterm_zero : M i0 j * z j = 0 :=
      le_antisymm hterm_le_zero (hterm_nonneg j)
    rcases mul_eq_zero.mp hterm_zero with hMzero | hz
    · exact False.elim ((hM i0 j).ne' hMzero)
    · exact hz
  refine ⟨C, ?_⟩
  ext i
  have hz := hz_zero i
  dsimp [z] at hz
  simp [Pi.smul_apply, smul_eq_mul]
  linarith

omit [DecidableEq Ω] in
/-- If an entrywise positive real matrix has a strictly positive right
eigenpair, then any real right eigenvalue is bounded in absolute value by that
positive eigenvalue. -/
theorem abs_eigenvalue_le_of_entrywisePositive_positive_eigenpair [Nonempty Ω]
    {M : Matrix Ω Ω ℝ} (hM : MatrixEntrywisePositive M)
    {lam : ℝ} {v : Ω → ℝ} (hv : StrictPositiveRightEigenpair M lam v)
    {mu : ℝ} {w : Ω → ℝ} (hw_ne : w ≠ 0)
    (hw_eig : M.mulVec w = mu • w) :
    |mu| ≤ lam := by
  rcases exists_positive_vector_abs_bound_attained hv.1 hw_ne with
    ⟨C, hCpos, hbound, ⟨i, hatt⟩⟩
  have hCv_pos : 0 < C * v i := mul_pos hCpos (hv.1 i)
  have hsum_abs :
      |M.mulVec w i| ≤ ∑ j, M i j * |w j| := by
    calc
      |M.mulVec w i| = |∑ j, M i j * w j| := by
        simp [Matrix.mulVec, dotProduct]
      _ ≤ ∑ j, |M i j * w j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, M i j * |w j| := by
        apply Finset.sum_congr rfl
        intro j _hj
        rw [abs_mul, abs_of_pos (hM i j)]
  have hsum_bound :
      ∑ j, M i j * |w j| ≤ ∑ j, M i j * (C * v j) := by
    exact Finset.sum_le_sum fun j _hj =>
      mul_le_mul_of_nonneg_left (hbound j) (hM i j).le
  have hsum_eval :
      ∑ j, M i j * (C * v j) = lam * (C * v i) := by
    have hv_apply := congr_fun hv.2 i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hv_apply
    calc
      ∑ j, M i j * (C * v j) = ∑ j, C * (M i j * v j) := by
        apply Finset.sum_congr rfl
        intro j _hj
        ring
      _ = C * ∑ j, M i j * v j := by
        rw [Finset.mul_sum]
      _ = lam * (C * v i) := by
        rw [hv_apply]
        ring
  have hmain : |mu| * (C * v i) ≤ lam * (C * v i) := by
    calc
      |mu| * (C * v i) = |mu * w i| := by
        rw [← hatt, abs_mul]
      _ = |M.mulVec w i| := by
        have h := congr_fun hw_eig i
        simp only [Pi.smul_apply, smul_eq_mul] at h
        rw [h]
      _ ≤ ∑ j, M i j * |w j| := hsum_abs
      _ ≤ ∑ j, M i j * (C * v j) := hsum_bound
      _ = lam * (C * v i) := hsum_eval
  exact le_of_mul_le_mul_right hmain hCv_pos

omit [DecidableEq Ω] in
/-- For an entrywise positive matrix, any real eigenvalue different from the
positive eigenpair's eigenvalue is strictly smaller in absolute value. -/
theorem abs_eigenvalue_lt_of_entrywisePositive_positive_eigenpair [Nonempty Ω]
    {M : Matrix Ω Ω ℝ} (hM : MatrixEntrywisePositive M)
    {lam : ℝ} {v : Ω → ℝ} (hv : StrictPositiveRightEigenpair M lam v)
    {mu : ℝ} {w : Ω → ℝ} (hw_ne : w ≠ 0)
    (hw_eig : M.mulVec w = mu • w) (hmu_ne : mu ≠ lam) :
    |mu| < lam := by
  have hle : |mu| ≤ lam :=
    abs_eigenvalue_le_of_entrywisePositive_positive_eigenpair hM hv hw_ne hw_eig
  by_contra hnot
  have habs : |mu| = lam := le_antisymm hle (le_of_not_gt hnot)
  have hM2 : MatrixEntrywisePositive (M * M) :=
    matrixEntrywisePositive_mul hM hM
  have hv2 : StrictPositiveRightEigenpair (M * M) (lam * lam) v := by
    refine ⟨hv.1, ?_⟩
    rw [← Matrix.mulVec_mulVec, hv.2, Matrix.mulVec_smul, hv.2]
    ext i
    simp [Pi.smul_apply, smul_eq_mul, mul_assoc]
  have hsq : mu * mu = lam * lam := by
    have hsqp : |mu| ^ 2 = lam ^ 2 := by rw [habs]
    have hsqp' : mu ^ 2 = lam ^ 2 := by simpa [sq_abs] using hsqp
    nlinarith
  have hw2 : (M * M).mulVec w = (lam * lam) • w := by
    rw [← Matrix.mulVec_mulVec, hw_eig, Matrix.mulVec_smul, hw_eig]
    ext i
    simp only [Pi.smul_apply, smul_eq_mul]
    calc
      mu * (mu * w i) = (mu * mu) * w i := by ring
      _ = (lam * lam) * w i := by rw [hsq]
      _ = lam * lam * w i := by ring
  rcases eigenvector_smul_of_entrywisePositive_positive_eigenpair hM2 hv2 hw2 with
    ⟨c, hc⟩
  have hw_lam : M.mulVec w = lam • w := by
    rw [hc, Matrix.mulVec_smul, hv.2]
    ext i
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hsame : mu = lam := by
    have hvec : mu • w = lam • w := by
      rw [← hw_eig, hw_lam]
    obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
      by_contra h
      apply hw_ne
      ext i
      by_contra hwi
      exact h ⟨i, hwi⟩
    have hi_eq := congr_fun hvec i
    simp only [Pi.smul_apply, smul_eq_mul] at hi_eq
    exact mul_right_cancel₀ hi hi_eq
  exact hmu_ne hsame

end TransferMatrix

end IsingModel

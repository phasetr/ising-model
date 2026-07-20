import IsingModel.TransferMatrix.LayerPerron.EigenpairComparison
import IsingModel.TransferMatrix.LayerSpectral.HermitianBridge
import IsingModel.TransferMatrix.LayerSpectral.Positivity
import Mathlib.Data.Finset.Max
import Mathlib.Data.Matrix.Mul

/-!
# Positive/simple Perron bridge (2/5): positive spectral-data columns

Structural split (2/5) of `TransferMatrix.LayerPerron`.  This child holds the column theory
of explicit real orthogonal spectral data: a column is a right eigenvector for the
corresponding spectral-data eigenvalue, columns are nonzero and pairwise non-proportional,
and a strictly positive top column of an entrywise positive matrix has a positive
eigenvalue, dominates all spectral-data eigenvalues in absolute value, spans its
eigenspace, dominates strictly off the top, and admits some finite subdominant ratio
`theta < 1`.  See the `IsingModel.TransferMatrix.LayerPerron` facade module for the full
contents overview.
-/

namespace IsingModel

namespace TransferMatrix

open Matrix

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

namespace RealOrthogonalSpectralData

/-- A column of explicit real orthogonal spectral data is a right eigenvector
with the corresponding spectral-data eigenvalue. -/
theorem mulVec_changeOfBasis_column {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (i : Ω) :
    M.mulVec (fun x => E.changeOfBasis x i)
      = E.eigenvalue i • (fun x => E.changeOfBasis x i) := by
  have hcol :
      E.changeOfBasisᵀ.mulVec (fun x => E.changeOfBasis x i) = Pi.single i 1 := by
    ext j
    have h := congr_fun (congr_fun E.orthogonal_left j) i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.one_apply,
      Pi.single_apply] using h
  calc
    M.mulVec (fun x => E.changeOfBasis x i)
        = (E.changeOfBasis * Matrix.diagonal E.eigenvalue * E.changeOfBasisᵀ).mulVec
            (fun x => E.changeOfBasis x i) := by
          exact congrArg (fun A => A.mulVec (fun x => E.changeOfBasis x i))
            E.diagonalizes
    _ = (E.changeOfBasis * Matrix.diagonal E.eigenvalue).mulVec (Pi.single i 1) := by
          rw [← Matrix.mulVec_mulVec, hcol]
    _ = E.eigenvalue i • (fun x => E.changeOfBasis x i) := by
          rw [Matrix.mulVec_single_one]
          ext j
          change (E.changeOfBasis * Matrix.diagonal E.eigenvalue) j i
            = (E.eigenvalue i • fun x => E.changeOfBasis x i) j
          rw [Matrix.mul_apply]
          rw [Finset.sum_eq_single i]
          · simp [Pi.smul_apply, smul_eq_mul, mul_comm]
          · intro b _ hb
            simp [hb]
          · intro hi
            exact (hi (Finset.mem_univ i)).elim

/-- A column of explicit orthogonal spectral data is nonzero. -/
theorem changeOfBasis_column_ne_zero {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (i : Ω) :
    (fun x => E.changeOfBasis x i) ≠ 0 := by
  intro hzero
  have hcol :
      E.changeOfBasisᵀ.mulVec (fun x => E.changeOfBasis x i) = Pi.single i 1 := by
    ext j
    have h := congr_fun (congr_fun E.orthogonal_left j) i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.one_apply,
      Pi.single_apply] using h
  have hleft : (E.changeOfBasisᵀ.mulVec (fun x => E.changeOfBasis x i)) i = 0 := by
    rw [hzero]
    simp [Matrix.mulVec, dotProduct]
  have hright : (Pi.single i 1 : Ω → ℝ) i = 1 := by
    simp
  have h := congr_fun hcol i
  rw [hleft, hright] at h
  norm_num at h

/-- Distinct columns of explicit orthogonal spectral data are not scalar
multiples of each other. -/
theorem changeOfBasis_columns_not_smul {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) {i j : Ω} (hij : i ≠ j) (c : ℝ) :
    (fun x => E.changeOfBasis x i) ≠ c • (fun x => E.changeOfBasis x j) := by
  intro hsmul
  have hleft :
      (E.changeOfBasisᵀ.mulVec (fun x => E.changeOfBasis x i)) i = 1 := by
    have h := congr_fun (congr_fun E.orthogonal_left i) i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.one_apply,
      Pi.single_apply] using h
  have hright :
      (E.changeOfBasisᵀ.mulVec (fun x => E.changeOfBasis x j)) i = 0 := by
    have h := congr_fun (congr_fun E.orthogonal_left i) j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.one_apply,
      Pi.single_apply, hij] using h
  have hmul :
      E.changeOfBasisᵀ.mulVec (fun x => E.changeOfBasis x i)
        = c • (E.changeOfBasisᵀ.mulVec (fun x => E.changeOfBasis x j)) := by
    rw [hsmul, Matrix.mulVec_smul]
  have h := congr_fun hmul i
  simp [hleft, hright] at h

/-- A positive spectral-data column of an entrywise positive matrix has a
positive eigenvalue. -/
theorem eigenvalue_pos_of_positive_column [Nonempty Ω]
    {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M)
    (hM : MatrixEntrywisePositive M) (top : Ω)
    (hpos : VectorPositive (fun x => E.changeOfBasis x top)) :
    0 < E.eigenvalue top :=
  eigenvalue_pos_of_strictPositiveRightEigenpair hM
    ⟨hpos, E.mulVec_changeOfBasis_column top⟩

/-- A positive spectral-data column of an entrywise positive matrix bounds all
spectral-data eigenvalues in absolute value. -/
theorem eigenvalue_abs_le_of_positive_column [Nonempty Ω]
    {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M)
    (hM : MatrixEntrywisePositive M) (top i : Ω)
    (hpos : VectorPositive (fun x => E.changeOfBasis x top)) :
    |E.eigenvalue i| ≤ E.eigenvalue top :=
  abs_eigenvalue_le_of_entrywisePositive_positive_eigenpair hM
    ⟨hpos, E.mulVec_changeOfBasis_column top⟩
    (E.changeOfBasis_column_ne_zero i)
    (E.mulVec_changeOfBasis_column i)

/-- A positive spectral-data column of an entrywise positive matrix spans the
corresponding eigenspace. -/
theorem eigenspace_simple_of_positive_column [Nonempty Ω]
    {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M)
    (hM : MatrixEntrywisePositive M) (top : Ω)
    (hpos : VectorPositive (fun x => E.changeOfBasis x top))
    (w : Ω → ℝ)
    (hw_eig : M.mulVec w = E.eigenvalue top • w) :
    ∃ c : ℝ, w = c • (fun x => E.changeOfBasis x top) :=
  eigenvector_smul_of_entrywisePositive_positive_eigenpair hM
    ⟨hpos, E.mulVec_changeOfBasis_column top⟩ hw_eig

/-- A non-top spectral-data column has eigenvalue strictly smaller in absolute
value than a positive top column's eigenvalue. -/
theorem eigenvalue_abs_lt_of_positive_column [Nonempty Ω]
    {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M)
    (hM : MatrixEntrywisePositive M) (top i : Ω) (hi : i ≠ top)
    (hpos : VectorPositive (fun x => E.changeOfBasis x top)) :
    |E.eigenvalue i| < E.eigenvalue top := by
  have hne : E.eigenvalue i ≠ E.eigenvalue top := by
    intro heq
    have hi_eig :
        M.mulVec (fun x => E.changeOfBasis x i)
          = E.eigenvalue top • (fun x => E.changeOfBasis x i) := by
      simpa [heq] using E.mulVec_changeOfBasis_column i
    rcases E.eigenspace_simple_of_positive_column hM top hpos
        (fun x => E.changeOfBasis x i) hi_eig with
      ⟨c, hc⟩
    exact E.changeOfBasis_columns_not_smul hi c hc
  exact abs_eigenvalue_lt_of_entrywisePositive_positive_eigenpair hM
    ⟨hpos, E.mulVec_changeOfBasis_column top⟩
    (E.changeOfBasis_column_ne_zero i)
    (E.mulVec_changeOfBasis_column i) hne

/-- A positive spectral-data top column gives some strict finite subdominant
ratio for all non-top spectral-data eigenvalues.  This is only an existence
statement for the finite maximum; certificate constructors still require the
quantitative prefactor condition separately. -/
theorem exists_subdominant_abs_ratio_of_positive_column [Nonempty Ω]
    {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M)
    (hM : MatrixEntrywisePositive M) (top : Ω)
    (hpos : VectorPositive (fun x => E.changeOfBasis x top)) :
    ∃ theta : ℝ, 0 ≤ theta ∧ theta < 1 ∧
      ∀ i, i ≠ top → |E.eigenvalue i| ≤ theta * E.eigenvalue top := by
  let rest : Finset Ω := Finset.univ.erase top
  have htop_pos : 0 < E.eigenvalue top :=
    E.eigenvalue_pos_of_positive_column hM top hpos
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
      have hlt := E.eigenvalue_abs_lt_of_positive_column hM top i0 hi0_ne hpos
      exact (div_lt_one htop_pos).mpr hlt
    · intro i hi
      have himem : i ∈ rest := Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩
      exact (div_le_iff₀ htop_pos).mp (hmax i himem)

end RealOrthogonalSpectralData

end TransferMatrix

end IsingModel

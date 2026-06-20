import IsingModel.TransferMatrix.LayerQuadraticFormDiag
import IsingModel.TransferMatrix.LayerQuadraticFormOffDiag

/-!
# Gershgorin Rayleigh envelope for the transfer-matrix quadratic form

This file combines the diagonal bounds (`LayerQuadraticFormDiag`) and the
off-diagonal split (`LayerQuadraticFormOffDiag`) into a two-sided Gershgorin
Rayleigh envelope for the quadratic form of a symmetric matrix:
`(min diag − offMass)·‖v‖² ≤ ⟨v, M v⟩ ≤ (max diag + offMass)·‖v‖²` and the
absolute form `|⟨v, M v⟩| ≤ (max |diag| + offMass)·‖v‖²`, where
`offMass = max_i ∑_{j ≠ i} |M i j|`.

Combining `⟨v,Mv⟩ = ∑ M i i v i² + (⟨v,Mv⟩ − ∑ M i i v i²)` with the two bounds is
pure triangle inequality.  The envelope still bounds the top eigenvalue, so it is
not by itself a strict spectral gap; it is the Rayleigh form from which the
top-eigenvalue contribution is subtracted on the top-orthogonal subspace.  The
ratio hook is provided as an all-vector envelope (it is not yet the strict
top-orthogonal subtraction).

The results are finite, unconditional Rayleigh estimates.  They do not construct
a strict spectral gap, prove a thermodynamic limit, or prove final hyperplane
exponential decay.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

open Matrix
open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- **Absolute Gershgorin Rayleigh envelope.**  The quadratic form of a symmetric
matrix is bounded in absolute value by the maximal absolute diagonal entry plus
the maximal off-diagonal absolute row sum, times the squared norm. -/
theorem abs_matrixQuadraticForm_le_matrixMaxAbsDiag_add_matrixMaxOffDiagAbsRowSum_mul_vectorSqNorm
    [Nonempty Ω] {M : Matrix Ω Ω ℝ} (hM_symm : Mᵀ = M) (v : Ω → ℝ) :
    |matrixQuadraticForm M v| ≤
      (matrixMaxAbsDiag M + matrixMaxOffDiagAbsRowSum M) * vectorSqNorm v := by
  have hoff := abs_matrixQuadraticForm_sub_diag_le_matrixMaxOffDiagAbsRowSum_mul_vectorSqNorm hM_symm v
  have hdiag := abs_diagQuadraticForm_le_matrixMaxAbsDiag_mul_vectorSqNorm M v
  have heq : (∑ i, M i i * (v i) ^ 2)
      + (matrixQuadraticForm M v - ∑ i, M i i * (v i) ^ 2) = matrixQuadraticForm M v := by ring
  have key := abs_add_le (∑ i, M i i * (v i) ^ 2)
    (matrixQuadraticForm M v - ∑ i, M i i * (v i) ^ 2)
  rw [heq] at key
  calc |matrixQuadraticForm M v|
      ≤ |∑ i, M i i * (v i) ^ 2| + |matrixQuadraticForm M v - ∑ i, M i i * (v i) ^ 2| := key
    _ ≤ matrixMaxAbsDiag M * vectorSqNorm v + matrixMaxOffDiagAbsRowSum M * vectorSqNorm v :=
        add_le_add hdiag hoff
    _ = (matrixMaxAbsDiag M + matrixMaxOffDiagAbsRowSum M) * vectorSqNorm v := by ring

/-- **Upper Gershgorin Rayleigh envelope.**  The quadratic form is bounded above
by the maximal diagonal entry plus the off-diagonal mass, times the squared
norm. -/
theorem matrixQuadraticForm_le_matrixMaxDiag_add_matrixMaxOffDiagAbsRowSum_mul_vectorSqNorm
    [Nonempty Ω] {M : Matrix Ω Ω ℝ} (hM_symm : Mᵀ = M) (v : Ω → ℝ) :
    matrixQuadraticForm M v ≤
      (matrixMaxDiag M + matrixMaxOffDiagAbsRowSum M) * vectorSqNorm v := by
  have hoff := abs_matrixQuadraticForm_sub_diag_le_matrixMaxOffDiagAbsRowSum_mul_vectorSqNorm hM_symm v
  have hoff_up := (abs_le.mp hoff).2
  have hdiag_up := diagQuadraticForm_le_matrixMaxDiag_mul_vectorSqNorm M v
  rw [add_mul]
  linarith [hdiag_up, hoff_up]

/-- **Lower Gershgorin Rayleigh envelope.**  The quadratic form is bounded below
by the minimal diagonal entry minus the off-diagonal mass, times the squared
norm. -/
theorem matrixMinDiag_sub_matrixMaxOffDiagAbsRowSum_mul_vectorSqNorm_le_matrixQuadraticForm
    [Nonempty Ω] {M : Matrix Ω Ω ℝ} (hM_symm : Mᵀ = M) (v : Ω → ℝ) :
    (matrixMinDiag M - matrixMaxOffDiagAbsRowSum M) * vectorSqNorm v ≤
      matrixQuadraticForm M v := by
  have hoff := abs_matrixQuadraticForm_sub_diag_le_matrixMaxOffDiagAbsRowSum_mul_vectorSqNorm hM_symm v
  have hoff_lo := (abs_le.mp hoff).1
  have hdiag_lo := matrixMinDiag_mul_vectorSqNorm_le_diagQuadraticForm M v
  rw [sub_mul]
  linarith [hdiag_lo, hoff_lo]

/-- The explicit subdominant absolute ratio is bounded by `θ` whenever the
Gershgorin envelope `max |diag| + offMass` is at most `θ·λ_max`.  This feeds the
all-vector Gershgorin envelope into the quadratic-form-gap hook; it is the
Rayleigh-envelope bound, not yet the strict top-orthogonal subtraction. -/
theorem RealOrthogonalSpectralData.subdominantAbsRatio_maxEigenIndex_le_of_gershgorinAbsDiagOffDiag_le
    [Nonempty Ω] {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M)
    (hM_pos : MatrixEntrywisePositive M) (hM_symm : Mᵀ = M)
    {theta : ℝ} (htheta : 0 ≤ theta)
    (hgersh :
      matrixMaxAbsDiag M + matrixMaxOffDiagAbsRowSum M ≤
        theta * E.eigenvalue E.maxEigenIndex) :
    E.subdominantAbsRatio_maxEigenIndex hM_pos ≤ theta := by
  refine E.subdominantAbsRatio_maxEigenIndex_le_of_quadraticForm_gap hM_pos htheta ?_
  intro v _
  calc |matrixQuadraticForm M v|
      ≤ (matrixMaxAbsDiag M + matrixMaxOffDiagAbsRowSum M) * vectorSqNorm v :=
        abs_matrixQuadraticForm_le_matrixMaxAbsDiag_add_matrixMaxOffDiagAbsRowSum_mul_vectorSqNorm
          hM_symm v
    _ ≤ (theta * E.eigenvalue E.maxEigenIndex) * vectorSqNorm v :=
        mul_le_mul_of_nonneg_right hgersh (vectorSqNorm_nonneg v)

end TransferMatrix

end IsingModel

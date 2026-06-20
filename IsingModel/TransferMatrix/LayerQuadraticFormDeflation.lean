import IsingModel.TransferMatrix.LayerQuadraticFormGershgorin

/-!
# Top-column deflation and the strict-gap reduction

The all-vector Gershgorin envelope of `LayerQuadraticFormGershgorin` cannot
produce a strict spectral gap, since it also bounds the top eigenvalue.  A strict
gap requires a bound on the subspace orthogonal to the maximal spectral column.

This file removes that obstruction by **deflating** the top eigenpair: the matrix
`matrixTopDeflation E top = M − λ_top · w_top w_topᵀ` (with `w_top` the maximal
spectral column) is symmetric, agrees with `M` in quadratic form on the
top-orthogonal subspace `{v : spectralCoord v top = 0}`, and has the maximal
eigenvalue replaced by `0`.  Applying the Gershgorin envelope to the *deflated*
matrix therefore yields a genuine subdominant-ratio bound — the hypothesis is the
deflated matrix's Gershgorin quantity, not the (circular) second eigenvalue.

This breaks the circularity but does not by itself construct a strict gap: it
reduces it to controlling the deflated matrix's entries, which still requires
knowing the top eigenvector concretely (a quantitative Perron--Frobenius /
Dobrushin estimate, in a later file).  The results here are finite and
conditional.  They do not prove a thermodynamic limit or final hyperplane decay.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

namespace RealOrthogonalSpectralData

open Matrix
open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The top-eigenpair deflation `M − λ_top · w_top w_topᵀ`, with `w_top` the
maximal spectral column `x ↦ changeOfBasis x top`. -/
def matrixTopDeflation {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M)
    (top : Ω) : Matrix Ω Ω ℝ :=
  fun i j => M i j - E.eigenvalue top * (E.changeOfBasis i top * E.changeOfBasis j top)

/-- The top-eigenpair deflation of a symmetric matrix is symmetric. -/
theorem matrixTopDeflation_transpose_eq_self {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (top : Ω) (hM_symm : Mᵀ = M) :
    (E.matrixTopDeflation top)ᵀ = E.matrixTopDeflation top := by
  ext i j
  have hsymm : M j i = M i j := by
    have h := congr_fun (congr_fun hM_symm i) j
    rwa [Matrix.transpose_apply] at h
  simp only [Matrix.transpose_apply, matrixTopDeflation]
  rw [hsymm]; ring

/-- The quadratic form lost in deflation is exactly the top spectral
contribution `λ_top · (spectralCoord v top)²`. -/
theorem matrixQuadraticForm_sub_topDeflation {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (top : Ω) (v : Ω → ℝ) :
    matrixQuadraticForm M v - matrixQuadraticForm (E.matrixTopDeflation top) v
      = E.eigenvalue top * (E.spectralCoord v top) ^ 2 := by
  rw [matrixQuadraticForm, matrixQuadraticForm]
  simp only [matrixTopDeflation]
  rw [← Finset.sum_sub_distrib]
  have h1 : ∀ i, (∑ j, v i * M i j * v j)
      - (∑ j, v i * (M i j -
          E.eigenvalue top * (E.changeOfBasis i top * E.changeOfBasis j top)) * v j)
      = ∑ j, E.eigenvalue top *
          (E.changeOfBasis i top * v i) * (E.changeOfBasis j top * v j) := by
    intro i
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [h1]
  have hsc : E.spectralCoord v top = ∑ i, E.changeOfBasis i top * v i := rfl
  rw [hsc, sq, Fintype.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- On the subspace orthogonal to the maximal spectral column, the quadratic form
of `M` agrees with that of its top deflation. -/
theorem matrixQuadraticForm_eq_topDeflation_of_spectralCoord_eq_zero {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (top : Ω) {v : Ω → ℝ}
    (hv : E.spectralCoord v top = 0) :
    matrixQuadraticForm M v = matrixQuadraticForm (E.matrixTopDeflation top) v := by
  have h := E.matrixQuadraticForm_sub_topDeflation top v
  rw [hv] at h
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at h
  linarith [h]

/-- **Top-deflated Gershgorin strict-gap reduction.**  If the Gershgorin quantity
of the top-deflated matrix is at most `θ·λ_max`, then the explicit subdominant
absolute ratio is at most `θ`.  Unlike the all-vector envelope, the deflated
matrix has the maximal eigenvalue removed, so its Gershgorin bound can be strictly
below `λ_max`; the circularity is broken because the hypothesis is on the deflated
matrix's entries, not on the second eigenvalue. -/
theorem subdominantAbsRatio_maxEigenIndex_le_of_topDeflatedGershgorin_le [Nonempty Ω]
    {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M)
    (hM_pos : MatrixEntrywisePositive M) (hM_symm : Mᵀ = M)
    {theta : ℝ} (htheta : 0 ≤ theta)
    (hgersh :
      matrixMaxAbsDiag (E.matrixTopDeflation E.maxEigenIndex)
          + matrixMaxOffDiagAbsRowSum (E.matrixTopDeflation E.maxEigenIndex)
        ≤ theta * E.eigenvalue E.maxEigenIndex) :
    E.subdominantAbsRatio_maxEigenIndex hM_pos ≤ theta := by
  refine E.subdominantAbsRatio_maxEigenIndex_le_of_quadraticForm_gap hM_pos htheta ?_
  intro v hv
  rw [E.matrixQuadraticForm_eq_topDeflation_of_spectralCoord_eq_zero E.maxEigenIndex hv]
  calc |matrixQuadraticForm (E.matrixTopDeflation E.maxEigenIndex) v|
      ≤ (matrixMaxAbsDiag (E.matrixTopDeflation E.maxEigenIndex)
          + matrixMaxOffDiagAbsRowSum (E.matrixTopDeflation E.maxEigenIndex)) * vectorSqNorm v :=
        abs_matrixQuadraticForm_le_matrixMaxAbsDiag_add_matrixMaxOffDiagAbsRowSum_mul_vectorSqNorm
          (E.matrixTopDeflation_transpose_eq_self E.maxEigenIndex hM_symm) v
    _ ≤ (theta * E.eigenvalue E.maxEigenIndex) * vectorSqNorm v :=
        mul_le_mul_of_nonneg_right hgersh (vectorSqNorm_nonneg v)

end RealOrthogonalSpectralData

end TransferMatrix

end IsingModel

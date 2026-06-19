import IsingModel.TransferMatrix.LayerQuadraticFormGap

/-!
# Row-sum Rayleigh bound for the transfer-matrix quadratic form

This file provides an unconditional Rayleigh bound for the quadratic form of a
symmetric matrix in terms of its maximal absolute row sum: for symmetric `M`,
`|⟨v, M v⟩| ≤ (max_i ∑_j |M i j|) · ‖v‖²` for every vector `v` (a discrete
Schur-test / Gershgorin-type estimate proved directly by double-sum expansion and
the arithmetic--geometric inequality, without operator-norm machinery).

This is the first building block for constructing the quadratic-form gap that
`LayerQuadraticFormGap` reduces the transverse-volume-uniform decay to.  The
bound holds for all vectors (not only the top-orthogonal subspace), so by itself
it bounds the maximal eigenvalue too and does not yet produce a strict gap; a
later off-diagonal-mass splitting on the top-orthogonal subspace will.

The results are finite and unconditional Rayleigh estimates.  They do not
construct a strict spectral gap, prove a thermodynamic limit, or prove final
hyperplane exponential decay.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

open Matrix
open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

/-- The absolute row sum of a matrix at index `i`: `∑ j, |M i j|`. -/
def matrixAbsRowSum (M : Matrix Ω Ω ℝ) (i : Ω) : ℝ :=
  ∑ j, |M i j|

/-- The maximal absolute row sum of a matrix. -/
noncomputable def matrixMaxAbsRowSum [Nonempty Ω] (M : Matrix Ω Ω ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => matrixAbsRowSum M i

/-- Each absolute row sum is at most the maximal absolute row sum. -/
theorem matrixAbsRowSum_le_matrixMaxAbsRowSum [Nonempty Ω] (M : Matrix Ω Ω ℝ) (i : Ω) :
    matrixAbsRowSum M i ≤ matrixMaxAbsRowSum M :=
  Finset.le_sup' (fun i => matrixAbsRowSum M i) (Finset.mem_univ i)

/-- The squared norm is nonnegative. -/
theorem vectorSqNorm_nonneg (v : Ω → ℝ) : 0 ≤ vectorSqNorm v :=
  Finset.sum_nonneg fun i _ => sq_nonneg (v i)

/-- **Row-sum Rayleigh bound.**  For a symmetric matrix whose absolute row sums
are all at most `C`, the quadratic form is bounded by `C · ‖v‖²` in absolute
value. -/
theorem abs_matrixQuadraticForm_le_of_absRowSum_le_of_symmetric
    {M : Matrix Ω Ω ℝ} {C : ℝ} (hM_symm : Mᵀ = M)
    (hrow : ∀ i, matrixAbsRowSum M i ≤ C) (v : Ω → ℝ) :
    |matrixQuadraticForm M v| ≤ C * vectorSqNorm v := by
  have hsymm_entry : ∀ i j, M i j = M j i := by
    intro i j
    have h := congr_fun (congr_fun hM_symm j) i
    rwa [Matrix.transpose_apply] at h
  -- Step 1: triangle inequality on the double sum.
  have h1 : |matrixQuadraticForm M v| ≤ ∑ i, ∑ j, |M i j| * (|v i| * |v j|) := by
    rw [matrixQuadraticForm]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun i _ => ?_
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun j _ => ?_
    rw [abs_mul, abs_mul]
    exact le_of_eq (by ring)
  -- Step 2: arithmetic-geometric inequality on each term.
  have h2 : ∑ i, ∑ j, |M i j| * (|v i| * |v j|)
      ≤ ∑ i, ∑ j, |M i j| * (((v i) ^ 2 + (v j) ^ 2) / 2) := by
    refine Finset.sum_le_sum fun i _ => ?_
    refine Finset.sum_le_sum fun j _ => ?_
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have hamgm : 2 * |v i| * |v j| ≤ |v i| ^ 2 + |v j| ^ 2 := two_mul_le_add_sq _ _
    rw [sq_abs, sq_abs] at hamgm
    linarith
  -- Step 3: split the symmetric average into a single row-sum-weighted sum.
  have h3 : ∑ i, ∑ j, |M i j| * (((v i) ^ 2 + (v j) ^ 2) / 2)
      = ∑ i, matrixAbsRowSum M i * (v i) ^ 2 := by
    have hsplit : ∀ i, ∑ j, |M i j| * (((v i) ^ 2 + (v j) ^ 2) / 2)
        = (v i) ^ 2 / 2 * matrixAbsRowSum M i
          + ∑ j, |M i j| * (v j) ^ 2 / 2 := by
      intro i
      rw [matrixAbsRowSum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib]
    have hcol : ∑ i, ∑ j, |M i j| * (v j) ^ 2 / 2
        = ∑ j, (v j) ^ 2 / 2 * matrixAbsRowSum M j := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [matrixAbsRowSum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hsymm_entry j i]
      ring
    rw [hcol]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [matrixAbsRowSum]
    ring
  -- Step 4: bound each row sum by `C`.
  have h4 : ∑ i, matrixAbsRowSum M i * (v i) ^ 2 ≤ C * vectorSqNorm v := by
    rw [vectorSqNorm, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    exact mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg _)
  calc |matrixQuadraticForm M v|
      ≤ ∑ i, ∑ j, |M i j| * (|v i| * |v j|) := h1
    _ ≤ ∑ i, ∑ j, |M i j| * (((v i) ^ 2 + (v j) ^ 2) / 2) := h2
    _ = ∑ i, matrixAbsRowSum M i * (v i) ^ 2 := h3
    _ ≤ C * vectorSqNorm v := h4

/-- The maximal-absolute-row-sum form of the Rayleigh bound. -/
theorem abs_matrixQuadraticForm_le_matrixMaxAbsRowSum_mul_vectorSqNorm
    [Nonempty Ω] {M : Matrix Ω Ω ℝ} (hM_symm : Mᵀ = M) (v : Ω → ℝ) :
    |matrixQuadraticForm M v| ≤ matrixMaxAbsRowSum M * vectorSqNorm v :=
  abs_matrixQuadraticForm_le_of_absRowSum_le_of_symmetric hM_symm
    (fun i => matrixAbsRowSum_le_matrixMaxAbsRowSum M i) v

/-- The explicit subdominant absolute ratio is bounded by `θ` whenever the
maximal absolute row sum is at most `θ·λ_max`.  This feeds the row-sum Rayleigh
bound (valid on all vectors, hence on the top-orthogonal subspace) into the
quadratic-form-gap hook. -/
theorem RealOrthogonalSpectralData.subdominantAbsRatio_maxEigenIndex_le_of_matrixMaxAbsRowSum_le
    [DecidableEq Ω] [Nonempty Ω] {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M)
    (hM_pos : MatrixEntrywisePositive M) (hM_symm : Mᵀ = M)
    {theta : ℝ} (htheta : 0 ≤ theta)
    (hrow : matrixMaxAbsRowSum M ≤ theta * E.eigenvalue E.maxEigenIndex) :
    E.subdominantAbsRatio_maxEigenIndex hM_pos ≤ theta := by
  refine E.subdominantAbsRatio_maxEigenIndex_le_of_quadraticForm_gap hM_pos htheta ?_
  intro v _
  calc |matrixQuadraticForm M v|
      ≤ matrixMaxAbsRowSum M * vectorSqNorm v :=
        abs_matrixQuadraticForm_le_matrixMaxAbsRowSum_mul_vectorSqNorm hM_symm v
    _ ≤ (theta * E.eigenvalue E.maxEigenIndex) * vectorSqNorm v :=
        mul_le_mul_of_nonneg_right hrow (vectorSqNorm_nonneg v)

end TransferMatrix

end IsingModel

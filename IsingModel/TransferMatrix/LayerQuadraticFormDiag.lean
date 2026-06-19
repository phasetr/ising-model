import IsingModel.TransferMatrix.LayerQuadraticFormRowSum

/-!
# Diagonal bounds for the transfer-matrix quadratic form

This file is the diagonal companion to the off-diagonal split of
`LayerQuadraticFormOffDiag`.  The diagonal contribution `∑ i, M i i · v i²` to the
quadratic form is two-sidedly controlled by the extremal diagonal entries:
`min_i M i i · ‖v‖² ≤ ∑ i M i i v i² ≤ max_i M i i · ‖v‖²`, and in absolute value
by the maximal absolute diagonal entry.  Combined with the off-diagonal mass
bound, these are the building blocks for subtracting the diagonal and top
contributions on the top-orthogonal subspace toward a strict spectral gap.

The results are finite, unconditional, and require neither symmetry nor spectral
data.  They do not construct a strict spectral gap, prove a thermodynamic limit,
or prove final hyperplane exponential decay.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

/-- The maximal diagonal entry of a matrix. -/
noncomputable def matrixMaxDiag [Nonempty Ω] (M : Matrix Ω Ω ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => M i i

/-- The minimal diagonal entry of a matrix. -/
noncomputable def matrixMinDiag [Nonempty Ω] (M : Matrix Ω Ω ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun i => M i i

/-- The maximal absolute diagonal entry of a matrix. -/
noncomputable def matrixMaxAbsDiag [Nonempty Ω] (M : Matrix Ω Ω ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => |M i i|

/-- Each diagonal entry is at most the maximal diagonal entry. -/
theorem matrixDiag_le_matrixMaxDiag [Nonempty Ω] (M : Matrix Ω Ω ℝ) (i : Ω) :
    M i i ≤ matrixMaxDiag M :=
  Finset.le_sup' (fun i => M i i) (Finset.mem_univ i)

/-- The minimal diagonal entry is at most each diagonal entry. -/
theorem matrixMinDiag_le_matrixDiag [Nonempty Ω] (M : Matrix Ω Ω ℝ) (i : Ω) :
    matrixMinDiag M ≤ M i i :=
  Finset.inf'_le (fun i => M i i) (Finset.mem_univ i)

/-- Each absolute diagonal entry is at most the maximal absolute diagonal entry. -/
theorem matrixAbsDiag_le_matrixMaxAbsDiag [Nonempty Ω] (M : Matrix Ω Ω ℝ) (i : Ω) :
    |M i i| ≤ matrixMaxAbsDiag M :=
  Finset.le_sup' (fun i => |M i i|) (Finset.mem_univ i)

/-- Upper bound on the diagonal quadratic-form contribution by the maximal
diagonal entry. -/
theorem diagQuadraticForm_le_matrixMaxDiag_mul_vectorSqNorm [Nonempty Ω]
    (M : Matrix Ω Ω ℝ) (v : Ω → ℝ) :
    ∑ i, M i i * (v i) ^ 2 ≤ matrixMaxDiag M * vectorSqNorm v := by
  rw [vectorSqNorm, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  exact mul_le_mul_of_nonneg_right (matrixDiag_le_matrixMaxDiag M i) (sq_nonneg _)

/-- Lower bound on the diagonal quadratic-form contribution by the minimal
diagonal entry. -/
theorem matrixMinDiag_mul_vectorSqNorm_le_diagQuadraticForm [Nonempty Ω]
    (M : Matrix Ω Ω ℝ) (v : Ω → ℝ) :
    matrixMinDiag M * vectorSqNorm v ≤ ∑ i, M i i * (v i) ^ 2 := by
  rw [vectorSqNorm, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  exact mul_le_mul_of_nonneg_right (matrixMinDiag_le_matrixDiag M i) (sq_nonneg _)

/-- Absolute bound on the diagonal quadratic-form contribution by the maximal
absolute diagonal entry. -/
theorem abs_diagQuadraticForm_le_matrixMaxAbsDiag_mul_vectorSqNorm [Nonempty Ω]
    (M : Matrix Ω Ω ℝ) (v : Ω → ℝ) :
    |∑ i, M i i * (v i) ^ 2| ≤ matrixMaxAbsDiag M * vectorSqNorm v := by
  calc |∑ i, M i i * (v i) ^ 2|
      ≤ ∑ i, |M i i * (v i) ^ 2| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |M i i| * (v i) ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [abs_mul, abs_of_nonneg (sq_nonneg (v i))]
    _ ≤ ∑ i, matrixMaxAbsDiag M * (v i) ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact mul_le_mul_of_nonneg_right (matrixAbsDiag_le_matrixMaxAbsDiag M i) (sq_nonneg _)
    _ = matrixMaxAbsDiag M * vectorSqNorm v := by rw [vectorSqNorm, Finset.mul_sum]

end TransferMatrix

end IsingModel

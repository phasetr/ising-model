import IsingModel.TransferMatrix.LayerDobrushinContraction

/-!
# Doeblin minorization and a strict Dobrushin bound

This file bounds the Dobrushin coefficient of a row-stochastic matrix below `1` by
the **Doeblin mass** `∑_j min_i P i j`:
`matrixDobrushinCoefficient P ≤ 1 − ∑_j min_i P i j`.
For an entrywise positive stochastic matrix the Doeblin mass is strictly
positive, so the Dobrushin coefficient is strictly below `1` — in particular for
the Doob transform of an entrywise positive matrix.

Combined with the eigenvalue bound of `LayerDobrushinContraction`, this gives a
strict second-eigenvalue gap for the stochastic Doob matrix.  The bound is not yet
uniform in the transverse box size: a uniform high-temperature lower bound on the
Doob entries (the quantitative Perron-vector estimate) is a later file.

The results are finite, unconditional estimates.  They do not give a
transverse-volume-uniform gap, prove a thermodynamic limit, or prove final
hyperplane exponential decay.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The column minimum `min_i P i j`. -/
noncomputable def matrixColMin [Nonempty Ω] (P : Matrix Ω Ω ℝ) (j : Ω) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun i => P i j

/-- The Doeblin mass `∑_j min_i P i j`. -/
noncomputable def matrixDoeblinMass [Nonempty Ω] (P : Matrix Ω Ω ℝ) : ℝ :=
  ∑ j, matrixColMin P j

/-- The column minimum is at most each entry of the column. -/
theorem matrixColMin_le [Nonempty Ω] (P : Matrix Ω Ω ℝ) (i j : Ω) :
    matrixColMin P j ≤ P i j :=
  Finset.inf'_le (fun i => P i j) (Finset.mem_univ i)

/-- `|a − b| = a + b − 2·min a b` for real `a, b`. -/
theorem abs_sub_eq_add_sub_two_mul_min (a b : ℝ) :
    |a - b| = a + b - 2 * min a b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
  · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring

/-- The row total-variation distance equals `1 − ∑_j min(P i j, P i' j)` for a
row-stochastic matrix. -/
theorem matrixDobrushinRowDistance_eq_one_sub_sum_min [Nonempty Ω]
    {P : Matrix Ω Ω ℝ} (hrow : ∀ i, ∑ j, P i j = 1) (i i' : Ω) :
    matrixDobrushinRowDistance P i i' = 1 - ∑ j, min (P i j) (P i' j) := by
  rw [matrixDobrushinRowDistance]
  have hexp : ∀ j, |P i j - P i' j|
      = P i j + P i' j - 2 * min (P i j) (P i' j) := fun j =>
    abs_sub_eq_add_sub_two_mul_min _ _
  simp_rw [hexp]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hrow i, hrow i', ← Finset.mul_sum]
  ring

/-- The Doeblin mass is at most one for a row-stochastic matrix. -/
theorem matrixDoeblinMass_le_one [Nonempty Ω] {P : Matrix Ω Ω ℝ}
    (hP : MatrixRowStochastic P) :
    matrixDoeblinMass P ≤ 1 := by
  rw [matrixDoeblinMass, ← hP.2 (Classical.arbitrary Ω)]
  exact Finset.sum_le_sum fun j _ => matrixColMin_le P (Classical.arbitrary Ω) j

/-- The row total-variation distance is at most `1 − Doeblin mass`. -/
theorem matrixDobrushinRowDistance_le_one_sub_doeblinMass [Nonempty Ω]
    {P : Matrix Ω Ω ℝ} (hP : MatrixRowStochastic P) (i i' : Ω) :
    matrixDobrushinRowDistance P i i' ≤ 1 - matrixDoeblinMass P := by
  rw [matrixDobrushinRowDistance_eq_one_sub_sum_min hP.2 i i', matrixDoeblinMass]
  have hle : ∑ j, matrixColMin P j ≤ ∑ j, min (P i j) (P i' j) :=
    Finset.sum_le_sum fun j _ => le_min (matrixColMin_le P i j) (matrixColMin_le P i' j)
  linarith

/-- **Doeblin minorization.**  The Dobrushin coefficient is at most `1 − Doeblin
mass`. -/
theorem matrixDobrushinCoefficient_le_one_sub_doeblinMass [Nonempty Ω]
    {P : Matrix Ω Ω ℝ} (hP : MatrixRowStochastic P) :
    matrixDobrushinCoefficient P ≤ 1 - matrixDoeblinMass P := by
  rw [matrixDobrushinCoefficient]
  refine Finset.sup'_le _ _ fun i _ => Finset.sup'_le _ _ fun i' _ => ?_
  exact matrixDobrushinRowDistance_le_one_sub_doeblinMass hP i i'

/-- The column minimum of an entrywise positive matrix is positive. -/
theorem matrixColMin_pos_of_entrywisePositive [Nonempty Ω] {P : Matrix Ω Ω ℝ}
    (hP : MatrixEntrywisePositive P) (j : Ω) :
    0 < matrixColMin P j := by
  obtain ⟨i0, _, hi0⟩ :=
    Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun i => P i j)
  rw [matrixColMin, hi0]
  exact hP i0 j

/-- The Doeblin mass of an entrywise positive matrix is positive. -/
theorem matrixDoeblinMass_pos_of_entrywisePositive [Nonempty Ω] {P : Matrix Ω Ω ℝ}
    (hP : MatrixEntrywisePositive P) :
    0 < matrixDoeblinMass P :=
  Finset.sum_pos (fun j _ => matrixColMin_pos_of_entrywisePositive hP j)
    Finset.univ_nonempty

/-- **Strict Dobrushin bound.**  An entrywise positive row-stochastic matrix has
Dobrushin coefficient strictly below one. -/
theorem matrixDobrushinCoefficient_lt_one_of_entrywisePositive_rowStochastic [Nonempty Ω]
    {P : Matrix Ω Ω ℝ} (hpos : MatrixEntrywisePositive P) (hP : MatrixRowStochastic P) :
    matrixDobrushinCoefficient P < 1 := by
  have h1 := matrixDobrushinCoefficient_le_one_sub_doeblinMass hP
  have h2 := matrixDoeblinMass_pos_of_entrywisePositive hpos
  linarith

/-- The Doob transform of an entrywise positive matrix along a positive Perron
eigenvector has Dobrushin coefficient strictly below one. -/
theorem matrixDobrushinCoefficient_matrixDoobTransform_lt_one [Nonempty Ω]
    {M : Matrix Ω Ω ℝ} (hM : MatrixEntrywisePositive M) {lam : ℝ} (hlam : 0 < lam)
    {w : Ω → ℝ} (hw : VectorPositive w) (hw_eig : M.mulVec w = lam • w) :
    matrixDobrushinCoefficient (matrixDoobTransform M lam w) < 1 :=
  matrixDobrushinCoefficient_lt_one_of_entrywisePositive_rowStochastic
    (fun i j => matrixDoobTransform_pos hM hlam hw i j)
    (matrixDoobTransform_rowStochastic hM hlam hw hw_eig)

end TransferMatrix

end IsingModel

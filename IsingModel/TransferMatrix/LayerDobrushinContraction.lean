import IsingModel.TransferMatrix.LayerDoobTransform

/-!
# Dobrushin oscillation contraction for row-stochastic matrices

This file proves the central Dobrushin contraction estimate: a row-stochastic
matrix `P` contracts the oscillation `osc(v) = max_i v_i − min_i v_i` of any
vector by its Dobrushin coefficient
`δ(P) = ½·max_{i,i'} ∑_j |P i j − P i' j|`:
`osc(P · v) ≤ δ(P) · osc(v)`.

Together with the Doob normalization of `LayerDoobTransform`, this is the route by
which the spectral gap of the balanced transfer matrix is controlled: the second
eigenvalue of the stochastic Doob matrix is bounded by `δ`, so a uniform bound
`δ < 1` yields a uniform spectral gap.  The quantitative bound `δ < 1` from the
layer entries is not proved here.

The results are finite, unconditional estimates for an abstract row-stochastic
matrix.  They do not bound `δ` quantitatively, prove a strict spectral gap, a
thermodynamic limit, or final hyperplane exponential decay.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

open Matrix
open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- A real matrix is row-stochastic: nonnegative entries and rows summing to one. -/
def MatrixRowStochastic (P : Matrix Ω Ω ℝ) : Prop :=
  (∀ i j, 0 ≤ P i j) ∧ ∀ i, ∑ j, P i j = 1

/-- The oscillation `max_i v_i − min_i v_i` of a finite real vector. -/
noncomputable def vectorOscillation [Nonempty Ω] (v : Ω → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty v -
    Finset.univ.inf' Finset.univ_nonempty v

/-- Half the total-variation distance between rows `i` and `i'` of `P`. -/
noncomputable def matrixDobrushinRowDistance (P : Matrix Ω Ω ℝ) (i i' : Ω) : ℝ :=
  (1 / 2 : ℝ) * ∑ j, |P i j - P i' j|

/-- The Dobrushin coefficient `½·max_{i,i'} ∑_j |P i j − P i' j|`. -/
noncomputable def matrixDobrushinCoefficient [Nonempty Ω] (P : Matrix Ω Ω ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i =>
    Finset.univ.sup' Finset.univ_nonempty fun i' =>
      matrixDobrushinRowDistance P i i'

/-! ## Oscillation basics -/

/-- The oscillation is nonnegative. -/
theorem vectorOscillation_nonneg [Nonempty Ω] (v : Ω → ℝ) :
    0 ≤ vectorOscillation v := by
  rw [vectorOscillation, sub_nonneg]
  exact (Finset.inf'_le v (Finset.mem_univ (Classical.arbitrary Ω))).trans
    (Finset.le_sup' v (Finset.mem_univ (Classical.arbitrary Ω)))

/-- The oscillation of a constant vector is zero. -/
@[simp] theorem vectorOscillation_const [Nonempty Ω] (c : ℝ) :
    vectorOscillation (fun _ : Ω => c) = 0 := by
  rw [vectorOscillation, Finset.sup'_const, Finset.inf'_const, sub_self]

/-- Pairwise differences bound the oscillation. -/
theorem vectorOscillation_le_of_forall_sub_le [Nonempty Ω] {v : Ω → ℝ} {C : ℝ}
    (h : ∀ i i', v i - v i' ≤ C) : vectorOscillation v ≤ C := by
  rw [vectorOscillation, sub_le_iff_le_add]
  refine Finset.sup'_le _ _ fun i _ => ?_
  rw [add_comm, ← sub_le_iff_le_add]
  refine Finset.le_inf' _ _ fun i' _ => ?_
  linarith [h i i']

/-- Each coordinate stays within half the oscillation of the midpoint. -/
theorem abs_sub_midpoint_le_half_oscillation [Nonempty Ω] (v : Ω → ℝ) (j : Ω) :
    |v j - (Finset.univ.sup' Finset.univ_nonempty v
        + Finset.univ.inf' Finset.univ_nonempty v) / 2|
      ≤ vectorOscillation v / 2 := by
  have hsup := Finset.le_sup' v (Finset.mem_univ j)
  have hinf := Finset.inf'_le v (Finset.mem_univ j)
  rw [vectorOscillation, abs_le]
  constructor <;> linarith

/-! ## Dobrushin coefficient basics -/

/-- The row distance is bounded by the Dobrushin coefficient. -/
theorem matrixDobrushinRowDistance_le_coefficient [Nonempty Ω] (P : Matrix Ω Ω ℝ)
    (i i' : Ω) :
    matrixDobrushinRowDistance P i i' ≤ matrixDobrushinCoefficient P := by
  refine le_trans ?_ (Finset.le_sup'
    (fun i => Finset.univ.sup' Finset.univ_nonempty fun i' =>
      matrixDobrushinRowDistance P i i') (Finset.mem_univ i))
  exact Finset.le_sup' (fun i' => matrixDobrushinRowDistance P i i') (Finset.mem_univ i')

/-- The row total-variation sum is at most twice the Dobrushin coefficient. -/
theorem sum_abs_row_sub_le_two_dobrushin [Nonempty Ω] (P : Matrix Ω Ω ℝ) (i i' : Ω) :
    ∑ j, |P i j - P i' j| ≤ 2 * matrixDobrushinCoefficient P := by
  have h := matrixDobrushinRowDistance_le_coefficient P i i'
  rw [matrixDobrushinRowDistance] at h
  linarith

/-- The Dobrushin coefficient is nonnegative. -/
theorem matrixDobrushinCoefficient_nonneg [Nonempty Ω] (P : Matrix Ω Ω ℝ) :
    0 ≤ matrixDobrushinCoefficient P := by
  have h := matrixDobrushinRowDistance_le_coefficient P
    (Classical.arbitrary Ω) (Classical.arbitrary Ω)
  rw [matrixDobrushinRowDistance] at h
  have hsum : (0 : ℝ) ≤ ∑ j, |P (Classical.arbitrary Ω) j - P (Classical.arbitrary Ω) j| :=
    Finset.sum_nonneg fun j _ => abs_nonneg _
  nlinarith [hsum, h]

/-! ## The oscillation contraction -/

/-- **Dobrushin oscillation contraction.**  A row-stochastic matrix contracts the
oscillation of any vector by its Dobrushin coefficient. -/
theorem vectorOscillation_mulVec_le_dobrushin [Nonempty Ω] {P : Matrix Ω Ω ℝ}
    (hrow : ∀ i, ∑ j, P i j = 1) (v : Ω → ℝ) :
    vectorOscillation (P.mulVec v) ≤
      matrixDobrushinCoefficient P * vectorOscillation v := by
  set c : ℝ := (Finset.univ.sup' Finset.univ_nonempty v
    + Finset.univ.inf' Finset.univ_nonempty v) / 2 with hc
  refine vectorOscillation_le_of_forall_sub_le fun i i' => ?_
  have hzero : ∑ j, (P i j - P i' j) = 0 := by
    rw [Finset.sum_sub_distrib, hrow i, hrow i', sub_self]
  have hi : (P.mulVec v) i = ∑ j, P i j * v j := rfl
  have hi' : (P.mulVec v) i' = ∑ j, P i' j * v j := rfl
  have hkey : (P.mulVec v) i - (P.mulVec v) i'
      = ∑ j, (P i j - P i' j) * (v j - c) := by
    rw [hi, hi', ← Finset.sum_sub_distrib]
    have hexpand : ∀ j, P i j * v j - P i' j * v j
        = (P i j - P i' j) * (v j - c) + (P i j - P i' j) * c := by
      intro j; ring
    simp_rw [hexpand]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hzero, zero_mul, add_zero]
  rw [hkey]
  calc ∑ j, (P i j - P i' j) * (v j - c)
      ≤ |∑ j, (P i j - P i' j) * (v j - c)| := le_abs_self _
    _ ≤ ∑ j, |(P i j - P i' j) * (v j - c)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |P i j - P i' j| * (vectorOscillation v / 2) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (abs_sub_midpoint_le_half_oscillation v j) (abs_nonneg _)
    _ = (∑ j, |P i j - P i' j|) * (vectorOscillation v / 2) := by rw [Finset.sum_mul]
    _ ≤ (2 * matrixDobrushinCoefficient P) * (vectorOscillation v / 2) :=
        mul_le_mul_of_nonneg_right (sum_abs_row_sub_le_two_dobrushin P i i')
          (by linarith [vectorOscillation_nonneg v])
    _ = matrixDobrushinCoefficient P * vectorOscillation v := by ring

/-! ## The Doob transform is row-stochastic -/

/-- The Doob transform of an entrywise positive matrix along a positive Perron
eigenvector is row-stochastic. -/
theorem matrixDoobTransform_rowStochastic [Nonempty Ω] {M : Matrix Ω Ω ℝ}
    (hM : MatrixEntrywisePositive M) {lam : ℝ} (hlam : 0 < lam) {w : Ω → ℝ}
    (hw : VectorPositive w) (hw_eig : M.mulVec w = lam • w) :
    MatrixRowStochastic (matrixDoobTransform M lam w) := by
  refine ⟨fun i j => (matrixDoobTransform_pos hM hlam hw i j).le, fun i => ?_⟩
  exact matrixDoobTransform_row_sum hw_eig hlam.ne' (fun i => (hw i).ne') i

end TransferMatrix

end IsingModel

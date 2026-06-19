import IsingModel.TransferMatrix.LayerQuadraticFormRowSum

/-!
# Off-diagonal split of the transfer-matrix quadratic form

This file refines the row-sum Rayleigh bound of `LayerQuadraticFormRowSum` by
separating the diagonal contribution: for a symmetric matrix, the quadratic form
differs from its diagonal part `∑ i, M i i · v i²` by an amount controlled by the
maximal **off-diagonal** absolute row sum,
`|⟨v, M v⟩ − ∑ i M i i v i²| ≤ (max_i ∑_{j ≠ i} |M i j|) · ‖v‖²`.

The proof reuses the row-sum bound applied to the off-diagonal part of `M` (the
matrix with the diagonal zeroed), avoiding a re-derivation with `j ≠ i`
bookkeeping.  This is the structural step before the strict spectral gap: on the
subspace orthogonal to the (entrywise positive) top eigenvector, the diagonal and
top contributions are subtracted, leaving the off-diagonal mass — handled in a
later file.

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

/-- The off-diagonal part of a matrix: the diagonal entries are set to zero. -/
def matrixOffDiagPart (M : Matrix Ω Ω ℝ) : Matrix Ω Ω ℝ :=
  fun i j => if i = j then 0 else M i j

/-- The off-diagonal absolute row sum `∑ j ≠ i, |M i j|`. -/
def matrixOffDiagAbsRowSum (M : Matrix Ω Ω ℝ) (i : Ω) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, |M i j|

/-- The maximal off-diagonal absolute row sum. -/
noncomputable def matrixMaxOffDiagAbsRowSum [Nonempty Ω] (M : Matrix Ω Ω ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => matrixOffDiagAbsRowSum M i

/-- Each off-diagonal absolute row sum is at most the maximal one. -/
theorem matrixOffDiagAbsRowSum_le_matrixMaxOffDiagAbsRowSum [Nonempty Ω]
    (M : Matrix Ω Ω ℝ) (i : Ω) :
    matrixOffDiagAbsRowSum M i ≤ matrixMaxOffDiagAbsRowSum M :=
  Finset.le_sup' (fun i => matrixOffDiagAbsRowSum M i) (Finset.mem_univ i)

/-- The off-diagonal part of a symmetric matrix is symmetric. -/
theorem matrixOffDiagPart_transpose_eq_self_of_transpose_eq_self
    {M : Matrix Ω Ω ℝ} (hM_symm : Mᵀ = M) :
    (matrixOffDiagPart M)ᵀ = matrixOffDiagPart M := by
  ext i j
  have hsymm_entry : M j i = M i j := by
    have h := congr_fun (congr_fun hM_symm i) j
    rwa [Matrix.transpose_apply] at h
  simp only [Matrix.transpose_apply, matrixOffDiagPart]
  by_cases h : j = i
  · subst h; simp
  · rw [if_neg h, if_neg (fun he => h he.symm), hsymm_entry]

/-- The absolute row sum of the off-diagonal part equals the off-diagonal
absolute row sum of the original matrix. -/
theorem matrixAbsRowSum_matrixOffDiagPart (M : Matrix Ω Ω ℝ) (i : Ω) :
    matrixAbsRowSum (matrixOffDiagPart M) i = matrixOffDiagAbsRowSum M i := by
  rw [matrixAbsRowSum, matrixOffDiagAbsRowSum]
  rw [← Finset.add_sum_erase Finset.univ (fun j => |matrixOffDiagPart M i j|)
    (Finset.mem_univ i)]
  have hdiag : |matrixOffDiagPart M i i| = 0 := by
    simp [matrixOffDiagPart]
  rw [hdiag, zero_add]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [matrixOffDiagPart, if_neg (fun he => (Finset.ne_of_mem_erase hj) he.symm)]

/-- The quadratic form of the off-diagonal part is the quadratic form minus the
diagonal contribution `∑ i, M i i · v i²`. -/
theorem matrixQuadraticForm_offDiagPart_eq_sub_diag (M : Matrix Ω Ω ℝ) (v : Ω → ℝ) :
    matrixQuadraticForm (matrixOffDiagPart M) v =
      matrixQuadraticForm M v - ∑ i, M i i * (v i) ^ 2 := by
  rw [matrixQuadraticForm, matrixQuadraticForm, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.add_sum_erase Finset.univ (fun j => v i * M i j * v j) (Finset.mem_univ i)]
  have hoff : ∑ j, v i * matrixOffDiagPart M i j * v j
      = ∑ j ∈ Finset.univ.erase i, v i * M i j * v j := by
    rw [← Finset.add_sum_erase Finset.univ
      (fun j => v i * matrixOffDiagPart M i j * v j) (Finset.mem_univ i)]
    have hdiag : v i * matrixOffDiagPart M i i * v i = 0 := by
      simp [matrixOffDiagPart]
    rw [hdiag, zero_add]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [matrixOffDiagPart, if_neg (fun he => (Finset.ne_of_mem_erase hj) he.symm)]
  rw [hoff]
  ring

/-- **Off-diagonal split Rayleigh bound.**  For a symmetric matrix whose
off-diagonal absolute row sums are all at most `C`, the quadratic form differs
from its diagonal contribution by at most `C · ‖v‖²` in absolute value. -/
theorem abs_matrixQuadraticForm_sub_diag_le_of_offDiagAbsRowSum_le_of_symmetric
    {M : Matrix Ω Ω ℝ} {C : ℝ} (hM_symm : Mᵀ = M)
    (hrow : ∀ i, matrixOffDiagAbsRowSum M i ≤ C) (v : Ω → ℝ) :
    |matrixQuadraticForm M v - ∑ i, M i i * (v i) ^ 2| ≤ C * vectorSqNorm v := by
  rw [← matrixQuadraticForm_offDiagPart_eq_sub_diag M v]
  refine abs_matrixQuadraticForm_le_of_absRowSum_le_of_symmetric
    (matrixOffDiagPart_transpose_eq_self_of_transpose_eq_self hM_symm) (fun i => ?_) v
  rw [matrixAbsRowSum_matrixOffDiagPart]
  exact hrow i

/-- The maximal-off-diagonal-row-sum form of the off-diagonal split bound. -/
theorem abs_matrixQuadraticForm_sub_diag_le_matrixMaxOffDiagAbsRowSum_mul_vectorSqNorm
    [Nonempty Ω] {M : Matrix Ω Ω ℝ} (hM_symm : Mᵀ = M) (v : Ω → ℝ) :
    |matrixQuadraticForm M v - ∑ i, M i i * (v i) ^ 2| ≤
      matrixMaxOffDiagAbsRowSum M * vectorSqNorm v :=
  abs_matrixQuadraticForm_sub_diag_le_of_offDiagAbsRowSum_le_of_symmetric hM_symm
    (fun i => matrixOffDiagAbsRowSum_le_matrixMaxOffDiagAbsRowSum M i) v

end TransferMatrix

end IsingModel

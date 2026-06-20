import IsingModel.TransferMatrix.LayerQuadraticFormDeflationEntries

/-!
# Doob (Perron) stochastic normalization of the transfer matrix

Given a positive matrix `M` with a strictly positive right eigenvector `w` of
eigenvalue `λ > 0` (the Perron eigenpair), the **Doob transform**
`P i j = M i j · w j / (λ · w i)` is an entrywise positive, row-stochastic matrix
similar to `M / λ`.  It conjugates `M / λ` by the diagonal `w`, sending the
eigenvector `v` of `M` (eigenvalue `μ`) to the eigenvector `v / w` of `P`
(eigenvalue `μ / λ`).

This is the structural reduction underlying a future quantitative
Perron--Frobenius / Dobrushin estimate: the spectral gap of `M` becomes the
spectral gap of the stochastic matrix `P`, whose contraction is controlled by a
Dobrushin/Hilbert-projective-metric coefficient.  The quantitative contraction
bound itself is not proved here.

The results are finite algebraic identities for an abstract positive Perron
eigenpair.  They do not prove a quantitative contraction, a strict spectral gap,
a thermodynamic limit, or final hyperplane exponential decay.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

open Matrix
open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The Doob (Perron) transform `P i j = M i j · w j / (λ · w i)` of a matrix `M`
relative to a positive eigenvector `w` of eigenvalue `λ`. -/
noncomputable def matrixDoobTransform (M : Matrix Ω Ω ℝ) (lam : ℝ) (w : Ω → ℝ) :
    Matrix Ω Ω ℝ :=
  fun i j => M i j * w j / (lam * w i)

/-- Entry of the Doob transform. -/
theorem matrixDoobTransform_apply (M : Matrix Ω Ω ℝ) (lam : ℝ) (w : Ω → ℝ) (i j : Ω) :
    matrixDoobTransform M lam w i j = M i j * w j / (lam * w i) :=
  rfl

/-- The Doob transform of an entrywise positive matrix along a positive
eigenvector is entrywise positive. -/
theorem matrixDoobTransform_pos {M : Matrix Ω Ω ℝ} (hM : MatrixEntrywisePositive M)
    {lam : ℝ} (hlam : 0 < lam) {w : Ω → ℝ} (hw : VectorPositive w) (i j : Ω) :
    0 < matrixDoobTransform M lam w i j := by
  rw [matrixDoobTransform]
  exact div_pos (mul_pos (hM i j) (hw j)) (mul_pos hlam (hw i))

/-- **The Doob transform is row-stochastic.**  Each row of `P` sums to one,
because `w` is a right eigenvector: `∑ j M i j w j = λ w i`. -/
theorem matrixDoobTransform_row_sum {M : Matrix Ω Ω ℝ} {lam : ℝ} {w : Ω → ℝ}
    (hw_eig : M.mulVec w = lam • w) (hlam : lam ≠ 0) (hw : ∀ i, w i ≠ 0) (i : Ω) :
    ∑ j, matrixDoobTransform M lam w i j = 1 := by
  simp only [matrixDoobTransform]
  rw [← Finset.sum_div]
  have h : ∑ j, M i j * w j = lam * w i := by
    have hi := congr_fun hw_eig i
    rw [Matrix.mulVec, dotProduct] at hi
    simpa [Pi.smul_apply, smul_eq_mul] using hi
  rw [h, div_self (mul_ne_zero hlam (hw i))]

/-- **The Doob transform conjugates eigenvectors.**  If `v` is an eigenvector of
`M` with eigenvalue `μ`, then `v / w` is an eigenvector of `P` with eigenvalue
`μ / λ`. -/
theorem matrixDoobTransform_mulVec {M : Matrix Ω Ω ℝ} {lam : ℝ} {w : Ω → ℝ}
    (hlam : lam ≠ 0) (hw : ∀ i, w i ≠ 0)
    {v : Ω → ℝ} {mu : ℝ} (hv_eig : M.mulVec v = mu • v) :
    (matrixDoobTransform M lam w).mulVec (fun i => v i / w i)
      = (mu / lam) • (fun i => v i / w i) := by
  funext i
  rw [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  simp only [matrixDoobTransform]
  have hstep : ∀ j, M i j * w j / (lam * w i) * (v j / w j) = M i j * v j / (lam * w i) := by
    intro j
    rw [div_mul_div_comm]
    field_simp [hw j]
  simp_rw [hstep]
  rw [← Finset.sum_div]
  have h : ∑ j, M i j * v j = mu * v i := by
    have hi := congr_fun hv_eig i
    rw [Matrix.mulVec, dotProduct] at hi
    simpa [Pi.smul_apply, smul_eq_mul] using hi
  rw [h]
  field_simp [hlam, hw i]

end TransferMatrix

end IsingModel

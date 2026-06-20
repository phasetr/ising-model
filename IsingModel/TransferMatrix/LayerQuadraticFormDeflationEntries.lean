import IsingModel.TransferMatrix.LayerQuadraticFormDeflation

/-!
# Entries and annihilation identity of the top deflation

This file exposes the entrywise structure of the top-eigenpair deflation
`matrixTopDeflation E top = M − λ_top · w_top w_topᵀ` of
`LayerQuadraticFormDeflation`, and records the defining annihilation identity:
the deflation kills the top spectral column.

These accessors reduce the deflated Gershgorin quantity that controls the strict
gap to explicit expressions in the original matrix entries and the top
eigenvector components `w_top x = changeOfBasis x top`.  The annihilation identity
`(deflation) · w_top = 0` confirms that the maximal eigenvalue is removed by the
deflation, isolating the genuinely remaining task — a quantitative entrywise
bound on `λ_top · w_i w_j` (a Perron--Frobenius / Hilbert-metric estimate) — for a
later file.

The results are finite, unconditional algebraic identities.  They do not bound the
deflated entries quantitatively, construct a strict spectral gap, prove a
thermodynamic limit, or prove final hyperplane exponential decay.

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

/-- Entry of the top deflation. -/
theorem matrixTopDeflation_apply {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M)
    (top i j : Ω) :
    E.matrixTopDeflation top i j =
      M i j - E.eigenvalue top * (E.changeOfBasis i top * E.changeOfBasis j top) :=
  rfl

/-- Diagonal entry of the top deflation in terms of the top eigenvector
component. -/
theorem matrixTopDeflation_diag {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M)
    (top i : Ω) :
    E.matrixTopDeflation top i i =
      M i i - E.eigenvalue top * (E.changeOfBasis i top) ^ 2 := by
  rw [matrixTopDeflation_apply]; ring

/-- Off-diagonal absolute row sum of the top deflation in terms of the original
entries and the top eigenvector components. -/
theorem matrixTopDeflation_offDiagAbsRowSum {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (top i : Ω) :
    matrixOffDiagAbsRowSum (E.matrixTopDeflation top) i =
      ∑ j ∈ Finset.univ.erase i,
        |M i j - E.eigenvalue top * (E.changeOfBasis i top * E.changeOfBasis j top)| := by
  rw [matrixOffDiagAbsRowSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [matrixTopDeflation_apply]

/-- **Deflation annihilates the top column.**  The top-eigenpair deflation maps
the maximal spectral column to zero, confirming the maximal eigenvalue is removed.
This follows from the eigen-equation `M · w_top = λ_top · w_top` and the unit norm
`∑ x (w_top x)² = 1`. -/
theorem matrixTopDeflation_mulVec_column_eq_zero {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (top : Ω) :
    (E.matrixTopDeflation top).mulVec (fun x => E.changeOfBasis x top) = 0 := by
  funext i
  have hmul := congr_fun (E.mulVec_changeOfBasis_column top) i
  rw [Matrix.mulVec, dotProduct] at hmul
  have hnorm := E.vectorSqNorm_changeOfBasis_column top
  rw [vectorSqNorm] at hnorm
  rw [Matrix.mulVec, dotProduct, Pi.zero_apply]
  have hstep : ∀ j, E.matrixTopDeflation top i j * E.changeOfBasis j top
      = M i j * E.changeOfBasis j top
        - E.eigenvalue top * E.changeOfBasis i top * (E.changeOfBasis j top) ^ 2 := by
    intro j; rw [matrixTopDeflation_apply]; ring
  simp_rw [hstep]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hnorm, hmul]
  simp [Pi.smul_apply, smul_eq_mul]

end RealOrthogonalSpectralData

end TransferMatrix

end IsingModel

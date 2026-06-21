import IsingModel.TransferMatrix.LayerQuadraticFormDeflationGap

/-!
# The top-deflation row cancellation identity (GJ §17.1, P5)

The top-deflated matrix `M_def = M − λ_max·w wᵀ` (with `w` the Perron column) annihilates `w`:
`M_def · w = 0` (`matrixTopDeflation_mulVec_column_eq_zero`). Splitting the row `i` of this identity
into its diagonal and off-diagonal parts expresses the deflated **diagonal** entry as a
Perron-weighted sum of the deflated **off-diagonal** entries:
`M_def_ii = − ∑_{j≠i} M_def_ij · (w_j / w_i)`.

This is the structural form of the spectral gap: the cancellation between `M_ij` and `λ_max·w_i·w_j`
is encoded by the eigen-equation, *not* destroyed by a triangle inequality. The maximal-eigenvalue
deflation thus bounds the deflated diagonal by the deflated off-diagonal mass weighted by Perron
ratios — the route to a subdominant ratio `θ < 1`.

* `matrixTopDeflation_diag_eq_neg_weighted_offDiag` — the row cancellation identity.
* `abs_matrixTopDeflation_diag_le_weighted_offDiag` — its absolute-value corollary.
* `changeOfBasis_maxEigenIndex_ne_zero_of_entrywisePositive` — the Perron column has no zero entry
  (entrywise positive `M`), discharging the `w_i ≠ 0` hypothesis.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §17.1.
-/

namespace IsingModel

namespace TransferMatrix

namespace RealOrthogonalSpectralData

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- **The top-deflation row cancellation identity**: since `M_def · w = 0` for the Perron column
`w = changeOfBasis · top`, the deflated diagonal entry equals minus the Perron-weighted sum of the
deflated off-diagonal entries, `M_def_ii = − ∑_{j≠i} M_def_ij · (w_j / w_i)` (needs `w_i ≠ 0`). -/
theorem matrixTopDeflation_diag_eq_neg_weighted_offDiag {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (top i : Ω)
    (hi : E.changeOfBasis i top ≠ 0) :
    E.matrixTopDeflation top i i =
      - ∑ j ∈ Finset.univ.erase i,
        E.matrixTopDeflation top i j * (E.changeOfBasis j top / E.changeOfBasis i top) := by
  have hzero := congr_fun (E.matrixTopDeflation_mulVec_column_eq_zero top) i
  rw [Matrix.mulVec, dotProduct, Pi.zero_apply] at hzero
  rw [← Finset.add_sum_erase Finset.univ
      (fun j => E.matrixTopDeflation top i j * E.changeOfBasis j top) (Finset.mem_univ i)] at hzero
  rw [show (- ∑ j ∈ Finset.univ.erase i,
        E.matrixTopDeflation top i j * (E.changeOfBasis j top / E.changeOfBasis i top))
      = (- ∑ j ∈ Finset.univ.erase i,
        E.matrixTopDeflation top i j * E.changeOfBasis j top) / E.changeOfBasis i top from by
    rw [neg_div, Finset.sum_div]
    exact congrArg Neg.neg (Finset.sum_congr rfl (fun j _ => by rw [mul_div_assoc]))]
  rw [eq_div_iff hi]
  linarith [hzero]

/-- **Absolute-value form of the row cancellation identity**: `|M_def_ii|` is at most the
Perron-ratio-weighted absolute off-diagonal mass. -/
theorem abs_matrixTopDeflation_diag_le_weighted_offDiag {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (top i : Ω)
    (hi : E.changeOfBasis i top ≠ 0) :
    |E.matrixTopDeflation top i i| ≤
      ∑ j ∈ Finset.univ.erase i,
        |E.matrixTopDeflation top i j| * |E.changeOfBasis j top / E.changeOfBasis i top| := by
  rw [matrixTopDeflation_diag_eq_neg_weighted_offDiag E top i hi, abs_neg]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  exact Finset.sum_congr rfl (fun j _ => abs_mul _ _)

/-- **The Perron column has no zero entry**: for an entrywise positive matrix the maximal spectral
column `changeOfBasis · maxEigenIndex` is signed-positive, so every entry is nonzero. This discharges
the `w_i ≠ 0` hypothesis of the row cancellation identity. -/
theorem changeOfBasis_maxEigenIndex_ne_zero_of_entrywisePositive [Nonempty Ω] {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (hM : MatrixEntrywisePositive M) (i : Ω) :
    E.changeOfBasis i E.maxEigenIndex ≠ 0 := by
  intro h
  have hpos := (E.signedPositiveColumn_maxEigenIndex hM).positive i
  simp only [h, mul_zero, lt_self_iff_false] at hpos

end RealOrthogonalSpectralData

end TransferMatrix

end IsingModel

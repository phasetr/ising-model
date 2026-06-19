import IsingModel.TransferMatrix.LayerOpenExplicitSubdominantRatio

/-!
# Quadratic-form spectral gap for the explicit subdominant ratio

This file reduces the explicit subdominant absolute ratio bound of
`LayerOpenExplicitSubdominantRatio` to a **quadratic-form gap** on the subspace
orthogonal to the maximal spectral column.  For a real orthogonally diagonalized
matrix, every non-maximal spectral column is a unit eigenvector whose spectral
coordinate at the maximal index vanishes, so a uniform Rayleigh bound
`|⟨v, M v⟩| ≤ ρ·‖v‖²` over that orthogonal subspace controls every non-maximal
eigenvalue in absolute value, hence the explicit subdominant ratio.

This is exactly the object a transverse-volume-uniform high-temperature estimate
(Dobrushin contraction / Hilbert projective metric) must produce: instead of an
eigenvalue list, it suffices to bound the transfer-matrix quadratic form on the
top-orthogonal subspace by `θ·λ_top·‖v‖²` with `θ` independent of the transverse
box radius.

The results are finite and conditional on the quadratic-form gap.  They do not
construct that gap, prove a thermodynamic limit, or prove final hyperplane
exponential decay.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

namespace RealOrthogonalSpectralData

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- A non-maximal spectral column has vanishing spectral coordinate at any other
index: the spectral columns are orthonormal. -/
theorem spectralCoord_changeOfBasis_column_ne {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) {i top : Ω} (hi : i ≠ top) :
    E.spectralCoord (fun x => E.changeOfBasis x i) top = 0 := by
  have h := congr_fun (congr_fun E.orthogonal_left top) i
  rw [Matrix.mul_apply, Matrix.one_apply, if_neg (fun he => hi he.symm)] at h
  simp only [Matrix.transpose_apply] at h
  rw [spectralCoord]
  rw [← h]

/-- A quadratic-form gap on the subspace orthogonal to the column `top` bounds
every non-`top` spectral eigenvalue in absolute value.  Applying the gap to the
`i`-th unit spectral column, whose quadratic form is `λ_i` and whose squared norm
is `1`, gives `|λ_i| ≤ ρ`. -/
theorem eigenvalue_abs_le_of_quadraticForm_gap {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) {top : Ω} {rho : ℝ}
    (hgap : ∀ v : Ω → ℝ, E.spectralCoord v top = 0 →
      |matrixQuadraticForm M v| ≤ rho * vectorSqNorm v)
    (i : Ω) (hi : i ≠ top) :
    |E.eigenvalue i| ≤ rho := by
  have hcol := hgap (fun x => E.changeOfBasis x i)
    (E.spectralCoord_changeOfBasis_column_ne hi)
  rw [matrixQuadraticForm_eq_eigenvalue_mul_sqNorm _ (E.mulVec_changeOfBasis_column i),
    E.vectorSqNorm_changeOfBasis_column i] at hcol
  simpa using hcol

/-- A quadratic-form gap `|⟨v, M v⟩| ≤ θ·λ_max·‖v‖²` on the subspace orthogonal to
the maximal spectral column bounds the explicit subdominant absolute ratio by
`θ`.  This composes the gap-to-eigenvalue bound with the explicit-ratio hook of
`LayerOpenExplicitSubdominantRatio`. -/
theorem subdominantAbsRatio_maxEigenIndex_le_of_quadraticForm_gap [Nonempty Ω]
    {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M)
    (hM : MatrixEntrywisePositive M) {theta : ℝ} (htheta : 0 ≤ theta)
    (hgap : ∀ v : Ω → ℝ, E.spectralCoord v E.maxEigenIndex = 0 →
      |matrixQuadraticForm M v| ≤
        (theta * E.eigenvalue E.maxEigenIndex) * vectorSqNorm v) :
    E.subdominantAbsRatio_maxEigenIndex hM ≤ theta := by
  refine E.subdominantAbsRatio_maxEigenIndex_le_of_eigenvalue_abs_le hM htheta ?_
  intro i hi
  exact E.eigenvalue_abs_le_of_quadraticForm_gap
    (rho := theta * E.eigenvalue E.maxEigenIndex) hgap i hi

end RealOrthogonalSpectralData

/-! ## Layer wrappers -/

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The explicit subdominant ratio of the generic Hermitian layer spectral data
is bounded by `θ` whenever the layer transfer matrix has a quadratic-form gap of
size `θ·λ_max` on the subspace orthogonal to its maximal spectral column. -/
theorem finiteTransverseHermitianExplicitRatio_le_of_quadraticForm_gap
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ)
    (hk_symm : ∀ ω η,
      layerTransitionWeight transitionPairs p ω η =
        layerTransitionWeight transitionPairs p η ω)
    {theta : ℝ} (htheta : 0 ≤ theta)
    (hgap : ∀ v : LayerState S → ℝ,
      (finiteTransverseHermitianData H transitionPairs p hk_symm).spectralCoord v
          (finiteTransverseHermitianData H transitionPairs p hk_symm).maxEigenIndex = 0 →
        |matrixQuadraticForm
            (layerSymmetricTransferMatrix
              (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)) v| ≤
          (theta *
            (finiteTransverseHermitianData H transitionPairs p hk_symm).eigenvalue
              (finiteTransverseHermitianData H transitionPairs p hk_symm).maxEigenIndex) *
            vectorSqNorm v) :
    finiteTransverseHermitianExplicitRatio H transitionPairs p hk_symm ≤ theta :=
  (finiteTransverseHermitianData H transitionPairs p
    hk_symm).subdominantAbsRatio_maxEigenIndex_le_of_quadraticForm_gap
    (finiteTransverseHermitian_entrywisePositive H transitionPairs p) htheta hgap

/-- Cubic specialization: the cubic explicit subdominant ratio is bounded by `θ`
from a quadratic-form gap of size `θ·λ_max`. -/
theorem cubicLayerHermitianExplicitRatio_le_of_quadraticForm_gap
    (d R : ℕ) (p : IsingParams ℝ) {theta : ℝ} (htheta : 0 ≤ theta)
    (hgap : ∀ v : LayerState (CubicLayerSite d R) → ℝ,
      (cubicLayerHermitianData d R p).spectralCoord v
          (cubicLayerHermitianData d R p).maxEigenIndex = 0 →
        |matrixQuadraticForm
            (layerSymmetricTransferMatrix
              (layerInternalWeight (cubicLayerGraph d R) p)
              (layerTransitionWeight (cubicLayerTransitionPairs d R) p)) v| ≤
          (theta * (cubicLayerHermitianData d R p).eigenvalue
            (cubicLayerHermitianData d R p).maxEigenIndex) * vectorSqNorm v) :
    cubicLayerHermitianExplicitRatio d R p ≤ theta :=
  finiteTransverseHermitianExplicitRatio_le_of_quadraticForm_gap (cubicLayerGraph d R)
    (cubicLayerTransitionPairs d R) p (cubicLayerTransitionWeight_symm d R p) htheta hgap

end TransferMatrix

end IsingModel

import IsingModel.TransferMatrix.LayerOpenSpectral.PathGlue
import IsingModel.TransferMatrix.LayerSpectral.FlipParity

/-!
# Open boundary-vector spectral form

The balanced open boundary vector and the boundary-vector spectral expansion and
estimate for the open marked matrix-product numerator.

This is a build-speed split child of `LayerOpenSpectral`; see that umbrella
module for the mathematical overview and references.
-/

namespace IsingModel

namespace TransferMatrix

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-! ## Open boundary-vector spectral form -/

/-- The balanced open boundary vector obtained after the diagonal similarity
`T = D⁻¹ S D`. -/
noncomputable def layerOpenBalancedBoundaryVector (u : Ω → ℝ) : Ω → ℝ :=
  fun a => Real.sqrt (u a)

/-- The open marked matrix-product numerator is the balanced boundary-vector
marked product after the diagonal similarity from `layerTransferMatrix` to
`layerSymmetricTransferMatrix`. -/
theorem layerOpenTwoPointMatrixProductNumerator_eq_balancedBoundaryMarkedProduct
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (hu : ∀ a, 0 < u a) (left sep right : ℕ) :
    layerOpenTwoPointMatrixProductNumerator u k f left sep right =
      RealOrthogonalSpectralData.boundaryMarkedProduct
        (layerSymmetricTransferMatrix u k)
        (layerOpenBalancedBoundaryVector u) f
        (layerOpenBalancedBoundaryVector u) left sep right := by
  let S := layerSymmetricTransferMatrix u k
  let D := layerTransferSqrtDiagonal u
  let Dinv := layerTransferSqrtDiagonalInv u
  let F := Matrix.diagonal f
  have hT : layerTransferMatrix u k = Dinv * S * D :=
    layerTransferMatrix_eq_sqrtDiagonalInv_mul_symm_mul_sqrtDiagonal u k hu
  have hDinvD : Dinv * D = 1 := layerTransferSqrtDiagonalInv_mul_sqrtDiagonal u hu
  have hDDinv : D * Dinv = 1 := layerTransferSqrtDiagonal_mul_sqrtDiagonalInv u hu
  have hFD : F * D = D * F := by
    dsimp [F, D, layerTransferSqrtDiagonal]
    exact diagonal_mul_comm f fun x => Real.sqrt (u x)
  have hprod :
      layerTransferMatrix u k ^ left * F * layerTransferMatrix u k ^ sep *
          F * layerTransferMatrix u k ^ right =
        Dinv * (S ^ left * F * S ^ sep * F * S ^ right) * D := by
    rw [hT, matrix_conj_pow S Dinv D hDinvD hDDinv left,
      matrix_conj_pow S Dinv D hDinvD hDDinv sep,
      matrix_conj_pow S Dinv D hDinvD hDDinv right]
    calc
      (Dinv * S ^ left * D) * F * (Dinv * S ^ sep * D) * F *
          (Dinv * S ^ right * D)
          = Dinv * S ^ left * (D * F) * Dinv * S ^ sep * (D * F) *
              Dinv * S ^ right * D := by
            noncomm_ring
      _ = Dinv * S ^ left * (F * D) * Dinv * S ^ sep * (F * D) *
              Dinv * S ^ right * D := by
            rw [hFD]
      _ = Dinv * (S ^ left * F * S ^ sep * F * S ^ right) * D := by
            noncomm_ring [hDDinv]
  unfold layerOpenTwoPointMatrixProductNumerator
    RealOrthogonalSpectralData.boundaryMarkedProduct layerOpenBalancedBoundaryVector
  dsimp only
  rw [hprod]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp [Dinv, D, layerTransferSqrtDiagonalInv, layerTransferSqrtDiagonal,
    Matrix.diagonal_mul, Matrix.mul_diagonal]
  field_simp [(Real.sqrt_pos_of_pos (hu a)).ne']
  rw [Real.sq_sqrt (le_of_lt (hu a))]
  ring

/-- The open marked matrix-product numerator in boundary-vector spectral
coordinates for the balanced transfer matrix. -/
theorem layerOpenTwoPointMatrixProductNumerator_eq_boundarySpectralSum
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (hu : ∀ a, 0 < u a)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (left sep right : ℕ) :
    layerOpenTwoPointMatrixProductNumerator u k f left sep right =
      ∑ i, ∑ j, ∑ l,
        E.boundaryCoordinates (layerOpenBalancedBoundaryVector u) i *
        E.eigenvalue i ^ left *
        E.markedMatrix f i j *
        E.eigenvalue j ^ sep *
        E.markedMatrix f j l *
        E.eigenvalue l ^ right *
        E.boundaryCoordinates (layerOpenBalancedBoundaryVector u) l := by
  rw [layerOpenTwoPointMatrixProductNumerator_eq_balancedBoundaryMarkedProduct
    u k f hu left sep right]
  exact RealOrthogonalSpectralData.boundaryMarkedProduct_eq_spectralSum
    E (layerOpenBalancedBoundaryVector u) f (layerOpenBalancedBoundaryVector u)
    left sep right

/-- A boundary-vector spectral estimate bounds the open marked matrix-product
numerator in the marked separation. -/
theorem layerOpenTwoPointMatrixProductNumerator_abs_le_boundarySpectralPrefactor
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (hu : ∀ a, 0 < u a)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (top : Ω) (scale theta : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (eigenvalue_abs_le_scale : ∀ i, |E.eigenvalue i| ≤ scale)
    (subdominant_abs_le : ∀ i, i ≠ top → |E.eigenvalue i| ≤ theta * scale)
    (central_dominant_channel_zero : ∀ i l,
      E.boundaryCoordinates (layerOpenBalancedBoundaryVector u) i *
        E.markedMatrix f i top *
        E.markedMatrix f top l *
        E.boundaryCoordinates (layerOpenBalancedBoundaryVector u) l = 0)
    (left sep right : ℕ) :
    |layerOpenTwoPointMatrixProductNumerator u k f left sep right|
      ≤ E.boundaryMarkedSpectralPrefactor f
          (layerOpenBalancedBoundaryVector u) (layerOpenBalancedBoundaryVector u) *
        scale ^ (left + sep + right) * theta ^ sep := by
  rw [layerOpenTwoPointMatrixProductNumerator_eq_boundarySpectralSum u k f hu E
    left sep right]
  exact RealOrthogonalSpectralData.boundaryMarkedSpectralSum_abs_le_spectralPrefactor
    E f (layerOpenBalancedBoundaryVector u) (layerOpenBalancedBoundaryVector u)
    top scale theta scale_pos theta_nonneg eigenvalue_abs_le_scale
    subdominant_abs_le central_dominant_channel_zero left sep right

end TransferMatrix

end IsingModel

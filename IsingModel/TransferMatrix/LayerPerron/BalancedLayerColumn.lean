import IsingModel.TransferMatrix.LayerPerron.PositiveColumn
import IsingModel.TransferMatrix.LayerSpectral.BalancedSpectralGap
import IsingModel.TransferMatrix.LayerSpectral.FlipParityLayerSymmetric
import IsingModel.TransferMatrix.LayerSpectral.HermitianBridge
import IsingModel.TransferMatrix.LayerSpectral.BalancedMatrix
import IsingModel.TransferMatrix.LayerSpectral.Positivity
import IsingModel.TransferMatrix.LayerGibbs

/-!
# Positive/simple Perron bridge (4/5): balanced layer columns and scale-fixed certificates

Structural split (4/5) of `TransferMatrix.LayerPerron`.  This child holds the balanced
layer transfer-matrix restatements of the positive-column conclusions (absolute
eigenvalue bound, eigenspace simplicity, strict bound off the top column, and the finite
subdominant ratio), together with the two general-`Ω` minimal-spectral-gap certificate
constructors that fix the transfer scale to the positive top column's eigenvalue.  See the
`IsingModel.TransferMatrix.LayerPerron` facade module for the full contents overview.
-/

namespace IsingModel

namespace TransferMatrix

open Matrix

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- For a balanced positive layer transfer matrix, a positive Hermitian spectral
column has an eigenvalue that bounds all spectral-data eigenvalues in absolute
value. -/
theorem layerSymmetricTransfer_eigenvalue_abs_le_of_positive_column
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (hk_symm : ∀ ω η, k ω η = k η ω)
    (top i : LayerState S)
    (hpos : VectorPositive
      (fun ω =>
        (layerSymmetricTransferOrthogonalSpectralData u k hk_symm).changeOfBasis ω top)) :
    |(layerSymmetricTransferOrthogonalSpectralData u k hk_symm).eigenvalue i|
      ≤ (layerSymmetricTransferOrthogonalSpectralData u k hk_symm).eigenvalue top :=
  RealOrthogonalSpectralData.eigenvalue_abs_le_of_positive_column
    (layerSymmetricTransferOrthogonalSpectralData u k hk_symm)
    (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos)
    top i hpos

/-- For a balanced positive layer transfer matrix, a positive Hermitian spectral
column spans its eigenspace. -/
theorem layerSymmetricTransfer_positive_column_eigenspace_simple
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (hk_symm : ∀ ω η, k ω η = k η ω)
    (top : LayerState S)
    (hpos : VectorPositive
      (fun ω =>
        (layerSymmetricTransferOrthogonalSpectralData u k hk_symm).changeOfBasis ω top))
    (w : LayerState S → ℝ)
    (hw_eig : (layerSymmetricTransferMatrix u k).mulVec w =
      (layerSymmetricTransferOrthogonalSpectralData u k hk_symm).eigenvalue top • w) :
    ∃ c : ℝ,
      w = c •
        (fun ω =>
          (layerSymmetricTransferOrthogonalSpectralData u k hk_symm).changeOfBasis ω top) :=
  RealOrthogonalSpectralData.eigenspace_simple_of_positive_column
    (layerSymmetricTransferOrthogonalSpectralData u k hk_symm)
    (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos)
    top hpos w hw_eig

/-- For a balanced positive layer transfer matrix, every non-top Hermitian
spectral-data eigenvalue is strictly smaller in absolute value than the
positive top column's eigenvalue. -/
theorem layerSymmetricTransfer_eigenvalue_abs_lt_of_positive_column
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (hk_symm : ∀ ω η, k ω η = k η ω)
    (top i : LayerState S) (hi : i ≠ top)
    (hpos : VectorPositive
      (fun ω =>
        (layerSymmetricTransferOrthogonalSpectralData u k hk_symm).changeOfBasis ω top)) :
    |(layerSymmetricTransferOrthogonalSpectralData u k hk_symm).eigenvalue i|
      < (layerSymmetricTransferOrthogonalSpectralData u k hk_symm).eigenvalue top :=
  RealOrthogonalSpectralData.eigenvalue_abs_lt_of_positive_column
    (layerSymmetricTransferOrthogonalSpectralData u k hk_symm)
    (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos)
    top i hi hpos

/-- For a balanced positive layer transfer matrix, a positive Hermitian spectral
top column gives some strict finite subdominant ratio for all non-top spectral
data eigenvalues. -/
theorem layerSymmetricTransfer_exists_subdominant_abs_ratio_of_positive_column
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (hk_symm : ∀ ω η, k ω η = k η ω)
    (top : LayerState S)
    (hpos : VectorPositive
      (fun ω =>
        (layerSymmetricTransferOrthogonalSpectralData u k hk_symm).changeOfBasis ω top)) :
    ∃ theta : ℝ, 0 ≤ theta ∧ theta < 1 ∧
      ∀ i, i ≠ top →
        |(layerSymmetricTransferOrthogonalSpectralData u k hk_symm).eigenvalue i|
          ≤ theta *
            (layerSymmetricTransferOrthogonalSpectralData u k hk_symm).eigenvalue top :=
  RealOrthogonalSpectralData.exists_subdominant_abs_ratio_of_positive_column
    (layerSymmetricTransferOrthogonalSpectralData u k hk_symm)
    (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos)
    top hpos

/-- Orthogonal spectral-data constructor with the transfer scale fixed to the
positive top spectral column's eigenvalue.  This removes the separate
`scale`, `scale_pos`, and `dominant_eigenvalue` inputs, but still assumes the
quantitative subdominant bound. -/
noncomputable def layerBalancedMinSpectralGapCertificate_of_orthogonalSubdominantBounds
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (hu : ∀ a, 0 < u a) (hk_pos : ∀ a b, 0 < k a b)
    (top : Ω) (theta : ℝ)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (partitionPrefactor_small :
      (((Fintype.card Ω - 1 : ℕ) : ℝ) * theta) < 1)
    (subdominant_abs_le : ∀ i, i ≠ top →
      |E.eigenvalue i| ≤ theta * E.eigenvalue top)
    (dominant_column_pos : VectorPositive (fun a => E.changeOfBasis a top))
    (dominant_markedDiagonal_zero : E.markedMatrix f top top = 0) :
    LayerBalancedMinSpectralGapCertificate u k f := by
  letI : Nonempty Ω := ⟨top⟩
  exact layerBalancedMinSpectralGapCertificate_of_orthogonalDominantBounds
    u k f E top (E.eigenvalue top) theta
    (E.eigenvalue_pos_of_positive_column
      (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos) top
      dominant_column_pos)
    theta_nonneg theta_lt_one partitionPrefactor_small rfl subdominant_abs_le
    dominant_markedDiagonal_zero

/-- Hermitian spectral-data constructor with the transfer scale fixed to the
positive top spectral column's eigenvalue. -/
noncomputable def layerBalancedMinSpectralGapCertificate_of_layerHermitianSubdominantBounds
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (hu : ∀ a, 0 < u a) (hk_pos : ∀ a b, 0 < k a b)
    (hk : ∀ a b, k a b = k b a)
    (top : Ω) (theta : ℝ)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (partitionPrefactor_small :
      (((Fintype.card Ω - 1 : ℕ) : ℝ) * theta) < 1)
    (subdominant_abs_le : ∀ i, i ≠ top →
      |(layerSymmetricTransferOrthogonalSpectralData u k hk).eigenvalue i|
        ≤ theta * (layerSymmetricTransferOrthogonalSpectralData u k hk).eigenvalue top)
    (dominant_column_pos : VectorPositive
      (fun a => (layerSymmetricTransferOrthogonalSpectralData u k hk).changeOfBasis a top))
    (dominant_markedDiagonal_zero :
      (layerSymmetricTransferOrthogonalSpectralData u k hk).markedMatrix f top top = 0) :
    LayerBalancedMinSpectralGapCertificate u k f :=
  layerBalancedMinSpectralGapCertificate_of_orthogonalSubdominantBounds
    u k f (layerSymmetricTransferOrthogonalSpectralData u k hk) hu hk_pos
    top theta theta_nonneg theta_lt_one partitionPrefactor_small
    subdominant_abs_le dominant_column_pos dominant_markedDiagonal_zero

end TransferMatrix

end IsingModel

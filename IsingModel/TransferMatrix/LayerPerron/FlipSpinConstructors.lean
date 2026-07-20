import IsingModel.TransferMatrix.LayerPerron.PositiveColumn
import IsingModel.TransferMatrix.LayerPerron.FlipEvenInvolution
import IsingModel.TransferMatrix.LayerSpectral.BalancedSpectralGap
import IsingModel.TransferMatrix.LayerSpectral.FlipParityLayerSymmetric
import IsingModel.TransferMatrix.LayerSpectral.BalancedMatrix
import IsingModel.TransferMatrix.LayerSpectral.HermitianBridge
import IsingModel.TransferMatrix.LayerSpectral.Positivity
import IsingModel.TransferMatrix.LayerGibbs

/-!
# Positive/simple Perron bridge (5/5): spin-observable certificate constructors

Structural split (5/5) of `TransferMatrix.LayerPerron`.  This child holds the eight
minimal-spectral-gap certificate constructors for layer spin observables that replace the
direct flip-evenness hypothesis by positivity of the dominant column: the
`positiveSimpleFlipSpin` family, where the caller still supplies eigenspace simplicity, and
the `positiveColumnFlipSpin` family, where simplicity is derived from entrywise positivity
of the balanced transfer matrix, each in orthogonal and Hermitian spectral-data variants
with a free or a scale-fixed transfer scale.  See the
`IsingModel.TransferMatrix.LayerPerron` facade module for the full contents overview.
-/

namespace IsingModel

namespace TransferMatrix

open Matrix

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- Orthogonal spectral-data constructor for spin observables using positive
simple dominant-column inputs instead of a direct flip-evenness hypothesis. -/
noncomputable def
    layerBalancedMinSpectralGapCertificate_of_orthogonalDominantBounds_positiveSimpleFlipSpin
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (top : LayerState S) (scale theta : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (partitionPrefactor_small :
      (((Fintype.card (LayerState S) - 1 : ℕ) : ℝ) * theta) < 1)
    (dominant_eigenvalue : E.eigenvalue top = scale)
    (subdominant_abs_le : ∀ i, i ≠ top → |E.eigenvalue i| ≤ theta * scale)
    (dominant_column_pos : VectorPositive (fun ω => E.changeOfBasis ω top))
    (dominant_eigenspace_simple : ∀ w : LayerState S → ℝ,
      (layerSymmetricTransferMatrix u k).mulVec w = E.eigenvalue top • w →
        ∃ c : ℝ, w = c • (fun ω => E.changeOfBasis ω top)) :
    LayerBalancedMinSpectralGapCertificate u k (layerSpinAt x) :=
  layerBalancedMinSpectralGapCertificate_of_orthogonalDominantBounds_flipEvenSpin
    u k x E top scale theta scale_pos theta_nonneg theta_lt_one
    partitionPrefactor_small dominant_eigenvalue subdominant_abs_le
    (layerSymmetricTransfer_positive_eigenvector_flip_even_of_simple_eigenspace
      u k hu_flip hk_flip dominant_column_pos (E.mulVec_changeOfBasis_column top)
      dominant_eigenspace_simple)

/-- Spin-observable constructor with the transfer scale fixed to the positive
top spectral column's eigenvalue, using positive simple dominant-column inputs
instead of a direct flip-evenness hypothesis. -/
noncomputable def
    layerBalancedMinSpectralGapCertificate_of_orthogonalSubdominantBounds_positiveSimpleFlipSpin
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (top : LayerState S) (theta : ℝ)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (partitionPrefactor_small :
      (((Fintype.card (LayerState S) - 1 : ℕ) : ℝ) * theta) < 1)
    (subdominant_abs_le : ∀ i, i ≠ top → |E.eigenvalue i| ≤ theta * E.eigenvalue top)
    (dominant_column_pos : VectorPositive (fun ω => E.changeOfBasis ω top))
    (dominant_eigenspace_simple : ∀ w : LayerState S → ℝ,
      (layerSymmetricTransferMatrix u k).mulVec w = E.eigenvalue top • w →
        ∃ c : ℝ, w = c • (fun ω => E.changeOfBasis ω top)) :
    LayerBalancedMinSpectralGapCertificate u k (layerSpinAt x) := by
  letI : Nonempty (LayerState S) := ⟨top⟩
  exact layerBalancedMinSpectralGapCertificate_of_orthogonalDominantBounds_positiveSimpleFlipSpin
    u k x hu_flip hk_flip E top (E.eigenvalue top) theta
    (E.eigenvalue_pos_of_positive_column
      (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos) top
      dominant_column_pos)
    theta_nonneg theta_lt_one partitionPrefactor_small rfl subdominant_abs_le
    dominant_column_pos dominant_eigenspace_simple

/-- Hermitian spectral-data constructor for spin observables using positive
simple dominant-column inputs instead of a direct flip-evenness hypothesis. -/
noncomputable def
    layerBalancedMinSpectralGapCertificate_of_layerHermitianDominantBounds_positiveSimpleFlipSpin
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hk : ∀ a b, k a b = k b a)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (top : LayerState S) (scale theta : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (partitionPrefactor_small :
      (((Fintype.card (LayerState S) - 1 : ℕ) : ℝ) * theta) < 1)
    (dominant_eigenvalue :
      (layerSymmetricTransferOrthogonalSpectralData u k hk).eigenvalue top = scale)
    (subdominant_abs_le : ∀ i, i ≠ top →
      |(layerSymmetricTransferOrthogonalSpectralData u k hk).eigenvalue i|
        ≤ theta * scale)
    (dominant_column_pos :
      VectorPositive
        (fun ω =>
          (layerSymmetricTransferOrthogonalSpectralData u k hk).changeOfBasis ω top))
    (dominant_eigenspace_simple : ∀ w : LayerState S → ℝ,
      (layerSymmetricTransferMatrix u k).mulVec w =
          (layerSymmetricTransferOrthogonalSpectralData u k hk).eigenvalue top • w →
        ∃ c : ℝ,
          w = c •
            (fun ω =>
              (layerSymmetricTransferOrthogonalSpectralData u k hk).changeOfBasis ω top)) :
    LayerBalancedMinSpectralGapCertificate u k (layerSpinAt x) :=
  layerBalancedMinSpectralGapCertificate_of_orthogonalDominantBounds_positiveSimpleFlipSpin
    u k x hu_flip hk_flip (layerSymmetricTransferOrthogonalSpectralData u k hk)
    top scale theta scale_pos theta_nonneg theta_lt_one partitionPrefactor_small
    dominant_eigenvalue subdominant_abs_le dominant_column_pos
    dominant_eigenspace_simple

/-- Hermitian spin-observable constructor with the transfer scale fixed to the
positive top spectral column's eigenvalue, using positive simple
dominant-column inputs instead of a direct flip-evenness hypothesis. -/
noncomputable def
    layerBalancedMinSpectralGapCertificate_of_layerHermitianSubdominantBounds_positiveSimpleFlipSpin
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (hk : ∀ a b, k a b = k b a)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (top : LayerState S) (theta : ℝ)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (partitionPrefactor_small :
      (((Fintype.card (LayerState S) - 1 : ℕ) : ℝ) * theta) < 1)
    (subdominant_abs_le : ∀ i, i ≠ top →
      |(layerSymmetricTransferOrthogonalSpectralData u k hk).eigenvalue i|
        ≤ theta * (layerSymmetricTransferOrthogonalSpectralData u k hk).eigenvalue top)
    (dominant_column_pos :
      VectorPositive
        (fun ω =>
          (layerSymmetricTransferOrthogonalSpectralData u k hk).changeOfBasis ω top))
    (dominant_eigenspace_simple : ∀ w : LayerState S → ℝ,
      (layerSymmetricTransferMatrix u k).mulVec w =
          (layerSymmetricTransferOrthogonalSpectralData u k hk).eigenvalue top • w →
        ∃ c : ℝ,
          w = c •
            (fun ω =>
              (layerSymmetricTransferOrthogonalSpectralData u k hk).changeOfBasis ω top)) :
    LayerBalancedMinSpectralGapCertificate u k (layerSpinAt x) :=
  layerBalancedMinSpectralGapCertificate_of_orthogonalSubdominantBounds_positiveSimpleFlipSpin
    u k x hu hk_pos hu_flip hk_flip
    (layerSymmetricTransferOrthogonalSpectralData u k hk) top theta
    theta_nonneg theta_lt_one partitionPrefactor_small subdominant_abs_le
    dominant_column_pos dominant_eigenspace_simple

/-- Spin-observable constructor using a positive dominant column.  The
one-dimensional dominant eigenspace is derived from positivity of the balanced
transfer matrix, so callers do not need to supply it separately. -/
noncomputable def
    layerBalancedMinSpectralGapCertificate_of_orthogonalDominantBounds_positiveColumnFlipSpin
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (top : LayerState S) (scale theta : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (partitionPrefactor_small :
      (((Fintype.card (LayerState S) - 1 : ℕ) : ℝ) * theta) < 1)
    (dominant_eigenvalue : E.eigenvalue top = scale)
    (subdominant_abs_le : ∀ i, i ≠ top → |E.eigenvalue i| ≤ theta * scale)
    (dominant_column_pos : VectorPositive (fun ω => E.changeOfBasis ω top)) :
    LayerBalancedMinSpectralGapCertificate u k (layerSpinAt x) := by
  letI : Nonempty (LayerState S) := ⟨top⟩
  exact
    layerBalancedMinSpectralGapCertificate_of_orthogonalDominantBounds_positiveSimpleFlipSpin
      u k x hu_flip hk_flip E top scale theta scale_pos theta_nonneg theta_lt_one
      partitionPrefactor_small dominant_eigenvalue subdominant_abs_le dominant_column_pos
      (fun w hw =>
        E.eigenspace_simple_of_positive_column
          (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos)
          top dominant_column_pos w hw)

/-- Spin-observable constructor with the transfer scale fixed to the positive
top spectral column's eigenvalue.  The simple-eigenspace input is derived from
the positive column. -/
noncomputable def
    layerBalancedMinSpectralGapCertificate_of_orthogonalSubdominantBounds_positiveColumnFlipSpin
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (top : LayerState S) (theta : ℝ)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (partitionPrefactor_small :
      (((Fintype.card (LayerState S) - 1 : ℕ) : ℝ) * theta) < 1)
    (subdominant_abs_le : ∀ i, i ≠ top → |E.eigenvalue i| ≤ theta * E.eigenvalue top)
    (dominant_column_pos : VectorPositive (fun ω => E.changeOfBasis ω top)) :
    LayerBalancedMinSpectralGapCertificate u k (layerSpinAt x) := by
  letI : Nonempty (LayerState S) := ⟨top⟩
  exact
    layerBalancedMinSpectralGapCertificate_of_orthogonalDominantBounds_positiveColumnFlipSpin
      u k x hu hk_pos hu_flip hk_flip E top (E.eigenvalue top) theta
      (E.eigenvalue_pos_of_positive_column
        (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos) top
        dominant_column_pos)
      theta_nonneg theta_lt_one partitionPrefactor_small rfl subdominant_abs_le
      dominant_column_pos

/-- Hermitian spin-observable constructor using a positive dominant column.
The one-dimensional dominant eigenspace is derived from positivity. -/
noncomputable def
    layerBalancedMinSpectralGapCertificate_of_layerHermitianDominantBounds_positiveColumnFlipSpin
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (hk : ∀ a b, k a b = k b a)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (top : LayerState S) (scale theta : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (partitionPrefactor_small :
      (((Fintype.card (LayerState S) - 1 : ℕ) : ℝ) * theta) < 1)
    (dominant_eigenvalue :
      (layerSymmetricTransferOrthogonalSpectralData u k hk).eigenvalue top = scale)
    (subdominant_abs_le : ∀ i, i ≠ top →
      |(layerSymmetricTransferOrthogonalSpectralData u k hk).eigenvalue i|
        ≤ theta * scale)
    (dominant_column_pos :
      VectorPositive
        (fun ω =>
          (layerSymmetricTransferOrthogonalSpectralData u k hk).changeOfBasis ω top)) :
    LayerBalancedMinSpectralGapCertificate u k (layerSpinAt x) :=
  layerBalancedMinSpectralGapCertificate_of_orthogonalDominantBounds_positiveColumnFlipSpin
    u k x hu hk_pos hu_flip hk_flip
    (layerSymmetricTransferOrthogonalSpectralData u k hk) top scale theta
    scale_pos theta_nonneg theta_lt_one partitionPrefactor_small
    dominant_eigenvalue subdominant_abs_le dominant_column_pos

/-- Hermitian spin-observable constructor with the transfer scale fixed to the
positive top spectral column's eigenvalue.  The simple-eigenspace input is
derived from the positive column. -/
noncomputable def
    layerBalancedMinSpectralGapCertificate_of_layerHermitianSubdominantBounds_positiveColumnFlipSpin
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (hk : ∀ a b, k a b = k b a)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (top : LayerState S) (theta : ℝ)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (partitionPrefactor_small :
      (((Fintype.card (LayerState S) - 1 : ℕ) : ℝ) * theta) < 1)
    (subdominant_abs_le : ∀ i, i ≠ top →
      |(layerSymmetricTransferOrthogonalSpectralData u k hk).eigenvalue i|
        ≤ theta * (layerSymmetricTransferOrthogonalSpectralData u k hk).eigenvalue top)
    (dominant_column_pos :
      VectorPositive
        (fun ω =>
          (layerSymmetricTransferOrthogonalSpectralData u k hk).changeOfBasis ω top)) :
    LayerBalancedMinSpectralGapCertificate u k (layerSpinAt x) :=
  layerBalancedMinSpectralGapCertificate_of_orthogonalSubdominantBounds_positiveColumnFlipSpin
    u k x hu hk_pos hu_flip hk_flip
    (layerSymmetricTransferOrthogonalSpectralData u k hk) top theta
    theta_nonneg theta_lt_one partitionPrefactor_small subdominant_abs_le
    dominant_column_pos

end TransferMatrix

end IsingModel

import IsingModel.TransferMatrix.LayerPerron
import IsingModel.TransferMatrix.LayerPerronExistence.LayerWrappers

/-!
# Signed-positive spin-observable certificate constructors (GJ §17.1)

The flip-even cancellation of a signed-positive balanced-layer spectral column
under a global spin flip, and the spin-observable minimal-spectral-gap
certificate constructors that use a signed-positive dominant column.  Part of
the `LayerPerronExistence` signed-positive dominant column split.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.1, pp. 304--306.
-/

namespace IsingModel

namespace TransferMatrix

open Matrix

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-! ## Signed-positive spin-observable certificate constructors -/

/-- A signed-positive spectral column of a balanced layer transfer matrix is
flip-even when the layer weights and transition weights are invariant under
global spin flip. -/
theorem layerSymmetricTransfer_signedPositiveColumn_flip_even
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (top : LayerState S) (hpos : E.SignedPositiveColumn top) :
    ∀ ω : LayerState S,
      E.changeOfBasis (layerStateFlipEquiv S ω) top = E.changeOfBasis ω top := by
  letI : Nonempty (LayerState S) := ⟨top⟩
  let v : LayerState S → ℝ := fun ω => hpos.sign * E.changeOfBasis ω top
  have hveig :
      (layerSymmetricTransferMatrix u k).mulVec v = E.eigenvalue top • v :=
    hpos.mulVec_signedColumn
  have hsimple :
      ∀ w : LayerState S → ℝ,
        (layerSymmetricTransferMatrix u k).mulVec w = E.eigenvalue top • w →
          ∃ c : ℝ, w = c • v := by
    intro w hw
    exact eigenvector_smul_of_entrywisePositive_positive_eigenpair
      (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos)
      hpos.strictPositiveRightEigenpair hw
  have hsigned_even :
      ∀ ω : LayerState S,
        v (layerStateFlipEquiv S ω) = v ω :=
    vectorPositive_eigenvector_flip_even_of_simple_eigenspace
      (layerStateFlipEquiv S)
      (fun ω => layerStateFlipEquiv_involutive S ω)
      hpos.positive hveig
      (layerSymmetricTransferMatrix_mulVec_comp_equiv u k (layerStateFlipEquiv S)
        hu_flip hk_flip)
      hsimple
  intro ω
  exact mul_left_cancel₀ hpos.sign_ne_zero (hsigned_even ω)

/-- Spin-observable constructor using a signed-positive dominant column.  The
flip-even marked-channel cancellation is derived after orienting the spectral
column by its sign. -/
noncomputable def
    layerBalancedMinSpectralGapCertificate_of_orthogonalDominantBounds_signedPositiveColumnFlipSpin
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
    (dominant_column_signed_pos : E.SignedPositiveColumn top) :
    LayerBalancedMinSpectralGapCertificate u k (layerSpinAt x) :=
  layerBalancedMinSpectralGapCertificate_of_orthogonalDominantBounds_flipEvenSpin
    u k x E top scale theta scale_pos theta_nonneg theta_lt_one
    partitionPrefactor_small dominant_eigenvalue subdominant_abs_le
    (layerSymmetricTransfer_signedPositiveColumn_flip_even
      u k hu hk_pos hu_flip hk_flip E top dominant_column_signed_pos)

/-- Spin-observable constructor using a signed-positive dominant column with
the transfer scale fixed to that column's eigenvalue. -/
noncomputable def
layerBalancedMinSpectralGapCertificate_of_orthogonalSubdominantBounds_signedPositiveColumnFlipSpin
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
    (subdominant_abs_le :
      ∀ i, i ≠ top → |E.eigenvalue i| ≤ theta * E.eigenvalue top)
    (dominant_column_signed_pos : E.SignedPositiveColumn top) :
    LayerBalancedMinSpectralGapCertificate u k (layerSpinAt x) := by
  letI : Nonempty (LayerState S) := ⟨top⟩
  exact
    layerBalancedMinSpectralGapCertificate_of_orthogonalDominantBounds_signedPositiveColumnFlipSpin
      u k x hu hk_pos hu_flip hk_flip E top (E.eigenvalue top) theta
      (E.eigenvalue_pos_of_signedPositiveColumn
        (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos) top
        dominant_column_signed_pos)
      theta_nonneg theta_lt_one partitionPrefactor_small rfl subdominant_abs_le
      dominant_column_signed_pos

end TransferMatrix

end IsingModel

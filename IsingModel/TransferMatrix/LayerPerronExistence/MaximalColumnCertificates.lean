import IsingModel.TransferMatrix.LayerPerron
import IsingModel.TransferMatrix.LayerPerronExistence.SpinObservableCertificates

/-!
# Maximal-column certificate constructors (GJ §17.1)

The minimal-spectral-gap certificate constructors driven by the maximal
signed-positive spectral column, in orthogonal and Hermitian forms, with the
finite prefactor smallness condition discharged by a one-element state space, an
inverse-cardinality ratio bound, or the one-site transverse-layer case.  Part of
the `LayerPerronExistence` signed-positive dominant column split.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.1, pp. 304--306.
-/

namespace IsingModel

namespace TransferMatrix

open Matrix

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-! ## Maximal-column certificate constructors -/

/-- Orthogonal spectral-data constructor with the transfer scale and
subdominant ratio fixed by the maximal signed-positive spectral column.

The finite prefactor condition
`((Fintype.card Ω - 1) * theta) < 1` remains an explicit quantitative input. -/
noncomputable def layerBalancedMinSpectralGapCertificate_of_orthogonalMaxEigenIndex
    [Nonempty Ω]
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (hu : ∀ a, 0 < u a) (hk_pos : ∀ a b, 0 < k a b)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (partitionPrefactor_small :
      (((Fintype.card Ω - 1 : ℕ) : ℝ) *
        E.subdominantRatio_maxEigenIndex
          (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos)) < 1)
    (dominant_markedDiagonal_zero :
      E.markedMatrix f E.maxEigenIndex E.maxEigenIndex = 0) :
    LayerBalancedMinSpectralGapCertificate u k f := by
  let hM := layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos
  exact layerBalancedMinSpectralGapCertificate_of_orthogonalDominantBounds
    u k f E E.maxEigenIndex (E.eigenvalue E.maxEigenIndex)
    (E.subdominantRatio_maxEigenIndex hM)
    (E.eigenvalue_pos_maxEigenIndex hM)
    (E.subdominantRatio_maxEigenIndex_nonneg hM)
    (E.subdominantRatio_maxEigenIndex_lt_one hM)
    partitionPrefactor_small rfl
    (E.eigenvalue_abs_le_subdominantRatio_maxEigenIndex hM)
    dominant_markedDiagonal_zero

/-- Hermitian spectral-data constructor with the transfer scale and
subdominant ratio fixed by the maximal signed-positive spectral column. -/
noncomputable def layerBalancedMinSpectralGapCertificate_of_layerHermitianMaxEigenIndex
    [Nonempty Ω]
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (hu : ∀ a, 0 < u a) (hk_pos : ∀ a b, 0 < k a b)
    (hk : ∀ a b, k a b = k b a)
    (partitionPrefactor_small :
      (((Fintype.card Ω - 1 : ℕ) : ℝ) *
        (layerSymmetricTransferOrthogonalSpectralData u k hk).subdominantRatio_maxEigenIndex
          (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos)) < 1)
    (dominant_markedDiagonal_zero :
      (layerSymmetricTransferOrthogonalSpectralData u k hk).markedMatrix f
        (layerSymmetricTransferOrthogonalSpectralData u k hk).maxEigenIndex
        (layerSymmetricTransferOrthogonalSpectralData u k hk).maxEigenIndex = 0) :
    LayerBalancedMinSpectralGapCertificate u k f :=
  layerBalancedMinSpectralGapCertificate_of_orthogonalMaxEigenIndex u k f hu hk_pos
    (layerSymmetricTransferOrthogonalSpectralData u k hk)
    partitionPrefactor_small dominant_markedDiagonal_zero

/-- Orthogonal max-index certificate whose finite prefactor smallness is
discharged by a one-element state space. -/
noncomputable def layerBalancedMinSpectralGapCertificate_of_orthogonalMaxEigenIndex_cardOne
    [Nonempty Ω]
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (hu : ∀ a, 0 < u a) (hk_pos : ∀ a b, 0 < k a b)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (hcard : Fintype.card Ω = 1)
    (dominant_markedDiagonal_zero :
      E.markedMatrix f E.maxEigenIndex E.maxEigenIndex = 0) :
    LayerBalancedMinSpectralGapCertificate u k f :=
  layerBalancedMinSpectralGapCertificate_of_orthogonalMaxEigenIndex u k f hu hk_pos E
    (finiteSpectralPartitionPrefactor_small_of_card_eq_one Ω hcard)
    dominant_markedDiagonal_zero

/-- Orthogonal max-index certificate whose finite prefactor smallness is
discharged by an inverse-cardinality bound on the canonical subdominant
ratio. -/
noncomputable def
    layerBalancedMinSpectralGapCertificate_of_orthogonalMaxEigenIndex_ratioSmall
    [Nonempty Ω]
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (hu : ∀ a, 0 < u a) (hk_pos : ∀ a b, 0 < k a b)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (hcard : 1 < Fintype.card Ω)
    (hratio :
      E.subdominantRatio_maxEigenIndex
          (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos)
        < (((Fintype.card Ω - 1 : ℕ) : ℝ))⁻¹)
    (dominant_markedDiagonal_zero :
      E.markedMatrix f E.maxEigenIndex E.maxEigenIndex = 0) :
    LayerBalancedMinSpectralGapCertificate u k f :=
  layerBalancedMinSpectralGapCertificate_of_orthogonalMaxEigenIndex u k f hu hk_pos E
    (finiteSpectralPartitionPrefactor_small_of_lt_inv_cardSubOne Ω hcard hratio)
    dominant_markedDiagonal_zero

/-- Hermitian max-index certificate whose finite prefactor smallness is
discharged by a one-element state space. -/
noncomputable def layerBalancedMinSpectralGapCertificate_of_layerHermitianMaxEigenIndex_cardOne
    [Nonempty Ω]
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (hu : ∀ a, 0 < u a) (hk_pos : ∀ a b, 0 < k a b)
    (hk : ∀ a b, k a b = k b a)
    (hcard : Fintype.card Ω = 1)
    (dominant_markedDiagonal_zero :
      (layerSymmetricTransferOrthogonalSpectralData u k hk).markedMatrix f
        (layerSymmetricTransferOrthogonalSpectralData u k hk).maxEigenIndex
        (layerSymmetricTransferOrthogonalSpectralData u k hk).maxEigenIndex = 0) :
    LayerBalancedMinSpectralGapCertificate u k f :=
  layerBalancedMinSpectralGapCertificate_of_layerHermitianMaxEigenIndex
    u k f hu hk_pos hk
    (finiteSpectralPartitionPrefactor_small_of_card_eq_one Ω hcard)
    dominant_markedDiagonal_zero

/-- Hermitian max-index certificate whose finite prefactor smallness is
discharged by an inverse-cardinality bound on the canonical subdominant
ratio. -/
noncomputable def
    layerBalancedMinSpectralGapCertificate_of_layerHermitianMaxEigenIndex_ratioSmall
    [Nonempty Ω]
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (hu : ∀ a, 0 < u a) (hk_pos : ∀ a b, 0 < k a b)
    (hk : ∀ a b, k a b = k b a)
    (hcard : 1 < Fintype.card Ω)
    (hratio :
      (layerSymmetricTransferOrthogonalSpectralData u k hk).subdominantRatio_maxEigenIndex
          (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos)
        < (((Fintype.card Ω - 1 : ℕ) : ℝ))⁻¹)
    (dominant_markedDiagonal_zero :
      (layerSymmetricTransferOrthogonalSpectralData u k hk).markedMatrix f
        (layerSymmetricTransferOrthogonalSpectralData u k hk).maxEigenIndex
        (layerSymmetricTransferOrthogonalSpectralData u k hk).maxEigenIndex = 0) :
    LayerBalancedMinSpectralGapCertificate u k f :=
  layerBalancedMinSpectralGapCertificate_of_layerHermitianMaxEigenIndex
    u k f hu hk_pos hk
    (finiteSpectralPartitionPrefactor_small_of_lt_inv_cardSubOne Ω hcard hratio)
    dominant_markedDiagonal_zero

/-- Spin-observable constructor using the maximal signed-positive spectral
column.  The signed-positive column gives flip-even dominant-channel
cancellation before entering the min-separation certificate route. -/
noncomputable def
    layerBalancedMinSpectralGapCertificate_of_orthogonalMaxEigenIndexFlipSpin
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (partitionPrefactor_small :
      (((Fintype.card (LayerState S) - 1 : ℕ) : ℝ) *
        E.subdominantRatio_maxEigenIndex
          (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos)) < 1) :
    LayerBalancedMinSpectralGapCertificate u k (layerSpinAt x) := by
  letI : Nonempty (LayerState S) := ⟨default⟩
  let hM := layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos
  exact
    layerBalancedMinSpectralGapCertificate_of_orthogonalDominantBounds_signedPositiveColumnFlipSpin
      u k x hu hk_pos hu_flip hk_flip E E.maxEigenIndex
      (E.eigenvalue E.maxEigenIndex)
      (E.subdominantRatio_maxEigenIndex hM)
      (E.eigenvalue_pos_maxEigenIndex hM)
      (E.subdominantRatio_maxEigenIndex_nonneg hM)
      (E.subdominantRatio_maxEigenIndex_lt_one hM)
      partitionPrefactor_small rfl
      (E.eigenvalue_abs_le_subdominantRatio_maxEigenIndex hM)
      (E.signedPositiveColumn_maxEigenIndex hM)

/-- Hermitian spin-observable constructor using the maximal signed-positive
spectral column of the balanced layer transfer matrix. -/
noncomputable def
    layerBalancedMinSpectralGapCertificate_of_layerHermitianMaxEigenIndexFlipSpin
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (hk : ∀ ω η, k ω η = k η ω)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (partitionPrefactor_small :
      (((Fintype.card (LayerState S) - 1 : ℕ) : ℝ) *
        layerSymmetricTransfer_subdominantRatio_maxEigenIndex u k hu hk_pos hk) < 1) :
    LayerBalancedMinSpectralGapCertificate u k (layerSpinAt x) := by
  letI : Nonempty (LayerState S) := ⟨default⟩
  let E := layerSymmetricTransferOrthogonalSpectralData u k hk
  exact
    layerBalancedMinSpectralGapCertificate_of_orthogonalMaxEigenIndexFlipSpin
      u k x hu hk_pos hu_flip hk_flip E
      (by
        simpa [layerSymmetricTransfer_subdominantRatio_maxEigenIndex, E] using
          partitionPrefactor_small)

/-- Orthogonal max-index spin certificate whose finite prefactor smallness is
discharged by a one-element layer-state space. -/
noncomputable def
    layerBalancedMinSpectralGapCertificate_of_orthogonalMaxEigenIndexFlipSpin_cardOne
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (hcard : Fintype.card (LayerState S) = 1) :
    LayerBalancedMinSpectralGapCertificate u k (layerSpinAt x) :=
  layerBalancedMinSpectralGapCertificate_of_orthogonalMaxEigenIndexFlipSpin
    u k x hu hk_pos hu_flip hk_flip E
    (finiteSpectralPartitionPrefactor_small_of_card_eq_one (LayerState S) hcard)

/-- Orthogonal max-index spin certificate whose finite prefactor smallness is
discharged by an inverse-cardinality bound on the canonical subdominant
ratio. -/
noncomputable def
    layerBalancedMinSpectralGapCertificate_of_orthogonalMaxEigenIndexFlipSpin_ratioSmall
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (hcard : 1 < Fintype.card (LayerState S))
    (hratio :
      E.subdominantRatio_maxEigenIndex
          (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos)
        < (((Fintype.card (LayerState S) - 1 : ℕ) : ℝ))⁻¹) :
    LayerBalancedMinSpectralGapCertificate u k (layerSpinAt x) :=
  layerBalancedMinSpectralGapCertificate_of_orthogonalMaxEigenIndexFlipSpin
    u k x hu hk_pos hu_flip hk_flip E
    (finiteSpectralPartitionPrefactor_small_of_lt_inv_cardSubOne
      (LayerState S) hcard hratio)

/-- Orthogonal max-index spin certificate for a one-site transverse layer.  In
this two-state layer case, the already proved strict canonical ratio `< 1`
discharges the finite prefactor smallness condition. -/
noncomputable def
    layerBalancedMinSpectralGapCertificate_of_orthogonalMaxEigenIndexFlipSpin_oneSite
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (hcard : Fintype.card S = 1) :
    LayerBalancedMinSpectralGapCertificate u k (layerSpinAt x) := by
  letI : Nonempty (LayerState S) := ⟨default⟩
  let hM := layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos
  exact
    layerBalancedMinSpectralGapCertificate_of_orthogonalMaxEigenIndexFlipSpin
      u k x hu hk_pos hu_flip hk_flip E
      (finiteSpectralPartitionPrefactor_small_of_layerState_card_eq_one S hcard
        (E.subdominantRatio_maxEigenIndex_lt_one hM))

/-- Hermitian max-index spin certificate whose finite prefactor smallness is
discharged by a one-element layer-state space. -/
noncomputable def
    layerBalancedMinSpectralGapCertificate_of_layerHermitianMaxEigenIndexFlipSpin_cardOne
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (hk : ∀ ω η, k ω η = k η ω)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (hcard : Fintype.card (LayerState S) = 1) :
    LayerBalancedMinSpectralGapCertificate u k (layerSpinAt x) :=
  layerBalancedMinSpectralGapCertificate_of_layerHermitianMaxEigenIndexFlipSpin
    u k x hu hk_pos hk hu_flip hk_flip
    (finiteSpectralPartitionPrefactor_small_of_card_eq_one (LayerState S) hcard)

/-- Hermitian max-index spin certificate whose finite prefactor smallness is
discharged by an inverse-cardinality bound on the canonical subdominant
ratio. -/
noncomputable def
    layerBalancedMinSpectralGapCertificate_of_layerHermitianMaxEigenIndexFlipSpin_ratioSmall
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (hk : ∀ ω η, k ω η = k η ω)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (hcard : 1 < Fintype.card (LayerState S))
    (hratio :
      layerSymmetricTransfer_subdominantRatio_maxEigenIndex u k hu hk_pos hk
        < (((Fintype.card (LayerState S) - 1 : ℕ) : ℝ))⁻¹) :
    LayerBalancedMinSpectralGapCertificate u k (layerSpinAt x) :=
  layerBalancedMinSpectralGapCertificate_of_layerHermitianMaxEigenIndexFlipSpin
    u k x hu hk_pos hk hu_flip hk_flip
    (finiteSpectralPartitionPrefactor_small_of_lt_inv_cardSubOne
      (LayerState S) hcard hratio)

/-- Hermitian max-index spin certificate for a one-site transverse layer.  In
this two-state layer case, the already proved strict canonical ratio `< 1`
discharges the finite prefactor smallness condition. -/
noncomputable def
    layerBalancedMinSpectralGapCertificate_of_layerHermitianMaxEigenIndexFlipSpin_oneSite
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (hk : ∀ ω η, k ω η = k η ω)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (hcard : Fintype.card S = 1) :
    LayerBalancedMinSpectralGapCertificate u k (layerSpinAt x) :=
  layerBalancedMinSpectralGapCertificate_of_layerHermitianMaxEigenIndexFlipSpin
    u k x hu hk_pos hk hu_flip hk_flip
    (finiteSpectralPartitionPrefactor_small_of_layerState_card_eq_one S hcard
      (layerSymmetricTransfer_subdominantRatio_maxEigenIndex_lt_one
        u k hu hk_pos hk))

end TransferMatrix

end IsingModel

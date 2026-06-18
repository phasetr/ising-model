import IsingModel.TransferMatrix.LayerPerronExistence

/-!
# Layer-cardinality small-ratio bridges

This file exposes the finite prefactor smallness threshold for finite transverse
layer states in terms of the transverse cardinality.  Since
`LayerState S = Config S`, the state space has cardinality `2 ^ Fintype.card S`.
For a nonempty transverse layer, the existing inverse-cardinality condition can
therefore be read as

`theta < ((2 ^ Fintype.card S - 1 : ℕ) : ℝ)⁻¹`.

This is only a cardinality-expansion bridge.  It does not prove a physical
small-ratio estimate for any concrete layer model, does not make `theta < 1`
sufficient for larger layer state spaces, and does not address open slabs,
thermodynamic limits, or final hyperplane exponential decay.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

/-! ## Cardinality-expanded finite prefactor smallness -/

/-- A nonempty transverse layer has a nontrivial layer-state space:
`|LayerState S| = 2 ^ |S| > 1`. -/
theorem layerState_card_nontrivial_of_nonempty (S : Type*) [Fintype S] [DecidableEq S]
    [Nonempty S] :
    1 < Fintype.card (LayerState S) := by
  rw [layerState_card_eq_two_pow S]
  have hcard_pos : 0 < Fintype.card S := Fintype.card_pos_iff.mpr inferInstance
  exact Nat.one_lt_pow (Nat.ne_of_gt hcard_pos) one_lt_two

/-- For a nonempty transverse layer, the finite prefactor smallness condition
follows from the inverse of the expanded layer-state cardinality `2 ^ |S| - 1`.

This is only a rewriting of the existing inverse-cardinality bridge using
`Fintype.card (LayerState S) = 2 ^ Fintype.card S`; it does not prove the
subdominant ratio bound itself. -/
theorem finiteSpectralPartitionPrefactor_small_of_layerState_lt_inv_two_pow_cardSubOne
    (S : Type*) [Fintype S] [DecidableEq S] [Nonempty S] {theta : ℝ}
    (htheta : theta < (((2 ^ Fintype.card S - 1 : ℕ) : ℝ))⁻¹) :
    (((Fintype.card (LayerState S) - 1 : ℕ) : ℝ) * theta) < 1 := by
  refine finiteSpectralPartitionPrefactor_small_of_lt_inv_cardSubOne
    (LayerState S) (layerState_card_nontrivial_of_nonempty S) ?_
  simpa [layerState_card_eq_two_pow S] using htheta

/-! ## Max-index spin certificate wrappers -/

/-- Orthogonal max-index spin certificate whose finite prefactor smallness is
discharged by an inverse-cardinality bound written with the transverse layer
cardinality `2 ^ |S|`. -/
noncomputable def
    layerBalancedMinSpectralGapCertificate_of_orthogonalMaxEigenIndexFlipSpin_layerCardinalitySmall
    {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (hratio :
      E.subdominantRatio_maxEigenIndex
          (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos)
        < (((2 ^ Fintype.card S - 1 : ℕ) : ℝ))⁻¹) :
    LayerBalancedMinSpectralGapCertificate u k (layerSpinAt x) :=
  layerBalancedMinSpectralGapCertificate_of_orthogonalMaxEigenIndexFlipSpin
    u k x hu hk_pos hu_flip hk_flip E
    (finiteSpectralPartitionPrefactor_small_of_layerState_lt_inv_two_pow_cardSubOne
      S hratio)

/-- Hermitian max-index spin certificate whose finite prefactor smallness is
discharged by an inverse-cardinality bound written with the transverse layer
cardinality `2 ^ |S|`. -/
noncomputable def
    layerBalancedMinSpectralGapCertificate_of_layerHermitianMaxEigenIndexFlipSpin_layerCardSmall
    {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (hk : ∀ ω η, k ω η = k η ω)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (hratio :
      layerSymmetricTransfer_subdominantRatio_maxEigenIndex u k hu hk_pos hk
        < (((2 ^ Fintype.card S - 1 : ℕ) : ℝ))⁻¹) :
    LayerBalancedMinSpectralGapCertificate u k (layerSpinAt x) :=
  layerBalancedMinSpectralGapCertificate_of_layerHermitianMaxEigenIndexFlipSpin
    u k x hu hk_pos hk hu_flip hk_flip
    (finiteSpectralPartitionPrefactor_small_of_layerState_lt_inv_two_pow_cardSubOne
      S hratio)

end TransferMatrix

end IsingModel

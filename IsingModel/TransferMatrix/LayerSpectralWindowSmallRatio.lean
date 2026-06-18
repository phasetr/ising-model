import IsingModel.TransferMatrix.CubicLayerCardinalitySmallRatio

/-!
# Layer spectral-window small-ratio bridges

This file gives a small-ratio entry point that does not depend on the canonical
subdominant ratio chosen by `Classical.choose`.  Instead, a later physical or
explicit spectral calculation may provide a concrete number `theta` and prove
that every non-maximal eigenvalue is bounded by
`theta * E.eigenvalue E.maxEigenIndex`.  If this same `theta` satisfies the
inverse layer-cardinality threshold, the existing balanced min-gap certificate
route applies.

This is a bridge for explicit spectral-window estimates.  It does not prove a
physical estimate for the full cubic layer, does not make `theta < 1` sufficient
for multi-site transverse layers, and does not address open slabs,
thermodynamic limits, or final hyperplane exponential decay.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

/-! ## Arithmetic for layer-cardinality spectral windows -/

/-- The expanded inverse-cardinality threshold for a nonempty transverse layer
is at most one. -/
theorem inv_two_pow_cardSubOne_le_one_of_nonempty
    (S : Type*) [Fintype S] [Nonempty S] :
    (((2 ^ Fintype.card S - 1 : ℕ) : ℝ))⁻¹ ≤ 1 := by
  have hcard_pos : 0 < Fintype.card S := Fintype.card_pos_iff.mpr inferInstance
  have hpow : 1 < 2 ^ Fintype.card S :=
    Nat.one_lt_pow (Nat.ne_of_gt hcard_pos) one_lt_two
  have hden_nat : 1 ≤ 2 ^ Fintype.card S - 1 := by omega
  have hden : (1 : ℝ) ≤ ((2 ^ Fintype.card S - 1 : ℕ) : ℝ) := by
    exact_mod_cast hden_nat
  exact inv_le_one_of_one_le₀ hden

/-- The expanded inverse-cardinality threshold implies the ordinary strict
`theta < 1` bound, but only as a consequence of the stronger threshold. -/
theorem lt_one_of_lt_inv_two_pow_cardSubOne
    (S : Type*) [Fintype S] [Nonempty S] {theta : ℝ}
    (htheta : theta < (((2 ^ Fintype.card S - 1 : ℕ) : ℝ))⁻¹) :
    theta < 1 :=
  lt_of_lt_of_le htheta (inv_two_pow_cardSubOne_le_one_of_nonempty S)

/-- The cubic transverse-box inverse-cardinality threshold is at most one. -/
theorem inv_cubicLayerSite_cardSubOne_le_one (d R : ℕ) :
    (((2 ^ ((2 * R + 1) ^ d) - 1 : ℕ) : ℝ))⁻¹ ≤ 1 := by
  letI : Nonempty (CubicLayerSite d R) := cubicLayerSite_nonempty d R
  simpa [cubicLayerSite_card d R] using
    inv_two_pow_cardSubOne_le_one_of_nonempty (CubicLayerSite d R)

/-- The cubic transverse-box inverse-cardinality threshold implies
`theta < 1`, again only as a consequence of the stronger threshold. -/
theorem lt_one_of_lt_inv_cubicLayerSite_cardSubOne
    (d R : ℕ) {theta : ℝ}
    (htheta : theta < (((2 ^ ((2 * R + 1) ^ d) - 1 : ℕ) : ℝ))⁻¹) :
    theta < 1 :=
  lt_of_lt_of_le htheta (inv_cubicLayerSite_cardSubOne_le_one d R)

/-! ## Layer-cardinality spectral-window certificates -/

/-- Orthogonal max-index spin certificate from an explicit spectral window.

The input `theta` bounds every non-maximal spectral eigenvalue, and the stronger
inverse-cardinality hypothesis on `theta` discharges the finite partition
prefactor.  This avoids relying on the canonical chosen subdominant ratio. -/
noncomputable def
    layerBalancedMinGapCert_orthogonal_spectralWindow_layerCardSmall
    {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (theta : ℝ)
    (theta_nonneg : 0 ≤ theta)
    (htheta : theta < (((2 ^ Fintype.card S - 1 : ℕ) : ℝ))⁻¹)
    (subdominant_abs_le :
      ∀ i, i ≠ E.maxEigenIndex →
        |E.eigenvalue i| ≤ theta * E.eigenvalue E.maxEigenIndex) :
    LayerBalancedMinSpectralGapCertificate u k (layerSpinAt x) := by
  let hM := layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos
  exact
  layerBalancedMinSpectralGapCertificate_of_orthogonalSubdominantBounds_signedPositiveColumnFlipSpin
      u k x hu hk_pos hu_flip hk_flip E E.maxEigenIndex theta theta_nonneg
      (lt_one_of_lt_inv_two_pow_cardSubOne S htheta)
      (finiteSpectralPartitionPrefactor_small_of_layerState_lt_inv_two_pow_cardSubOne
        S htheta)
      subdominant_abs_le (E.signedPositiveColumn_maxEigenIndex hM)

/-- Hermitian max-index spin certificate from an explicit spectral window for
the Hermitian spectral data of the balanced layer transfer matrix. -/
noncomputable def
    layerBalancedMinGapCert_hermitian_spectralWindow_layerCardSmall
    {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (hk : ∀ ω η, k ω η = k η ω)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (theta : ℝ)
    (theta_nonneg : 0 ≤ theta)
    (htheta : theta < (((2 ^ Fintype.card S - 1 : ℕ) : ℝ))⁻¹)
    (subdominant_abs_le :
      ∀ i, i ≠ (layerSymmetricTransferOrthogonalSpectralData u k hk).maxEigenIndex →
        |(layerSymmetricTransferOrthogonalSpectralData u k hk).eigenvalue i| ≤
          theta * (layerSymmetricTransferOrthogonalSpectralData u k hk).eigenvalue
            (layerSymmetricTransferOrthogonalSpectralData u k hk).maxEigenIndex) :
    LayerBalancedMinSpectralGapCertificate u k (layerSpinAt x) := by
  let E := layerSymmetricTransferOrthogonalSpectralData u k hk
  exact
    layerBalancedMinGapCert_orthogonal_spectralWindow_layerCardSmall
      u k x hu hk_pos hu_flip hk_flip E theta theta_nonneg htheta
      (by
        simpa [E] using subdominant_abs_le)

/-! ## Cubic spectral-window certificates -/

/-- Orthogonal spectral-window spin certificate for cubic transverse boxes.

The theorem consumes a concrete eigenvalue window `theta` for the cubic
balanced transfer matrix and the explicit cubic inverse-cardinality threshold.
It does not prove that the physical cubic layer supplies such a `theta`. -/
noncomputable def cubicLayerBalancedMinGapCertificate_orthogonal_spectralWindow
    (d R : ℕ) (p : IsingParams ℝ) (x : CubicLayerSite d R)
    (hp : p.h = 0)
    (E : RealOrthogonalSpectralData
      (layerSymmetricTransferMatrix
        (layerInternalWeight (cubicLayerGraph d R) p)
        (layerTransitionWeight (cubicLayerTransitionPairs d R) p)))
    (theta : ℝ)
    (theta_nonneg : 0 ≤ theta)
    (htheta : theta < (((2 ^ ((2 * R + 1) ^ d) - 1 : ℕ) : ℝ))⁻¹)
    (subdominant_abs_le :
      ∀ i, i ≠ E.maxEigenIndex →
        |E.eigenvalue i| ≤ theta * E.eigenvalue E.maxEigenIndex) :
    LayerBalancedMinSpectralGapCertificate
      (layerInternalWeight (cubicLayerGraph d R) p)
      (layerTransitionWeight (cubicLayerTransitionPairs d R) p)
      (layerSpinAt x) := by
  letI : Nonempty (CubicLayerSite d R) := cubicLayerSite_nonempty d R
  refine
    layerBalancedMinGapCert_orthogonal_spectralWindow_layerCardSmall
      (layerInternalWeight (cubicLayerGraph d R) p)
      (layerTransitionWeight (cubicLayerTransitionPairs d R) p)
      x
      (cubicLayerInternalWeight_pos d R p)
      (cubicLayerTransitionWeight_pos d R p)
      ?_ ?_ E theta theta_nonneg ?_ subdominant_abs_le
  · exact layerInternalWeight_flip_of_h_zero (cubicLayerGraph d R) p hp
  · exact layerTransitionWeight_flip_flip (cubicLayerTransitionPairs d R) p
  · rw [← cubicLayerSite_card d R] at htheta
    exact htheta

/-- Hermitian spectral-window spin certificate for cubic transverse boxes.

The explicit spectral window is stated for the Hermitian spectral data attached
to the cubic balanced transfer matrix. -/
noncomputable def cubicLayerBalancedMinGapCertificate_hermitian_spectralWindow
    (d R : ℕ) (p : IsingParams ℝ) (x : CubicLayerSite d R)
    (hp : p.h = 0)
    (theta : ℝ)
    (theta_nonneg : 0 ≤ theta)
    (htheta : theta < (((2 ^ ((2 * R + 1) ^ d) - 1 : ℕ) : ℝ))⁻¹)
    (subdominant_abs_le :
      ∀ i,
        i ≠
            (layerSymmetricTransferOrthogonalSpectralData
              (layerInternalWeight (cubicLayerGraph d R) p)
              (layerTransitionWeight (cubicLayerTransitionPairs d R) p)
              (cubicLayerTransitionWeight_symm d R p)).maxEigenIndex →
          |(layerSymmetricTransferOrthogonalSpectralData
              (layerInternalWeight (cubicLayerGraph d R) p)
              (layerTransitionWeight (cubicLayerTransitionPairs d R) p)
              (cubicLayerTransitionWeight_symm d R p)).eigenvalue i| ≤
            theta *
              (layerSymmetricTransferOrthogonalSpectralData
                (layerInternalWeight (cubicLayerGraph d R) p)
                (layerTransitionWeight (cubicLayerTransitionPairs d R) p)
                (cubicLayerTransitionWeight_symm d R p)).eigenvalue
                (layerSymmetricTransferOrthogonalSpectralData
                  (layerInternalWeight (cubicLayerGraph d R) p)
                  (layerTransitionWeight (cubicLayerTransitionPairs d R) p)
                  (cubicLayerTransitionWeight_symm d R p)).maxEigenIndex) :
    LayerBalancedMinSpectralGapCertificate
      (layerInternalWeight (cubicLayerGraph d R) p)
      (layerTransitionWeight (cubicLayerTransitionPairs d R) p)
      (layerSpinAt x) := by
  letI : Nonempty (CubicLayerSite d R) := cubicLayerSite_nonempty d R
  refine
    layerBalancedMinGapCert_hermitian_spectralWindow_layerCardSmall
      (layerInternalWeight (cubicLayerGraph d R) p)
      (layerTransitionWeight (cubicLayerTransitionPairs d R) p)
      x
      (cubicLayerInternalWeight_pos d R p)
      (cubicLayerTransitionWeight_pos d R p)
      (cubicLayerTransitionWeight_symm d R p)
      ?_ ?_ theta theta_nonneg ?_ ?_
  · exact layerInternalWeight_flip_of_h_zero (cubicLayerGraph d R) p hp
  · exact layerTransitionWeight_flip_flip (cubicLayerTransitionPairs d R) p
  · rw [← cubicLayerSite_card d R] at htheta
    exact htheta
  · exact subdominant_abs_le

end TransferMatrix

end IsingModel

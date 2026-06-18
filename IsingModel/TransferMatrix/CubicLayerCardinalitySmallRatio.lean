import IsingModel.TransferMatrix.CubicLayerCylinder
import IsingModel.TransferMatrix.LayerCardinalitySmallRatio

/-!
# Cubic layer-cardinality small-ratio bridge

This file specialises the layer-cardinality small-ratio bridge to the finite
cubic transverse boxes used by `CubicLayerCylinder.lean`.  The only new
arithmetic input is the cubic-box cardinality
`Fintype.card (CubicLayerSite d R) = (2 * R + 1) ^ d`, which rewrites the
inverse-cardinality sufficient condition as

`theta < ((2 ^ ((2 * R + 1) ^ d) - 1 : ℕ) : ℝ)⁻¹`.

This remains a cardinality-threshold bridge.  It does not prove that the
physical cubic-layer subdominant ratio satisfies this bound, does not make
`theta < 1` sufficient for multi-site transverse layers, and does not address
open slabs, thermodynamic limits, or final hyperplane exponential decay.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

/-! ## Cubic transverse cardinality -/

/-- The transverse cubic layer has cardinality `(2 * R + 1) ^ d`. -/
theorem cubicLayerSite_card (d R : ℕ) :
    Fintype.card (CubicLayerSite d R) = (2 * R + 1) ^ d := by
  rw [CubicLayerSite, Fintype.card_coe]
  exact Ambient.card_cubicBox d R

/-- The transverse cubic layer is nonempty. -/
theorem cubicLayerSite_nonempty (d R : ℕ) : Nonempty (CubicLayerSite d R) :=
  Fintype.card_pos_iff.mp <| by
    rw [cubicLayerSite_card]
    positivity

/-- A cubic transverse layer has a nontrivial layer-state space. -/
theorem cubicLayerState_card_nontrivial (d R : ℕ) :
    1 < Fintype.card (LayerState (CubicLayerSite d R)) := by
  letI : Nonempty (CubicLayerSite d R) := cubicLayerSite_nonempty d R
  exact layerState_card_nontrivial_of_nonempty (CubicLayerSite d R)

/-- The cubic-box cardinality form of the finite spectral prefactor smallness
condition. -/
theorem finiteSpectralPartitionPrefactor_small_of_cubicLayerSite_card
    (d R : ℕ) {theta : ℝ}
    (htheta : theta < (((2 ^ ((2 * R + 1) ^ d) - 1 : ℕ) : ℝ))⁻¹) :
    (((Fintype.card (LayerState (CubicLayerSite d R)) - 1 : ℕ) : ℝ) * theta) < 1 := by
  letI : Nonempty (CubicLayerSite d R) := cubicLayerSite_nonempty d R
  refine finiteSpectralPartitionPrefactor_small_of_layerState_lt_inv_two_pow_cardSubOne
    (CubicLayerSite d R) ?_
  rw [← cubicLayerSite_card d R] at htheta
  exact htheta

/-! ## Concrete cubic layer weights -/

/-- The cubic one-layer Ising weight is strictly positive. -/
theorem cubicLayerInternalWeight_pos (d R : ℕ) (p : IsingParams ℝ)
    (ω : LayerState (CubicLayerSite d R)) :
    0 < layerInternalWeight (cubicLayerGraph d R) p ω :=
  Real.exp_pos _

/-- The cubic adjacent-layer Ising transition weight is strictly positive. -/
theorem cubicLayerTransitionWeight_pos (d R : ℕ) (p : IsingParams ℝ)
    (ω η : LayerState (CubicLayerSite d R)) :
    0 < layerTransitionWeight (cubicLayerTransitionPairs d R) p ω η :=
  Real.exp_pos _

/-- The identity-pair cubic transition weight is symmetric in its two layer
states. -/
theorem cubicLayerTransitionWeight_symm (d R : ℕ) (p : IsingParams ℝ)
    (ω η : LayerState (CubicLayerSite d R)) :
    layerTransitionWeight (cubicLayerTransitionPairs d R) p ω η =
      layerTransitionWeight (cubicLayerTransitionPairs d R) p η ω := by
  unfold layerTransitionWeight cubicLayerTransitionPairs layerIdentityTransitionPairs
  congr 1
  congr 1
  rw [Finset.sum_image, Finset.sum_image]
  · exact Finset.sum_congr rfl fun x _ => mul_comm _ _
  · intro x _ y _ hxy
    exact (Prod.ext_iff.mp hxy).1
  · intro x _ y _ hxy
    exact (Prod.ext_iff.mp hxy).1

/-! ## Cubic max-index spin certificate wrappers -/

/-- Orthogonal max-index spin certificate for cubic transverse boxes, with the
finite prefactor smallness discharged by the cubic layer cardinality threshold.

The hypothesis on the canonical subdominant ratio is still an explicit
quantitative input; this wrapper only rewrites the cardinality threshold for
`CubicLayerSite d R`. -/
noncomputable def cubicLayerBalancedMinGapCertificate_orthogonal_layerCardSmall
    (d R : ℕ) (p : IsingParams ℝ) (x : CubicLayerSite d R)
    (hp : p.h = 0)
    (E : RealOrthogonalSpectralData
      (layerSymmetricTransferMatrix
        (layerInternalWeight (cubicLayerGraph d R) p)
        (layerTransitionWeight (cubicLayerTransitionPairs d R) p)))
    (hratio :
      E.subdominantRatio_maxEigenIndex
          (layerSymmetricTransferMatrix_entrywisePositive
            (layerInternalWeight (cubicLayerGraph d R) p)
            (layerTransitionWeight (cubicLayerTransitionPairs d R) p)
            (cubicLayerInternalWeight_pos d R p)
            (cubicLayerTransitionWeight_pos d R p))
        < (((2 ^ ((2 * R + 1) ^ d) - 1 : ℕ) : ℝ))⁻¹) :
    LayerBalancedMinSpectralGapCertificate
      (layerInternalWeight (cubicLayerGraph d R) p)
      (layerTransitionWeight (cubicLayerTransitionPairs d R) p)
      (layerSpinAt x) := by
  letI : Nonempty (CubicLayerSite d R) := cubicLayerSite_nonempty d R
  refine
    layerBalancedMinSpectralGapCertificate_of_orthogonalMaxEigenIndexFlipSpin_layerCardinalitySmall
      (layerInternalWeight (cubicLayerGraph d R) p)
      (layerTransitionWeight (cubicLayerTransitionPairs d R) p)
      x
      (cubicLayerInternalWeight_pos d R p)
      (cubicLayerTransitionWeight_pos d R p)
      ?_ ?_ E ?_
  · exact layerInternalWeight_flip_of_h_zero (cubicLayerGraph d R) p hp
  · exact layerTransitionWeight_flip_flip (cubicLayerTransitionPairs d R) p
  · rw [← cubicLayerSite_card d R] at hratio
    exact hratio

/-- Hermitian max-index spin certificate for cubic transverse boxes, with the
finite prefactor smallness discharged by the cubic layer cardinality threshold.

The hypothesis on the canonical subdominant ratio is still an explicit
quantitative input; this wrapper only rewrites the cardinality threshold for
`CubicLayerSite d R`. -/
noncomputable def cubicLayerBalancedMinGapCertificate_hermitian_layerCardSmall
    (d R : ℕ) (p : IsingParams ℝ) (x : CubicLayerSite d R)
    (hp : p.h = 0)
    (hratio :
      layerSymmetricTransfer_subdominantRatio_maxEigenIndex
          (layerInternalWeight (cubicLayerGraph d R) p)
          (layerTransitionWeight (cubicLayerTransitionPairs d R) p)
          (cubicLayerInternalWeight_pos d R p)
          (cubicLayerTransitionWeight_pos d R p)
          (cubicLayerTransitionWeight_symm d R p)
        < (((2 ^ ((2 * R + 1) ^ d) - 1 : ℕ) : ℝ))⁻¹) :
    LayerBalancedMinSpectralGapCertificate
      (layerInternalWeight (cubicLayerGraph d R) p)
      (layerTransitionWeight (cubicLayerTransitionPairs d R) p)
      (layerSpinAt x) := by
  letI : Nonempty (CubicLayerSite d R) := cubicLayerSite_nonempty d R
  refine
    layerBalancedMinSpectralGapCertificate_of_layerHermitianMaxEigenIndexFlipSpin_layerCardSmall
      (layerInternalWeight (cubicLayerGraph d R) p)
      (layerTransitionWeight (cubicLayerTransitionPairs d R) p)
      x
      (cubicLayerInternalWeight_pos d R p)
      (cubicLayerTransitionWeight_pos d R p)
      (cubicLayerTransitionWeight_symm d R p)
      ?_ ?_ ?_
  · exact layerInternalWeight_flip_of_h_zero (cubicLayerGraph d R) p hp
  · exact layerTransitionWeight_flip_flip (cubicLayerTransitionPairs d R) p
  · rw [← cubicLayerSite_card d R] at hratio
    exact hratio

end TransferMatrix

end IsingModel

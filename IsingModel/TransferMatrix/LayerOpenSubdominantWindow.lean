import IsingModel.TransferMatrix.LayerOpenBoundaryWindow

/-!
# Open-boundary canonical subdominant boundary-window bridges

This file fixes the open-boundary decay parameter to the canonical finite
max-index subdominant ratio supplied by the Perron-facing spectral API.  It
composes the boundary-coordinate window from `LayerOpenBoundaryWindow.lean`
with `RealOrthogonalSpectralData.subdominantRatio_maxEigenIndex`, removing the
explicit `theta`, `theta_nonneg`, and `subdominant_abs_le` inputs from the
max-index open-boundary consumers.

The results are still finite and conditional.  The boundary-window inequality
and parity-adapted spectral data remain explicit inputs.  This file does not
construct parity-adapted spectral data, prove an interacting cubic-layer
spectral window, pass to a thermodynamic limit, or prove final hyperplane
exponential decay.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-! ## Canonical-ratio certificate wrappers -/

/-- Max-index open min-gap certificate with the decay parameter fixed to the
canonical subdominant ratio and denominator smallness supplied by the boundary
window. -/
noncomputable def
    layerOpenMinGapCert_of_maxEigenIndexCanonicalRatioBoundaryWindow
    [Nonempty Ω]
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (hu : ∀ a, 0 < u a) (hk_pos : ∀ a b, 0 < k a b)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (hratio_window :
      E.subdominantRatio_maxEigenIndex
          (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos)
        < layerOpenBoundarySpectralWindowCap u E E.maxEigenIndex)
    (central_dominant_channel_zero : ∀ i l,
      E.boundaryCoordinates (layerOpenBalancedBoundaryVector u) i *
        E.markedMatrix f i E.maxEigenIndex *
        E.markedMatrix f E.maxEigenIndex l *
        E.boundaryCoordinates (layerOpenBalancedBoundaryVector u) l = 0) :
    LayerOpenMinSpectralGapCertificate u k f :=
  layerOpenMinGapCert_of_maxEigenIndexBoundaryWindow
    u k f hu hk_pos E
    (E.subdominantRatio_maxEigenIndex
      (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos))
    (E.subdominantRatio_maxEigenIndex_nonneg
      (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos))
    hratio_window
    (E.eigenvalue_abs_le_subdominantRatio_maxEigenIndex
      (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos))
    central_dominant_channel_zero

/-- Open spin-observable min-gap certificate with flip-parity cancellation,
boundary-window denominator control, and the canonical max-index subdominant
ratio. -/
noncomputable def
    layerOpenMinGapCert_of_maxEigenIndexFlipParityCanonicalRatioBoundaryWindow
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (hratio_window :
      E.subdominantRatio_maxEigenIndex
          (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos)
        < layerOpenBoundarySpectralWindowCap u E E.maxEigenIndex)
    (hparity : E.ColumnFlipParity (layerStateFlipEquiv S)) :
    LayerOpenMinSpectralGapCertificate u k (layerSpinAt x) := by
  letI : Nonempty (LayerState S) := ⟨default⟩
  exact
    layerOpenMinGapCert_of_maxEigenIndexFlipParitySpin_boundaryWindow
      u k x hu hk_pos hu_flip hk_flip E
      (E.subdominantRatio_maxEigenIndex
        (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos))
      (E.subdominantRatio_maxEigenIndex_nonneg
        (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos))
      hratio_window
      (E.eigenvalue_abs_le_subdominantRatio_maxEigenIndex
        (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos))
      hparity

/-- Physical zero-field open spin-observable min-gap certificate with
flip-parity cancellation, boundary-window denominator control, and the
canonical max-index subdominant ratio. -/
noncomputable def
    layerOpenMinGapCert_of_layerMaxEigenIndexFlipParityCanonicalRatioBoundaryWindow
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ) (hp : p.h = 0) (x : S)
    (spec : RealOrthogonalSpectralData
      (layerSymmetricTransferMatrix
        (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)))
    (hratio_window :
      spec.subdominantRatio_maxEigenIndex
          (layerSymmetricTransferMatrix_entrywisePositive
            (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)
            (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _))
        <
          layerOpenBoundarySpectralWindowCap
            (layerInternalWeight H p) spec spec.maxEigenIndex)
    (hparity : spec.ColumnFlipParity (layerStateFlipEquiv S)) :
    LayerOpenMinSpectralGapCertificate
      (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)
      (layerSpinAt x) := by
  letI : Nonempty (LayerState S) := ⟨default⟩
  exact
    layerOpenMinGapCert_of_maxEigenIndexFlipParityCanonicalRatioBoundaryWindow
      (layerInternalWeight H p) (layerTransitionWeight transitionPairs p) x
      (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _)
      (layerInternalWeight_flip_of_h_zero H p hp)
      (layerTransitionWeight_flip_flip transitionPairs p)
      spec hratio_window hparity

/-! ## Project-level open-slab consumers -/

/-- Project-level finite open-slab same-transverse-site correlation decay with
the canonical max-index subdominant ratio and boundary-window denominator
control. -/
theorem
    correlation_layerOpenSlabGraph_same_transverse_abs_le_of_canonicalRatioBoundaryWindow
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ) (hp : p.h = 0) (x : S)
    (spec : RealOrthogonalSpectralData
      (layerSymmetricTransferMatrix
        (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)))
    (hratio_window :
      spec.subdominantRatio_maxEigenIndex
          (layerSymmetricTransferMatrix_entrywisePositive
            (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)
            (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _))
        <
          layerOpenBoundarySpectralWindowCap
            (layerInternalWeight H p) spec spec.maxEigenIndex)
    (hparity : spec.ColumnFlipParity (layerStateFlipEquiv S))
    (left sep right : ℕ) (hsep : 0 < sep) :
    |correlation (layerOpenSlabGraph (S := S) H transitionPairs (left + sep + right)) p
      ({Prod.mk (layerOpenLeftIndex left sep right) x,
        Prod.mk (layerOpenRightIndex left sep right) x} :
          Finset (LayerOpenSlabSite (left + sep + right) S))|
      ≤
        (spec.boundaryMarkedSpectralPrefactor (layerSpinAt x)
          (layerOpenBalancedBoundaryVector (layerInternalWeight H p))
          (layerOpenBalancedBoundaryVector (layerInternalWeight H p)) /
            spec.boundarySpectralPartitionPrefactor
              (layerOpenBalancedBoundaryVector (layerInternalWeight H p))
              spec.maxEigenIndex
              (spec.subdominantRatio_maxEigenIndex
                (layerSymmetricTransferMatrix_entrywisePositive
                  (layerInternalWeight H p)
                  (layerTransitionWeight transitionPairs p)
                  (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _)))) *
          (spec.subdominantRatio_maxEigenIndex
            (layerSymmetricTransferMatrix_entrywisePositive
              (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)
              (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _))) ^ sep := by
  letI : Nonempty (LayerState S) := ⟨default⟩
  exact
    correlation_layerOpenSlabGraph_same_transverse_abs_le_of_maxEigenIndexFlipParity_boundaryWindow
      (S := S) H transitionPairs p hp x spec
      (spec.subdominantRatio_maxEigenIndex
        (layerSymmetricTransferMatrix_entrywisePositive
          (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)
          (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _)))
      (spec.subdominantRatio_maxEigenIndex_nonneg
        (layerSymmetricTransferMatrix_entrywisePositive
          (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)
          (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _)))
      hratio_window
      (spec.eigenvalue_abs_le_subdominantRatio_maxEigenIndex
        (layerSymmetricTransferMatrix_entrywisePositive
          (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)
          (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _)))
      hparity left sep right hsep

/-- Cubic transverse open slabs inherit the canonical-ratio boundary-window
consumer from the generic open-slab theorem. -/
theorem
    correlation_cubicLayerOpenSlabGraph_same_transverse_abs_le_of_canonicalRatioBoundaryWindow
    (d R : ℕ) (p : IsingParams ℝ) (hp : p.h = 0) (x : CubicLayerSite d R)
    (spec : RealOrthogonalSpectralData
      (layerSymmetricTransferMatrix
        (layerInternalWeight (cubicLayerGraph d R) p)
        (layerTransitionWeight (cubicLayerTransitionPairs d R) p)))
    (hratio_window :
      spec.subdominantRatio_maxEigenIndex
          (layerSymmetricTransferMatrix_entrywisePositive
            (layerInternalWeight (cubicLayerGraph d R) p)
            (layerTransitionWeight (cubicLayerTransitionPairs d R) p)
            (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _))
        <
          layerOpenBoundarySpectralWindowCap
            (layerInternalWeight (cubicLayerGraph d R) p)
            spec spec.maxEigenIndex)
    (hparity :
      spec.ColumnFlipParity (layerStateFlipEquiv (CubicLayerSite d R)))
    (left sep right : ℕ) (hsep : 0 < sep) :
    |correlation (cubicLayerOpenSlabGraph d R (left + sep + right)) p
      ({Prod.mk (layerOpenLeftIndex left sep right) x,
        Prod.mk (layerOpenRightIndex left sep right) x} :
          Finset (LayerOpenSlabSite (left + sep + right) (CubicLayerSite d R)))|
      ≤
        (spec.boundaryMarkedSpectralPrefactor (layerSpinAt x)
          (layerOpenBalancedBoundaryVector
            (layerInternalWeight (cubicLayerGraph d R) p))
          (layerOpenBalancedBoundaryVector
            (layerInternalWeight (cubicLayerGraph d R) p)) /
            spec.boundarySpectralPartitionPrefactor
              (layerOpenBalancedBoundaryVector
                (layerInternalWeight (cubicLayerGraph d R) p))
              spec.maxEigenIndex
              (spec.subdominantRatio_maxEigenIndex
                (layerSymmetricTransferMatrix_entrywisePositive
                  (layerInternalWeight (cubicLayerGraph d R) p)
                  (layerTransitionWeight (cubicLayerTransitionPairs d R) p)
                  (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _)))) *
          (spec.subdominantRatio_maxEigenIndex
            (layerSymmetricTransferMatrix_entrywisePositive
              (layerInternalWeight (cubicLayerGraph d R) p)
              (layerTransitionWeight (cubicLayerTransitionPairs d R) p)
              (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _))) ^ sep := by
  rw [cubicLayerOpenSlabGraph]
  exact
    correlation_layerOpenSlabGraph_same_transverse_abs_le_of_canonicalRatioBoundaryWindow
      (S := CubicLayerSite d R) (cubicLayerGraph d R)
      (cubicLayerTransitionPairs d R) p hp x spec hratio_window hparity
      left sep right hsep

end TransferMatrix

end IsingModel

import IsingModel.TransferMatrix.LayerOpenBoundaryNormWindow

/-!
# Open-boundary physical norm-window bridges

This file exposes the denominator in the open-boundary norm-window cap as the
finite one-layer internal partition sum for physical layer weights.  It is a
thin physical API over `LayerOpenBoundaryNormWindow.lean`: the cap is
definitionally the existing generic norm-window cap at
`u = layerInternalWeight H p`, but its statement displays
`∑ ω, layerInternalWeight H p ω`.

The results remain finite and conditional.  They do not prove the physical
norm-window inequality, construct parity-adapted spectral data, prove an
interacting cubic-layer spectral window, pass to a thermodynamic limit, or
prove final hyperplane exponential decay.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

open scoped BigOperators

/-! ## Physical norm-window caps -/

/-- The open-boundary norm-window cap for physical layer weights, with the
one-layer internal partition sum displayed explicitly. -/
noncomputable def layerOpenPhysicalBoundaryNormWindowCap
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ)
    (spec : RealOrthogonalSpectralData
      (layerSymmetricTransferMatrix
        (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)))
    (top : LayerState S) : ℝ :=
  min 1
    ((spec.boundaryCoordinates
      (layerOpenBalancedBoundaryVector (layerInternalWeight H p)) top) ^ 2 /
        ∑ ω : LayerState S, layerInternalWeight H p ω)

/-- The physical norm-window cap is the generic norm-window cap specialized to
the physical one-layer weight. -/
theorem layerOpenPhysicalBoundaryNormWindowCap_eq_layerOpenBoundaryNormWindowCap
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ)
    (spec : RealOrthogonalSpectralData
      (layerSymmetricTransferMatrix
        (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)))
    (top : LayerState S) :
    layerOpenPhysicalBoundaryNormWindowCap H transitionPairs p spec top =
      layerOpenBoundaryNormWindowCap (layerInternalWeight H p) spec top :=
  rfl

/-- Signed-positive top coordinates make the physical norm-window cap
strictly positive. -/
theorem layerOpenPhysicalBoundaryNormWindowCap_pos_of_signedPositiveColumn
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ)
    (spec : RealOrthogonalSpectralData
      (layerSymmetricTransferMatrix
        (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)))
    (top : LayerState S) (hpos : spec.SignedPositiveColumn top) :
    0 < layerOpenPhysicalBoundaryNormWindowCap H transitionPairs p spec top := by
  letI : Nonempty (LayerState S) := ⟨default⟩
  rw [layerOpenPhysicalBoundaryNormWindowCap]
  exact lt_min zero_lt_one
    (div_pos
      (layerOpenBoundaryCoordinate_sq_pos_of_signedPositiveColumn
        (layerInternalWeight H p) (fun _ => Real.exp_pos _) spec top hpos)
      (Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty))

/-- A physical norm-window bound implies the existing open boundary spectral
window. -/
theorem theta_lt_layerOpenBoundarySpectralWindowCap_of_lt_physicalNormWindowCap
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ)
    (spec : RealOrthogonalSpectralData
      (layerSymmetricTransferMatrix
        (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)))
    (top : LayerState S) (hpos : spec.SignedPositiveColumn top) {theta : ℝ}
    (htheta :
      theta < layerOpenPhysicalBoundaryNormWindowCap H transitionPairs p spec top) :
    theta < layerOpenBoundarySpectralWindowCap (layerInternalWeight H p) spec top :=
  theta_lt_layerOpenBoundarySpectralWindowCap_of_lt_normWindowCap_signedPositive
    (layerInternalWeight H p) (fun _ => Real.exp_pos _) spec top hpos
    (by
      simpa [layerOpenPhysicalBoundaryNormWindowCap_eq_layerOpenBoundaryNormWindowCap]
        using htheta)

/-! ## Physical certificate and open-slab consumers -/

/-- Physical zero-field open spin-observable min-gap certificate with
flip-parity cancellation, canonical max-index ratio, and the physical
norm-window denominator. -/
noncomputable def
    layerOpenMinGapCert_of_layerMaxEigenIndexFlipParityCanonicalRatioPhysicalNormWindow
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ) (hp : p.h = 0) (x : S)
    (spec : RealOrthogonalSpectralData
      (layerSymmetricTransferMatrix
        (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)))
    (hratio_phys :
      spec.subdominantRatio_maxEigenIndex
          (layerSymmetricTransferMatrix_entrywisePositive
            (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)
            (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _))
        <
          layerOpenPhysicalBoundaryNormWindowCap
            H transitionPairs p spec spec.maxEigenIndex)
    (hparity : spec.ColumnFlipParity (layerStateFlipEquiv S)) :
    LayerOpenMinSpectralGapCertificate
      (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)
      (layerSpinAt x) :=
  layerOpenMinGapCert_of_layerMaxEigenIndexFlipParityCanonicalRatioBoundaryNormWindow
    H transitionPairs p hp x spec
    (by
      simpa [layerOpenPhysicalBoundaryNormWindowCap_eq_layerOpenBoundaryNormWindowCap]
        using hratio_phys)
    hparity

/-- Project-level finite open-slab same-transverse-site correlation decay with
the canonical max-index subdominant ratio and the physical norm-window
denominator. -/
theorem
    correlation_layerOpenSlabGraph_same_transverse_abs_le_of_canonicalRatioPhysicalNormWindow
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ) (hp : p.h = 0) (x : S)
    (spec : RealOrthogonalSpectralData
      (layerSymmetricTransferMatrix
        (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)))
    (hratio_phys :
      spec.subdominantRatio_maxEigenIndex
          (layerSymmetricTransferMatrix_entrywisePositive
            (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)
            (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _))
        <
          layerOpenPhysicalBoundaryNormWindowCap
            H transitionPairs p spec spec.maxEigenIndex)
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
  exact
    correlation_layerOpenSlabGraph_same_transverse_abs_le_of_canonicalRatioBoundaryNormWindow
      H transitionPairs p hp x spec
      (by
        simpa [layerOpenPhysicalBoundaryNormWindowCap_eq_layerOpenBoundaryNormWindowCap]
          using hratio_phys)
      hparity left sep right hsep

/-! ## Cubic physical caps and consumers -/

/-- The cubic-layer physical norm-window cap, specialized from the generic
physical cap. -/
noncomputable def cubicLayerOpenPhysicalBoundaryNormWindowCap
    (d R : ℕ) (p : IsingParams ℝ)
    (spec : RealOrthogonalSpectralData
      (layerSymmetricTransferMatrix
        (layerInternalWeight (cubicLayerGraph d R) p)
        (layerTransitionWeight (cubicLayerTransitionPairs d R) p)))
    (top : LayerState (CubicLayerSite d R)) : ℝ :=
  layerOpenPhysicalBoundaryNormWindowCap
    (cubicLayerGraph d R) (cubicLayerTransitionPairs d R) p spec top

/-- Cubic transverse open slabs inherit the canonical-ratio physical
norm-window consumer from the generic physical open-slab theorem. -/
theorem
    correlation_cubicLayerOpenSlabGraph_same_transverse_abs_le_of_canonicalRatioPhysicalNormWindow
    (d R : ℕ) (p : IsingParams ℝ) (hp : p.h = 0) (x : CubicLayerSite d R)
    (spec : RealOrthogonalSpectralData
      (layerSymmetricTransferMatrix
        (layerInternalWeight (cubicLayerGraph d R) p)
        (layerTransitionWeight (cubicLayerTransitionPairs d R) p)))
    (hratio_phys :
      spec.subdominantRatio_maxEigenIndex
          (layerSymmetricTransferMatrix_entrywisePositive
            (layerInternalWeight (cubicLayerGraph d R) p)
            (layerTransitionWeight (cubicLayerTransitionPairs d R) p)
            (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _))
        <
          cubicLayerOpenPhysicalBoundaryNormWindowCap
            d R p spec spec.maxEigenIndex)
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
    correlation_layerOpenSlabGraph_same_transverse_abs_le_of_canonicalRatioPhysicalNormWindow
      (S := CubicLayerSite d R) (cubicLayerGraph d R)
      (cubicLayerTransitionPairs d R) p hp x spec
      (by simpa [cubicLayerOpenPhysicalBoundaryNormWindowCap] using hratio_phys)
      hparity left sep right hsep

end TransferMatrix

end IsingModel

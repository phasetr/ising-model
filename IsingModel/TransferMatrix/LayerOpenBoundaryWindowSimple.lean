import IsingModel.TransferMatrix.LayerOpenParitySimple

/-!
# Open-boundary boundary-window consumers from simple spectral columns

This file connects the columnwise simple-eigenspace parity bridge to the
open-boundary boundary-window route.  It exposes the explicit `top`/`theta`
boundary-window consumers with `ColumnSimpleEigenspaces` in place of a direct
`ColumnFlipParity` hypothesis.

The results are finite and conditional.  They do not prove a new spectral
window estimate, a physical norm-window inequality, an interacting cubic-layer
spectral window, a thermodynamic limit, or final hyperplane exponential decay.
They also do not construct parity-adapted bases in degenerate eigenspaces.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

/-! ## Open-boundary boundary-window consumers with simple-column parity input -/

/-- Open spin-observable min-gap certificate with boundary-window denominator
control and flip-parity cancellation derived from columnwise simple
eigenspaces. -/
noncomputable def
    layerOpenMinGapCert_of_subdominant_signedPositiveSimpleParitySpin_boundaryWindow
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (top : LayerState S) (theta : ℝ)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_boundary_window :
      theta < layerOpenBoundarySpectralWindowCap u E top)
    (subdominant_abs_le :
      ∀ i, i ≠ top → |E.eigenvalue i| ≤ theta * E.eigenvalue top)
    (hsimple : E.ColumnSimpleEigenspaces)
    (dominant_column_signed_pos : E.SignedPositiveColumn top) :
    LayerOpenMinSpectralGapCertificate u k (layerSpinAt x) :=
  layerOpenMinGapCert_of_subdominant_signedPositiveFlipParitySpin_boundaryWindow
    u k x hu hk_pos hu_flip hk_flip E top theta theta_nonneg
    theta_lt_boundary_window subdominant_abs_le
    (layerSymmetricTransfer_columnFlipParity_of_columnSimple
      u k hu_flip hk_flip E hsimple)
    dominant_column_signed_pos

/-- Max-index open spin-observable min-gap certificate with boundary-window
denominator control and flip parity derived from columnwise simple
eigenspaces. -/
noncomputable def
    layerOpenMinGapCert_of_maxEigenIndexSimpleParitySpin_boundaryWindow
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (theta : ℝ)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_boundary_window :
      theta < layerOpenBoundarySpectralWindowCap u E E.maxEigenIndex)
    (subdominant_abs_le :
      ∀ i, i ≠ E.maxEigenIndex →
        |E.eigenvalue i| ≤ theta * E.eigenvalue E.maxEigenIndex)
    (hsimple : E.ColumnSimpleEigenspaces) :
    LayerOpenMinSpectralGapCertificate u k (layerSpinAt x) :=
  layerOpenMinGapCert_of_maxEigenIndexFlipParitySpin_boundaryWindow
    u k x hu hk_pos hu_flip hk_flip E theta theta_nonneg
    theta_lt_boundary_window subdominant_abs_le
    (layerSymmetricTransfer_columnFlipParity_of_columnSimple
      u k hu_flip hk_flip E hsimple)

/-- Physical open spin-observable min-gap certificate with boundary-window
denominator control and flip parity derived from columnwise simple
eigenspaces. -/
noncomputable def
    layerOpenMinGapCert_of_layerSubdominant_signedPositiveSimpleParitySpin_boundaryWindow
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ) (hp : p.h = 0) (x : S)
    (spec : RealOrthogonalSpectralData
      (layerSymmetricTransferMatrix
        (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)))
    (top : LayerState S) (theta : ℝ)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_boundary_window :
      theta <
        layerOpenBoundarySpectralWindowCap
          (layerInternalWeight H p) spec top)
    (subdominant_abs_le :
      ∀ i, i ≠ top → |spec.eigenvalue i| ≤ theta * spec.eigenvalue top)
    (hsimple : spec.ColumnSimpleEigenspaces)
    (dominant_column_signed_pos : spec.SignedPositiveColumn top) :
    LayerOpenMinSpectralGapCertificate
      (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)
      (layerSpinAt x) :=
  layerOpenMinGapCert_of_subdominant_signedPositiveSimpleParitySpin_boundaryWindow
    (layerInternalWeight H p) (layerTransitionWeight transitionPairs p) x
    (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _)
    (layerInternalWeight_flip_of_h_zero H p hp)
    (layerTransitionWeight_flip_flip transitionPairs p)
    spec top theta theta_nonneg theta_lt_boundary_window
    subdominant_abs_le hsimple dominant_column_signed_pos

/-- Physical max-index open spin-observable min-gap certificate with
boundary-window denominator control and flip parity derived from columnwise
simple eigenspaces. -/
noncomputable def
    layerOpenMinGapCert_of_layerMaxEigenIndexSimpleParitySpin_boundaryWindow
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ) (hp : p.h = 0) (x : S)
    (spec : RealOrthogonalSpectralData
      (layerSymmetricTransferMatrix
        (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)))
    (theta : ℝ)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_boundary_window :
      theta <
        layerOpenBoundarySpectralWindowCap
          (layerInternalWeight H p) spec spec.maxEigenIndex)
    (subdominant_abs_le :
      ∀ i, i ≠ spec.maxEigenIndex →
        |spec.eigenvalue i| ≤ theta * spec.eigenvalue spec.maxEigenIndex)
    (hsimple : spec.ColumnSimpleEigenspaces) :
    LayerOpenMinSpectralGapCertificate
      (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)
      (layerSpinAt x) :=
  layerOpenMinGapCert_of_layerMaxEigenIndexFlipParitySpin_boundaryWindow
    H transitionPairs p hp x spec theta theta_nonneg
    theta_lt_boundary_window subdominant_abs_le
    (layerSymmetricTransfer_columnFlipParity_of_columnSimple
      (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)
      (layerInternalWeight_flip_of_h_zero H p hp)
      (layerTransitionWeight_flip_flip transitionPairs p) spec hsimple)

/-- Project-level finite open-slab same-transverse-site correlation decay from
signed-positive simple-column parity and boundary-window denominator control. -/
theorem
    correlation_layerOpenSlabGraph_abs_le_of_signedPositiveSimpleParity_boundaryWindow
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ) (hp : p.h = 0) (x : S)
    (spec : RealOrthogonalSpectralData
      (layerSymmetricTransferMatrix
        (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)))
    (top : LayerState S) (theta : ℝ)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_boundary_window :
      theta <
        layerOpenBoundarySpectralWindowCap
          (layerInternalWeight H p) spec top)
    (subdominant_abs_le :
      ∀ i, i ≠ top → |spec.eigenvalue i| ≤ theta * spec.eigenvalue top)
    (hsimple : spec.ColumnSimpleEigenspaces)
    (dominant_column_signed_pos : spec.SignedPositiveColumn top)
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
              (layerOpenBalancedBoundaryVector (layerInternalWeight H p)) top theta) *
          theta ^ sep := by
  exact
    correlation_layerOpenSlabGraph_same_transverse_abs_le_of_signedPositiveFlipParity_boundaryWindow
      H transitionPairs p hp x spec top theta theta_nonneg
      theta_lt_boundary_window subdominant_abs_le
      (layerSymmetricTransfer_columnFlipParity_of_columnSimple
        (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)
        (layerInternalWeight_flip_of_h_zero H p hp)
        (layerTransitionWeight_flip_flip transitionPairs p) spec hsimple)
      dominant_column_signed_pos left sep right hsep

/-- Project-level finite open-slab same-transverse-site correlation decay from
max-index simple-column parity and boundary-window denominator control. -/
theorem
    correlation_layerOpenSlabGraph_abs_le_of_maxEigenIndexSimpleParity_boundaryWindow
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ) (hp : p.h = 0) (x : S)
    (spec : RealOrthogonalSpectralData
      (layerSymmetricTransferMatrix
        (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)))
    (theta : ℝ)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_boundary_window :
      theta <
        layerOpenBoundarySpectralWindowCap
          (layerInternalWeight H p) spec spec.maxEigenIndex)
    (subdominant_abs_le :
      ∀ i, i ≠ spec.maxEigenIndex →
        |spec.eigenvalue i| ≤ theta * spec.eigenvalue spec.maxEigenIndex)
    (hsimple : spec.ColumnSimpleEigenspaces)
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
              spec.maxEigenIndex theta) *
          theta ^ sep := by
  exact
    correlation_layerOpenSlabGraph_same_transverse_abs_le_of_maxEigenIndexFlipParity_boundaryWindow
      H transitionPairs p hp x spec theta theta_nonneg
      theta_lt_boundary_window subdominant_abs_le
      (layerSymmetricTransfer_columnFlipParity_of_columnSimple
        (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)
        (layerInternalWeight_flip_of_h_zero H p hp)
        (layerTransitionWeight_flip_flip transitionPairs p) spec hsimple)
      left sep right hsep

/-- Cubic transverse open slabs inherit the signed-positive simple-parity
boundary-window consumer from the generic physical open-slab theorem. -/
theorem
    correlation_cubicLayerOpenSlabGraph_abs_le_of_signedPositiveSimpleParityBoundaryWindow
    (d R : ℕ) (p : IsingParams ℝ) (hp : p.h = 0) (x : CubicLayerSite d R)
    (spec : RealOrthogonalSpectralData
      (layerSymmetricTransferMatrix
        (layerInternalWeight (cubicLayerGraph d R) p)
        (layerTransitionWeight (cubicLayerTransitionPairs d R) p)))
    (top : LayerState (CubicLayerSite d R)) (theta : ℝ)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_boundary_window :
      theta <
        layerOpenBoundarySpectralWindowCap
          (layerInternalWeight (cubicLayerGraph d R) p) spec top)
    (subdominant_abs_le :
      ∀ i, i ≠ top → |spec.eigenvalue i| ≤ theta * spec.eigenvalue top)
    (hsimple : spec.ColumnSimpleEigenspaces)
    (dominant_column_signed_pos : spec.SignedPositiveColumn top)
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
                (layerInternalWeight (cubicLayerGraph d R) p)) top theta) *
          theta ^ sep := by
  rw [cubicLayerOpenSlabGraph]
  exact
    correlation_layerOpenSlabGraph_abs_le_of_signedPositiveSimpleParity_boundaryWindow
      (S := CubicLayerSite d R) (cubicLayerGraph d R)
      (cubicLayerTransitionPairs d R) p hp x spec top theta theta_nonneg
      theta_lt_boundary_window subdominant_abs_le hsimple
      dominant_column_signed_pos left sep right hsep

/-- Cubic transverse open slabs inherit the max-index simple-parity
boundary-window consumer from the generic physical open-slab theorem. -/
theorem
    correlation_cubicLayerOpenSlabGraph_abs_le_of_maxEigenIndexSimpleParityBoundaryWindow
    (d R : ℕ) (p : IsingParams ℝ) (hp : p.h = 0) (x : CubicLayerSite d R)
    (spec : RealOrthogonalSpectralData
      (layerSymmetricTransferMatrix
        (layerInternalWeight (cubicLayerGraph d R) p)
        (layerTransitionWeight (cubicLayerTransitionPairs d R) p)))
    (theta : ℝ)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_boundary_window :
      theta <
        layerOpenBoundarySpectralWindowCap
          (layerInternalWeight (cubicLayerGraph d R) p) spec spec.maxEigenIndex)
    (subdominant_abs_le :
      ∀ i, i ≠ spec.maxEigenIndex →
        |spec.eigenvalue i| ≤ theta * spec.eigenvalue spec.maxEigenIndex)
    (hsimple : spec.ColumnSimpleEigenspaces)
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
              spec.maxEigenIndex theta) *
          theta ^ sep := by
  rw [cubicLayerOpenSlabGraph]
  exact
    correlation_layerOpenSlabGraph_abs_le_of_maxEigenIndexSimpleParity_boundaryWindow
      (S := CubicLayerSite d R) (cubicLayerGraph d R)
      (cubicLayerTransitionPairs d R) p hp x spec theta theta_nonneg
      theta_lt_boundary_window subdominant_abs_le hsimple left sep right hsep

end TransferMatrix

end IsingModel

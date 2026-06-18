import IsingModel.TransferMatrix.LayerOpenSlabGraph
import IsingModel.TransferMatrix.LayerOpenSpectral

/-!
# Finite open layer-slab spectral decay consumers

This file consumes the finite open-boundary spectral numerator constructor as
project-level correlation bounds for open layer slabs.  The denominator remains
an explicit matrix-partition lower-bound hypothesis.

The statements remain finite and conditional.  They do not prove an open
denominator spectral lower bound, Perron--Frobenius input, a physical
interacting spectral window, thermodynamic-limit decay, or final hyperplane
exponential decay.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

open scoped BigOperators

/-- Physical open-slab orthogonal boundary-dominance hypotheses produce an open
min-gap certificate for the corresponding concrete layer weights. -/
noncomputable def
    layerOpenMinSpectralGapCertificate_of_layerOrthogonalBoundaryDominantBounds
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ) (x : S)
    (spec : RealOrthogonalSpectralData
      (layerSymmetricTransferMatrix
        (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)))
    (top : LayerState S) (scale theta partitionPrefactor : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (partitionPrefactor_pos : 0 < partitionPrefactor)
    (partition_lower_matrix : ∀ {n : ℕ},
      partitionPrefactor * scale ^ n ≤
        layerOpenMatrixPartition
          (layerInternalWeight H p) (layerTransitionWeight transitionPairs p) n)
    (eigenvalue_abs_le_scale : ∀ i, |spec.eigenvalue i| ≤ scale)
    (subdominant_abs_le : ∀ i, i ≠ top → |spec.eigenvalue i| ≤ theta * scale)
    (central_dominant_channel_zero : ∀ i l,
      spec.boundaryCoordinates
          (layerOpenBalancedBoundaryVector (layerInternalWeight H p)) i *
        spec.markedMatrix (layerSpinAt x) i top *
        spec.markedMatrix (layerSpinAt x) top l *
        spec.boundaryCoordinates
          (layerOpenBalancedBoundaryVector (layerInternalWeight H p)) l = 0) :
    LayerOpenMinSpectralGapCertificate
      (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)
      (layerSpinAt x) :=
  layerOpenMinSpectralGapCertificate_of_matrixPartition_orthogonalBoundaryDominantBounds
    (layerInternalWeight H p) (layerTransitionWeight transitionPairs p) (layerSpinAt x)
    (fun _ => Real.exp_pos _) spec top scale theta partitionPrefactor
    scale_pos theta_nonneg theta_lt_one partitionPrefactor_pos
    partition_lower_matrix eigenvalue_abs_le_scale subdominant_abs_le
    central_dominant_channel_zero

/-- Orthogonal boundary-dominance hypotheses give project-level finite open-slab
same-transverse-site correlation decay. -/
theorem
    correlation_layerOpenSlabGraph_same_transverse_abs_le_of_orthogonalBoundaryDominantBounds
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ) (x : S)
    (spec : RealOrthogonalSpectralData
      (layerSymmetricTransferMatrix
        (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)))
    (top : LayerState S) (scale theta partitionPrefactor : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (partitionPrefactor_pos : 0 < partitionPrefactor)
    (partition_lower_matrix : ∀ {n : ℕ},
      partitionPrefactor * scale ^ n ≤
        layerOpenMatrixPartition
          (layerInternalWeight H p) (layerTransitionWeight transitionPairs p) n)
    (eigenvalue_abs_le_scale : ∀ i, |spec.eigenvalue i| ≤ scale)
    (subdominant_abs_le : ∀ i, i ≠ top → |spec.eigenvalue i| ≤ theta * scale)
    (central_dominant_channel_zero : ∀ i l,
      spec.boundaryCoordinates
          (layerOpenBalancedBoundaryVector (layerInternalWeight H p)) i *
        spec.markedMatrix (layerSpinAt x) i top *
        spec.markedMatrix (layerSpinAt x) top l *
        spec.boundaryCoordinates
          (layerOpenBalancedBoundaryVector (layerInternalWeight H p)) l = 0)
    (left sep right : ℕ) (hsep : 0 < sep) :
    |correlation (layerOpenSlabGraph (S := S) H transitionPairs (left + sep + right)) p
      ({Prod.mk (layerOpenLeftIndex left sep right) x,
        Prod.mk (layerOpenRightIndex left sep right) x} :
          Finset (LayerOpenSlabSite (left + sep + right) S))|
      ≤
        (spec.boundaryMarkedSpectralPrefactor (layerSpinAt x)
          (layerOpenBalancedBoundaryVector (layerInternalWeight H p))
          (layerOpenBalancedBoundaryVector (layerInternalWeight H p)) /
            partitionPrefactor) *
          theta ^ sep := by
  let cert :
      LayerOpenMinSpectralGapCertificate
        (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)
        (layerSpinAt x) :=
    layerOpenMinSpectralGapCertificate_of_layerOrthogonalBoundaryDominantBounds
      H transitionPairs p x spec top scale theta partitionPrefactor
      scale_pos theta_nonneg theta_lt_one partitionPrefactor_pos
      partition_lower_matrix eigenvalue_abs_le_scale subdominant_abs_le
      central_dominant_channel_zero
  exact
    correlation_layerOpenSlabGraph_same_transverse_abs_le_of_openMinSpectralGapCertificate
      (S := S) H transitionPairs p x cert left sep right hsep

/-- Cubic transverse open slabs inherit the finite open spectral-decay consumer
from the generic open-slab theorem. -/
theorem
    correlation_cubicLayerOpenSlabGraph_same_transverse_abs_le_of_orthogonalBoundaryDominantBounds
    (d R : ℕ) (p : IsingParams ℝ) (x : CubicLayerSite d R)
    (spec : RealOrthogonalSpectralData
      (layerSymmetricTransferMatrix
        (layerInternalWeight (cubicLayerGraph d R) p)
        (layerTransitionWeight (cubicLayerTransitionPairs d R) p)))
    (top : LayerState (CubicLayerSite d R)) (scale theta partitionPrefactor : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (partitionPrefactor_pos : 0 < partitionPrefactor)
    (partition_lower_matrix : ∀ {n : ℕ},
      partitionPrefactor * scale ^ n ≤
        layerOpenMatrixPartition
          (layerInternalWeight (cubicLayerGraph d R) p)
          (layerTransitionWeight (cubicLayerTransitionPairs d R) p) n)
    (eigenvalue_abs_le_scale : ∀ i, |spec.eigenvalue i| ≤ scale)
    (subdominant_abs_le : ∀ i, i ≠ top → |spec.eigenvalue i| ≤ theta * scale)
    (central_dominant_channel_zero : ∀ i l,
      spec.boundaryCoordinates
          (layerOpenBalancedBoundaryVector
            (layerInternalWeight (cubicLayerGraph d R) p)) i *
        spec.markedMatrix (layerSpinAt x) i top *
        spec.markedMatrix (layerSpinAt x) top l *
        spec.boundaryCoordinates
          (layerOpenBalancedBoundaryVector
            (layerInternalWeight (cubicLayerGraph d R) p)) l = 0)
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
            partitionPrefactor) *
          theta ^ sep := by
  rw [cubicLayerOpenSlabGraph]
  exact
    correlation_layerOpenSlabGraph_same_transverse_abs_le_of_orthogonalBoundaryDominantBounds
      (S := CubicLayerSite d R) (cubicLayerGraph d R)
      (cubicLayerTransitionPairs d R) p x spec top scale theta partitionPrefactor
      scale_pos theta_nonneg theta_lt_one partitionPrefactor_pos
      partition_lower_matrix eigenvalue_abs_le_scale subdominant_abs_le
      central_dominant_channel_zero left sep right hsep

end TransferMatrix

end IsingModel

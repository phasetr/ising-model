import IsingModel.TransferMatrix.TwoSiteInteractingLayerOpenBoundaryWindow
import IsingModel.TransferMatrix.LayerOpenTwoMarkedSpectralDecay

/-!
# Two-site interacting open cross-transverse-site decay discharge

This file completes the cross-transverse-site (`x ≠ y`) analogue of the
interacting `K2` open-boundary discharge.  It bounds the open-slab correlation
`⟨σ_(left,x) · σ_(left+sep,y)⟩` for arbitrary transverse sites `x`, `y : Fin 2`
by the two-marked spectral prefactor divided by the spectral partition
prefactor, times `theta ^ sep`.

The same flip-even boundary vector, simple spectrum and signed-positive
dominant column inputs as the same-site route are reused.  Only the
central-channel cancellation is twinned: for two marks it suffices that the
*left* mark `layerSpinAt x` is flip-odd against the flip-even top column, so the
right mark `layerSpinAt y` plays no role in the dominant-channel vanishing.

The results are finite.  They do not prove a closed-form decay rate, a
thermodynamic limit, or final hyperplane exponential decay.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

open Matrix

/-- The interacting `K2` two-marked central dominant channel vanishes from
flip-parity: the *left* mark `layerSpinAt x` is flip-odd against the flip-even
top column, so the dominant-channel coefficient is zero independently of the
right mark `layerSpinAt y`. -/
theorem twoSiteInteractingLayer_twoMarkedCentral_zero_of_layerSpinAt_flipParity
    (p : IsingParams ℝ) (hp : p.h = 0) (hβJ : 0 < p.β * p.J) (x y : Fin 2) :
    ∀ i l,
      (twoSiteInteractingLayerOrthogonalSpectralData p hp).boundaryCoordinates
          (layerOpenBalancedBoundaryVector
            (layerInternalWeight (SimpleGraph.completeGraph (Fin 2)) p)) i *
        (twoSiteInteractingLayerOrthogonalSpectralData p hp).markedMatrix
          (layerSpinAt x) i twoSiteInteractingLayerTop *
        (twoSiteInteractingLayerOrthogonalSpectralData p hp).markedMatrix
          (layerSpinAt y) twoSiteInteractingLayerTop l *
        (twoSiteInteractingLayerOrthogonalSpectralData p hp).boundaryCoordinates
          (layerOpenBalancedBoundaryVector
            (layerInternalWeight (SimpleGraph.completeGraph (Fin 2)) p)) l = 0 :=
  let E := twoSiteInteractingLayerOrthogonalSpectralData p hp
  let u := layerInternalWeight (SimpleGraph.completeGraph (Fin 2)) p
  let k := layerTransitionWeight (layerIdentityTransitionPairs (Fin 2)) p
  let hu_flip := layerInternalWeight_flip_of_h_zero (SimpleGraph.completeGraph (Fin 2)) p hp
  let hk_flip := layerTransitionWeight_flip_flip (layerIdentityTransitionPairs (Fin 2)) p
  -- left mark flip-odd kills the dominant channel; right mark is a spectator
  E.boundaryTwoMarkedCentral_zero_of_equiv_evenBoundary_columnParity
    (layerSpinAt x) (layerSpinAt y)
    (layerOpenBalancedBoundaryVector u) (layerOpenBalancedBoundaryVector u)
    twoSiteInteractingLayerTop (layerStateFlipEquiv (Fin 2))
    (fun ω => layerSpinAt_flip x ω)
    (layerOpenBalancedBoundaryVector_flip_of_u_flip u hu_flip)
    (layerSymmetricTransfer_signedPositiveColumn_flip_even u k
      (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _) hu_flip hk_flip
      E twoSiteInteractingLayerTop
      (twoSiteInteractingLayerOrthogonalSpectralData_top_signedPositiveColumn p hp))
    (layerSymmetricTransfer_columnFlipParity_of_columnSimple u k hu_flip hk_flip E
      (E.columnSimpleEigenspaces_of_simpleSpectrum
        (twoSiteInteractingLayerOrthogonalSpectralData_simpleSpectrum p hp hβJ)))

open RealOrthogonalSpectralData in
/-- First unconditional finite *interacting* transverse-edge open-slab
*cross*-transverse-site correlation bound, in prefactor form with decay
parameter `theta = flipOdd / top`.  The same-site bound is the `x = y` case. -/
theorem correlation_twoSiteInteractingLayerOpenSlabGraph_cross_abs_le_of_simpleSpectrum
    (p : IsingParams ℝ) (hp : p.h = 0) (hβJ : 0 < p.β * p.J)
    (x y : Fin 2) (left sep right : ℕ) (hsep : 0 < sep) :
    |correlation
        (layerOpenSlabGraph (S := Fin 2) (SimpleGraph.completeGraph (Fin 2))
          (layerIdentityTransitionPairs (Fin 2)) (left + sep + right)) p
        ({Prod.mk (layerOpenLeftIndex left sep right) x,
          Prod.mk (layerOpenRightIndex left sep right) y} :
            Finset (LayerOpenSlabSite (left + sep + right) (Fin 2)))|
      ≤
        ((twoSiteInteractingLayerOrthogonalSpectralData p hp).boundaryTwoMarkedSpectralPrefactor
            (layerSpinAt x) (layerSpinAt y)
            (layerOpenBalancedBoundaryVector
              (layerInternalWeight (SimpleGraph.completeGraph (Fin 2)) p))
            (layerOpenBalancedBoundaryVector
              (layerInternalWeight (SimpleGraph.completeGraph (Fin 2)) p)) /
          (twoSiteInteractingLayerOrthogonalSpectralData p hp).boundarySpectralPartitionPrefactor
            (layerOpenBalancedBoundaryVector
              (layerInternalWeight (SimpleGraph.completeGraph (Fin 2)) p))
            twoSiteInteractingLayerTop (twoSiteInteractingTheta (p.β * p.J))) *
          twoSiteInteractingTheta (p.β * p.J) ^ sep := by
  have htheta_cap := twoSiteInteractingLayer_theta_lt_cap p hp hβJ
  have hwindow_cap_pos :
      0 < layerOpenBoundarySpectralWindowCap
        (layerInternalWeight (SimpleGraph.completeGraph (Fin 2)) p)
        (twoSiteInteractingLayerOrthogonalSpectralData p hp)
        twoSiteInteractingLayerTop :=
    layerOpenBoundarySpectralWindowCap_pos_of_signedPositiveColumn
      (layerInternalWeight (SimpleGraph.completeGraph (Fin 2)) p)
      (fun _ => Real.exp_pos _)
      (twoSiteInteractingLayerOrthogonalSpectralData p hp)
      twoSiteInteractingLayerTop
      (twoSiteInteractingLayerOrthogonalSpectralData_top_signedPositiveColumn p hp)
  have htop_sq_pos :
      0 < ((twoSiteInteractingLayerOrthogonalSpectralData p hp).boundaryCoordinates
        (layerOpenBalancedBoundaryVector
          (layerInternalWeight (SimpleGraph.completeGraph (Fin 2)) p))
        twoSiteInteractingLayerTop) ^ 2 :=
    layerOpenBoundaryCoordinate_sq_pos_of_signedPositiveColumn
      (layerInternalWeight (SimpleGraph.completeGraph (Fin 2)) p)
      (fun _ => Real.exp_pos _)
      (twoSiteInteractingLayerOrthogonalSpectralData p hp)
      twoSiteInteractingLayerTop
      (twoSiteInteractingLayerOrthogonalSpectralData_top_signedPositiveColumn p hp)
  have hpart_pos :
      0 < (twoSiteInteractingLayerOrthogonalSpectralData p hp).boundarySpectralPartitionPrefactor
        (layerOpenBalancedBoundaryVector
          (layerInternalWeight (SimpleGraph.completeGraph (Fin 2)) p))
        twoSiteInteractingLayerTop (twoSiteInteractingTheta (p.β * p.J)) :=
    boundarySpectralPartitionPrefactor_pos_of_lt_boundarySpectralWindowCap
      (twoSiteInteractingLayerOrthogonalSpectralData p hp)
      (layerOpenBalancedBoundaryVector
        (layerInternalWeight (SimpleGraph.completeGraph (Fin 2)) p))
      twoSiteInteractingLayerTop htop_sq_pos htheta_cap
  exact
    correlation_layerOpenSlabGraph_two_transverse_abs_le_of_boundarySpectralDenominator
      (SimpleGraph.completeGraph (Fin 2)) (layerIdentityTransitionPairs (Fin 2)) p x y
      (twoSiteInteractingLayerOrthogonalSpectralData p hp) twoSiteInteractingLayerTop
      ((twoSiteInteractingLayerOrthogonalSpectralData p hp).eigenvalue
        twoSiteInteractingLayerTop)
      (twoSiteInteractingTheta (p.β * p.J))
      ((twoSiteInteractingLayerOrthogonalSpectralData p hp).eigenvalue_pos_of_signedPositiveColumn
        (layerSymmetricTransferMatrix_entrywisePositive
          (layerInternalWeight (SimpleGraph.completeGraph (Fin 2)) p)
          (layerTransitionWeight (layerIdentityTransitionPairs (Fin 2)) p)
          (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _))
        twoSiteInteractingLayerTop
        (twoSiteInteractingLayerOrthogonalSpectralData_top_signedPositiveColumn p hp))
      (twoSiteInteractingTheta_nonneg hβJ)
      (twoSiteInteractingTheta_lt_one (p.β * p.J)) hpart_pos rfl
      (twoSiteInteractingLayerSpectralWindow_theta p hp hβJ)
      (twoSiteInteractingLayer_twoMarkedCentral_zero_of_layerSpinAt_flipParity p hp hβJ x y)
      left sep right hsep

end TransferMatrix

end IsingModel

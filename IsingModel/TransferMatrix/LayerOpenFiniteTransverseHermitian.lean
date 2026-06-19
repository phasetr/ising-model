import IsingModel.TransferMatrix.LayerOpenBoundaryWindowSimple
import IsingModel.TransferMatrix.LayerOpenSimpleSpectrum
import IsingModel.TransferMatrix.LayerPerronExistence

/-!
# Finite arbitrary transverse layer open-slab decay via Hermitian spectral data

This file generalizes the open-boundary same-transverse-site decay consumers
from the closed-form `Fin 2` (`K2`) transverse fiber to an **arbitrary finite
transverse layer** `S`.  Instead of an explicit closed-form diagonalization, the
spectral data is supplied generically by the real spectral theorem packaging
`layerSymmetricTransferOrthogonalSpectralData` for the symmetric balanced
transfer matrix, and the decay parameter is fixed to the canonical maximal-index
subdominant ratio `RealOrthogonalSpectralData.subdominantRatio_maxEigenIndex`.

Because the balanced transfer matrix is entrywise positive, the maximal column is
automatically signed-positive (finite Perron-facing orientation) and the
canonical subdominant ratio automatically bounds every non-maximal eigenvalue in
absolute value and is strictly below one.  Beyond the zero-field condition
`p.h = 0`, the only remaining user inputs are:

* `hk_symm`: symmetry of the transition weight (needed for the spectral theorem);
* `hwindow`: the canonical subdominant ratio lies strictly below the open
  boundary spectral-window cap (the quantitative gap, discharged uniformly at
  high temperature in a later phase);
* `hsimple` / `hsimple_spectrum`: a columnwise-simple-eigenspace (or simple
  spectrum) input, supplying the flip-parity central cancellation.

The results are finite and conditional on the boundary-window gap and the
parity input.  They do not construct the window uniformly, prove a thermodynamic
limit, or prove final hyperplane exponential decay.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

/-! ## The generic Hermitian layer spectral data -/

/-- The generic real orthogonal spectral data for the symmetric balanced
transfer matrix of an arbitrary finite transverse layer `S`, supplied by the
real spectral theorem.  This replaces the closed-form `Fin 2` diagonalization. -/
noncomputable def finiteTransverseHermitianData
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ)
    (hk_symm : ∀ ω η,
      layerTransitionWeight transitionPairs p ω η =
        layerTransitionWeight transitionPairs p η ω) :
    RealOrthogonalSpectralData
      (layerSymmetricTransferMatrix
        (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)) :=
  layerSymmetricTransferOrthogonalSpectralData
    (layerInternalWeight H p) (layerTransitionWeight transitionPairs p) hk_symm

/-- The balanced transfer matrix of an arbitrary finite transverse layer is
entrywise positive. -/
theorem finiteTransverseHermitian_entrywisePositive
    {S : Type*} [Fintype S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ) :
    MatrixEntrywisePositive
      (layerSymmetricTransferMatrix
        (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)) :=
  layerSymmetricTransferMatrix_entrywisePositive
    (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)
    (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _)

/-- The canonical maximal-index subdominant decay ratio of the generic Hermitian
layer spectral data for an arbitrary finite transverse layer. -/
noncomputable def finiteTransverseHermitianRatio
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ)
    (hk_symm : ∀ ω η,
      layerTransitionWeight transitionPairs p ω η =
        layerTransitionWeight transitionPairs p η ω) : ℝ :=
  (finiteTransverseHermitianData H transitionPairs p hk_symm).subdominantRatio_maxEigenIndex
    (finiteTransverseHermitian_entrywisePositive H transitionPairs p)

/-- The canonical maximal-index subdominant decay ratio is strictly below one. -/
theorem finiteTransverseHermitianRatio_lt_one
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ)
    (hk_symm : ∀ ω η,
      layerTransitionWeight transitionPairs p ω η =
        layerTransitionWeight transitionPairs p η ω) :
    finiteTransverseHermitianRatio H transitionPairs p hk_symm < 1 :=
  (finiteTransverseHermitianData H transitionPairs p hk_symm).subdominantRatio_maxEigenIndex_lt_one
    (finiteTransverseHermitian_entrywisePositive H transitionPairs p)

/-- The canonical maximal-index subdominant decay ratio is nonnegative. -/
theorem finiteTransverseHermitianRatio_nonneg
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ)
    (hk_symm : ∀ ω η,
      layerTransitionWeight transitionPairs p ω η =
        layerTransitionWeight transitionPairs p η ω) :
    0 ≤ finiteTransverseHermitianRatio H transitionPairs p hk_symm :=
  (finiteTransverseHermitianData H transitionPairs p hk_symm).subdominantRatio_maxEigenIndex_nonneg
    (finiteTransverseHermitian_entrywisePositive H transitionPairs p)

/-! ## Arbitrary finite transverse layer open-slab decay -/

/-- Finite open-slab same-transverse-site correlation decay for an **arbitrary
finite transverse layer** `S`, from generic Hermitian spectral data, the
canonical maximal-index subdominant ratio, the open boundary-window gap, and a
columnwise-simple-eigenspace parity input.  The subdominant absolute bound and
signed-positive maximal column are automatic from entrywise positivity. -/
theorem
    correlation_layerOpenSlabGraph_abs_le_of_hermitianCanonicalRatioSimpleParityWindow
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ) (hp : p.h = 0) (x : S)
    (hk_symm : ∀ ω η,
      layerTransitionWeight transitionPairs p ω η =
        layerTransitionWeight transitionPairs p η ω)
    (hwindow :
      finiteTransverseHermitianRatio H transitionPairs p hk_symm <
        layerOpenBoundarySpectralWindowCap (layerInternalWeight H p)
          (finiteTransverseHermitianData H transitionPairs p hk_symm)
          (finiteTransverseHermitianData H transitionPairs p hk_symm).maxEigenIndex)
    (hsimple :
      (finiteTransverseHermitianData H transitionPairs p hk_symm).ColumnSimpleEigenspaces)
    (left sep right : ℕ) (hsep : 0 < sep) :
    |correlation (layerOpenSlabGraph (S := S) H transitionPairs (left + sep + right)) p
        ({Prod.mk (layerOpenLeftIndex left sep right) x,
          Prod.mk (layerOpenRightIndex left sep right) x} :
            Finset (LayerOpenSlabSite (left + sep + right) S))|
      ≤
        ((finiteTransverseHermitianData H transitionPairs p hk_symm).boundaryMarkedSpectralPrefactor
            (layerSpinAt x)
            (layerOpenBalancedBoundaryVector (layerInternalWeight H p))
            (layerOpenBalancedBoundaryVector (layerInternalWeight H p)) /
          (finiteTransverseHermitianData H transitionPairs p
              hk_symm).boundarySpectralPartitionPrefactor
            (layerOpenBalancedBoundaryVector (layerInternalWeight H p))
            (finiteTransverseHermitianData H transitionPairs p hk_symm).maxEigenIndex
            (finiteTransverseHermitianRatio H transitionPairs p hk_symm)) *
          finiteTransverseHermitianRatio H transitionPairs p hk_symm ^ sep :=
  correlation_layerOpenSlabGraph_abs_le_of_maxEigenIndexSimpleParity_boundaryWindow
    H transitionPairs p hp x
    (finiteTransverseHermitianData H transitionPairs p hk_symm)
    (finiteTransverseHermitianRatio H transitionPairs p hk_symm)
    (finiteTransverseHermitianRatio_nonneg H transitionPairs p hk_symm)
    hwindow
    (fun i hi =>
      (finiteTransverseHermitianData H transitionPairs p
          hk_symm).eigenvalue_abs_le_subdominantRatio_maxEigenIndex
        (finiteTransverseHermitian_entrywisePositive H transitionPairs p) i hi)
    hsimple left sep right hsep

/-- Finite open-slab same-transverse-site correlation decay for an arbitrary
finite transverse layer `S`, with the parity input strengthened to a simple
spectrum (distinct eigenvalues).  Columnwise simple eigenspaces follow. -/
theorem
    correlation_layerOpenSlabGraph_abs_le_of_hermitianCanonicalRatioSimpleSpectrumWindow
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ) (hp : p.h = 0) (x : S)
    (hk_symm : ∀ ω η,
      layerTransitionWeight transitionPairs p ω η =
        layerTransitionWeight transitionPairs p η ω)
    (hwindow :
      finiteTransverseHermitianRatio H transitionPairs p hk_symm <
        layerOpenBoundarySpectralWindowCap (layerInternalWeight H p)
          (finiteTransverseHermitianData H transitionPairs p hk_symm)
          (finiteTransverseHermitianData H transitionPairs p hk_symm).maxEigenIndex)
    (hsimple_spectrum :
      (finiteTransverseHermitianData H transitionPairs p hk_symm).SimpleSpectrum)
    (left sep right : ℕ) (hsep : 0 < sep) :
    |correlation (layerOpenSlabGraph (S := S) H transitionPairs (left + sep + right)) p
        ({Prod.mk (layerOpenLeftIndex left sep right) x,
          Prod.mk (layerOpenRightIndex left sep right) x} :
            Finset (LayerOpenSlabSite (left + sep + right) S))|
      ≤
        ((finiteTransverseHermitianData H transitionPairs p hk_symm).boundaryMarkedSpectralPrefactor
            (layerSpinAt x)
            (layerOpenBalancedBoundaryVector (layerInternalWeight H p))
            (layerOpenBalancedBoundaryVector (layerInternalWeight H p)) /
          (finiteTransverseHermitianData H transitionPairs p
              hk_symm).boundarySpectralPartitionPrefactor
            (layerOpenBalancedBoundaryVector (layerInternalWeight H p))
            (finiteTransverseHermitianData H transitionPairs p hk_symm).maxEigenIndex
            (finiteTransverseHermitianRatio H transitionPairs p hk_symm)) *
          finiteTransverseHermitianRatio H transitionPairs p hk_symm ^ sep :=
  correlation_layerOpenSlabGraph_abs_le_of_hermitianCanonicalRatioSimpleParityWindow
    H transitionPairs p hp x hk_symm hwindow
    ((finiteTransverseHermitianData H transitionPairs p
        hk_symm).columnSimpleEigenspaces_of_simpleSpectrum hsimple_spectrum)
    left sep right hsep

/-! ## Cubic transverse layer specialization -/

/-- The cubic transverse layer (`cubicLayerGraph d R`) inherits the arbitrary
finite transverse layer open-slab decay from generic Hermitian spectral data and
the canonical maximal-index subdominant ratio, with a columnwise-simple-eigenspace
parity input. -/
theorem correlation_cubicLayerOpenSlabGraph_abs_le_of_hermitianCanonicalRatioSimpleParityWindow
    (d R : ℕ) (p : IsingParams ℝ) (hp : p.h = 0) (x : CubicLayerSite d R)
    (hk_symm : ∀ ω η,
      layerTransitionWeight (cubicLayerTransitionPairs d R) p ω η =
        layerTransitionWeight (cubicLayerTransitionPairs d R) p η ω)
    (hwindow :
      finiteTransverseHermitianRatio (cubicLayerGraph d R)
          (cubicLayerTransitionPairs d R) p hk_symm <
        layerOpenBoundarySpectralWindowCap
          (layerInternalWeight (cubicLayerGraph d R) p)
          (finiteTransverseHermitianData (cubicLayerGraph d R)
            (cubicLayerTransitionPairs d R) p hk_symm)
          (finiteTransverseHermitianData (cubicLayerGraph d R)
            (cubicLayerTransitionPairs d R) p hk_symm).maxEigenIndex)
    (hsimple :
      (finiteTransverseHermitianData (cubicLayerGraph d R)
        (cubicLayerTransitionPairs d R) p hk_symm).ColumnSimpleEigenspaces)
    (left sep right : ℕ) (hsep : 0 < sep) :
    |correlation (layerOpenSlabGraph (S := CubicLayerSite d R)
          (cubicLayerGraph d R) (cubicLayerTransitionPairs d R)
          (left + sep + right)) p
        ({Prod.mk (layerOpenLeftIndex left sep right) x,
          Prod.mk (layerOpenRightIndex left sep right) x} :
            Finset (LayerOpenSlabSite (left + sep + right) (CubicLayerSite d R)))|
      ≤
        ((finiteTransverseHermitianData (cubicLayerGraph d R)
              (cubicLayerTransitionPairs d R) p hk_symm).boundaryMarkedSpectralPrefactor
            (layerSpinAt x)
            (layerOpenBalancedBoundaryVector (layerInternalWeight (cubicLayerGraph d R) p))
            (layerOpenBalancedBoundaryVector (layerInternalWeight (cubicLayerGraph d R) p)) /
          (finiteTransverseHermitianData (cubicLayerGraph d R)
              (cubicLayerTransitionPairs d R) p hk_symm).boundarySpectralPartitionPrefactor
            (layerOpenBalancedBoundaryVector (layerInternalWeight (cubicLayerGraph d R) p))
            (finiteTransverseHermitianData (cubicLayerGraph d R)
              (cubicLayerTransitionPairs d R) p hk_symm).maxEigenIndex
            (finiteTransverseHermitianRatio (cubicLayerGraph d R)
              (cubicLayerTransitionPairs d R) p hk_symm)) *
          finiteTransverseHermitianRatio (cubicLayerGraph d R)
            (cubicLayerTransitionPairs d R) p hk_symm ^ sep :=
  correlation_layerOpenSlabGraph_abs_le_of_hermitianCanonicalRatioSimpleParityWindow
    (cubicLayerGraph d R) (cubicLayerTransitionPairs d R) p hp x hk_symm hwindow
    hsimple left sep right hsep

end TransferMatrix

end IsingModel

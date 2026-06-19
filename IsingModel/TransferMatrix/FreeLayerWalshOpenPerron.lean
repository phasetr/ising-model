import IsingModel.TransferMatrix.FreeLayerWalshSpectralWindow
import IsingModel.TransferMatrix.LayerOpenPerron

/-!
# Free-layer Walsh inputs for the open-boundary Perron route

This file specializes the open-boundary flip-parity Perron constructors to the
finite zero-field free layer with the explicit Walsh spectral basis.  The
Walsh basis supplies the concrete flip-parity decomposition and the top column
is signed-positive.  For the free open boundary, the balanced boundary vector
has only the top Walsh coordinate, so the open denominator prefactor smallness
condition is discharged directly.

The results are finite and free-layer only.  They do not claim a physical
interacting cubic spectral window, a thermodynamic limit, or final hyperplane
exponential decay.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

open scoped BigOperators

variable {S : Type*} [Fintype S] [DecidableEq S]

/-! ## Free open-boundary Walsh coordinates -/

omit [DecidableEq S] in
/-- At zero field, the balanced open boundary vector of the free layer is the
constant vector `1`. -/
theorem layerOpenBalancedBoundaryVector_bot_h_zero
    (p : IsingParams ℝ) (hp : p.h = 0) (ω : LayerState S) :
    layerOpenBalancedBoundaryVector (layerInternalWeight (⊥ : SimpleGraph S) p) ω = 1 := by
  simp [layerOpenBalancedBoundaryVector, layerInternalWeight_bot_h_zero p hp]

/-- In the zero-field free layer, the open boundary vector has no spectral
coordinate in any non-top Walsh mode. -/
theorem freeLayerPhysical_boundaryCoordinates_nonTop_zero
    (p : IsingParams ℝ) (hp : p.h = 0)
    {i : LayerState S} (hi : i ≠ freeLayerWalshTop (S := S)) :
    (freeLayerPhysicalOrthogonalSpectralData (S := S) p hp).boundaryCoordinates
      (layerOpenBalancedBoundaryVector
        (layerInternalWeight (⊥ : SimpleGraph S) p)) i = 0 := by
  classical
  let A : Finset S := layerStateDownSet i
  have hA_nonempty : A.Nonempty :=
    layerStateDownSet_nonempty_of_ne_freeLayerWalshTop (S := S) hi
  rw [RealOrthogonalSpectralData.boundaryCoordinates]
  calc
    ∑ x : LayerState S,
        layerOpenBalancedBoundaryVector
            (layerInternalWeight (⊥ : SimpleGraph S) p) x *
          (freeLayerPhysicalOrthogonalSpectralData (S := S) p hp).changeOfBasis x i
        =
        (Fintype.card (LayerState S) : ℝ)⁻¹.sqrt *
          ∑ x : LayerState S, spinProduct A x := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro x _hx
          simp [A, freeLayerPhysicalOrthogonalSpectralData,
            freeLayerTransferOrthogonalSpectralData, freeLayerWalshMatrix,
            freeLayerWalshColumn, layerOpenBalancedBoundaryVector_bot_h_zero p hp]
    _ = 0 := by
          rw [sum_config_spinProduct_eq_zero A hA_nonempty, mul_zero]

/-- For the zero-field free layer, the open boundary denominator prefactor
smallness condition holds for `theta = tanh (βJ)`. -/
theorem freeLayerPhysical_boundaryPrefactor_small_tanh
    (p : IsingParams ℝ) (hp : p.h = 0) :
    (∑ i ∈ Finset.univ.erase (freeLayerWalshTop (S := S)),
        ((freeLayerPhysicalOrthogonalSpectralData (S := S) p hp).boundaryCoordinates
          (layerOpenBalancedBoundaryVector
            (layerInternalWeight (⊥ : SimpleGraph S) p)) i) ^ 2) *
        Real.tanh (p.β * p.J)
      <
      ((freeLayerPhysicalOrthogonalSpectralData (S := S) p hp).boundaryCoordinates
        (layerOpenBalancedBoundaryVector
          (layerInternalWeight (⊥ : SimpleGraph S) p))
        (freeLayerWalshTop (S := S))) ^ 2 := by
  classical
  have hsum_zero :
      ∑ i ∈ Finset.univ.erase (freeLayerWalshTop (S := S)),
        ((freeLayerPhysicalOrthogonalSpectralData (S := S) p hp).boundaryCoordinates
          (layerOpenBalancedBoundaryVector
            (layerInternalWeight (⊥ : SimpleGraph S) p)) i) ^ 2 = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    have hi_ne : i ≠ freeLayerWalshTop (S := S) := (Finset.mem_erase.mp hi).1
    rw [freeLayerPhysical_boundaryCoordinates_nonTop_zero (S := S) p hp hi_ne]
    ring
  rw [hsum_zero, zero_mul]
  exact
    layerOpenBoundaryCoordinate_sq_pos_of_signedPositiveColumn
      (layerInternalWeight (⊥ : SimpleGraph S) p)
      (fun _ => Real.exp_pos _)
      (freeLayerPhysicalOrthogonalSpectralData (S := S) p hp)
      (freeLayerWalshTop (S := S))
      (freeLayerPhysicalOrthogonalSpectralData_top_signedPositiveColumn
        (S := S) p hp)

/-! ## Free open-boundary certificate and consumer -/

/-- Finite zero-field free-layer open min-gap certificate with the explicit
Walsh spectral data and decay rate `tanh (βJ)`. -/
noncomputable def freeLayerOpenMinGapCertificate_tanh
    (p : IsingParams ℝ) (hp : p.h = 0) (hβJ : 0 < p.β * p.J) (x : S) :
    LayerOpenMinSpectralGapCertificate
      (layerInternalWeight (⊥ : SimpleGraph S) p)
      (layerTransitionWeight (layerIdentityTransitionPairs S) p)
      (layerSpinAt x) := by
  let spec := freeLayerPhysicalOrthogonalSpectralData (S := S) p hp
  let top : LayerState S := freeLayerWalshTop (S := S)
  refine
    layerOpenMinGapCert_of_layerSubdominant_signedPositiveFlipParitySpin
      (⊥ : SimpleGraph S) (layerIdentityTransitionPairs S) p hp x
      spec top (Real.tanh (p.β * p.J)) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [Real.tanh_eq_sinh_div_cosh]
    exact le_of_lt (div_pos (Real.sinh_pos_iff.mpr hβJ) (Real.cosh_pos _))
  · exact Real.tanh_lt_one (p.β * p.J)
  · simpa [spec, top] using
      freeLayerPhysical_boundaryPrefactor_small_tanh (S := S) p hp
  · intro i hi
    simpa [spec, top, freeLayerPhysicalOrthogonalSpectralData,
      freeLayerTransferOrthogonalSpectralData, freeLayerWalshEigenvalue_top] using
        freeLayerWalshSpectralWindow_tanh (S := S) (le_of_lt hβJ) i hi
  · simpa [spec] using
      freeLayerPhysicalOrthogonalSpectralData_columnFlipParity (S := S) p hp
  · simpa [spec, top] using
      freeLayerPhysicalOrthogonalSpectralData_top_signedPositiveColumn
        (S := S) p hp

/-- Project-level finite open-slab same-transverse-site correlation decay for
the zero-field free layer, with explicit Walsh spectral data and rate
`tanh (βJ)`. -/
theorem correlation_freeLayerOpenSlabGraph_same_transverse_abs_le_tanh
    (p : IsingParams ℝ) (hp : p.h = 0) (hβJ : 0 < p.β * p.J) (x : S)
    (left sep right : ℕ) (hsep : 0 < sep) :
    |correlation
      (layerOpenSlabGraph (S := S) (⊥ : SimpleGraph S)
        (layerIdentityTransitionPairs S) (left + sep + right)) p
      ({Prod.mk (layerOpenLeftIndex left sep right) x,
        Prod.mk (layerOpenRightIndex left sep right) x} :
          Finset (LayerOpenSlabSite (left + sep + right) S))|
      ≤
        ((freeLayerPhysicalOrthogonalSpectralData (S := S) p hp).boundaryMarkedSpectralPrefactor
            (layerSpinAt x)
            (layerOpenBalancedBoundaryVector
              (layerInternalWeight (⊥ : SimpleGraph S) p))
            (layerOpenBalancedBoundaryVector
              (layerInternalWeight (⊥ : SimpleGraph S) p)) /
          (freeLayerPhysicalOrthogonalSpectralData (S := S) p hp).boundarySpectralPartitionPrefactor
              (layerOpenBalancedBoundaryVector
                (layerInternalWeight (⊥ : SimpleGraph S) p))
              (freeLayerWalshTop (S := S)) (Real.tanh (p.β * p.J))) *
          Real.tanh (p.β * p.J) ^ sep := by
  let cert :=
    freeLayerOpenMinGapCertificate_tanh (S := S) p hp hβJ x
  simpa [cert] using
    correlation_layerOpenSlabGraph_same_transverse_abs_le_of_openMinSpectralGapCertificate
      (S := S) (⊥ : SimpleGraph S) (layerIdentityTransitionPairs S) p x
      cert left sep right hsep

end TransferMatrix

end IsingModel

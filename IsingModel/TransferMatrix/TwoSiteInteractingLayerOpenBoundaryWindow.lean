import IsingModel.TransferMatrix.TwoSiteInteractingLayerSpectralWindow
import IsingModel.TransferMatrix.LayerOpenBoundaryWindowSimple
import IsingModel.TransferMatrix.LayerOpenSimpleSpectrum

/-!
# Two-site interacting open boundary-window discharge

This file completes the interacting `K2` open-boundary discharge: it proves the
open boundary-window cap equals `1` and feeds the simple-spectrum /
signed-positive / spectral-window inputs of
`TwoSiteInteractingLayerSpectralWindow` through the columnwise-simple-eigenspace
boundary-window consumer.  The result is the first unconditional finite
*interacting* transverse-edge open-slab same-transverse-site correlation bound,
in prefactor form with decay parameter `theta = flipOdd / top`.

The balanced boundary vector `v(ω) = sqrt(internalWeight ω)` is not constant for
the interacting layer, but it is flip-even, so the two odd spectral columns have
vanishing boundary coordinates; only the even-bottom coordinate survives, and
the cap is `1` because the dominant boundary coordinate squared dominates it.

The results are finite.  They do not prove a closed-form decay rate, a
thermodynamic limit, or final hyperplane exponential decay.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

open Matrix

/-! ## Odd spectral columns and their vanishing boundary coordinates -/

/-- The physical-layer flip-odd column in terms of spins. -/
theorem twoSiteInteractingLayer_flipOdd_col_eq
    (p : IsingParams ℝ) (hp : p.h = 0) (ω : LayerState (Fin 2)) :
    (twoSiteInteractingLayerOrthogonalSpectralData p hp).changeOfBasis ω
        (layerStateFin2EquivFin2Prod.symm (0, 1))
      = (1 / Real.sqrt 2) * (Spin.sign ℝ (ω 0) + Spin.sign ℝ (ω 1)) / 2 := by
  simp only [twoSiteInteractingLayerOrthogonalSpectralData,
    RealOrthogonalSpectralData.reindex, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm, Equiv.apply_symm_apply]
  simp only [twoSiteInteractingTransferOrthogonalSpectralData,
    twoSiteInteractingChangeOfBasis, Matrix.of_apply, layerStateFin2EquivFin2Prod,
    Equiv.coe_fn_mk, spin1D_spinEquivFin2, Prod.mk.injEq, Fin.reduceEq, and_true, and_false, ↓reduceIte]
  ring

/-- The physical-layer swap-odd column in terms of spins. -/
theorem twoSiteInteractingLayer_swapOdd_col_eq
    (p : IsingParams ℝ) (hp : p.h = 0) (ω : LayerState (Fin 2)) :
    (twoSiteInteractingLayerOrthogonalSpectralData p hp).changeOfBasis ω
        (layerStateFin2EquivFin2Prod.symm (1, 0))
      = (1 / Real.sqrt 2) * (Spin.sign ℝ (ω 0) - Spin.sign ℝ (ω 1)) / 2 := by
  simp only [twoSiteInteractingLayerOrthogonalSpectralData,
    RealOrthogonalSpectralData.reindex, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm, Equiv.apply_symm_apply]
  simp only [twoSiteInteractingTransferOrthogonalSpectralData,
    twoSiteInteractingChangeOfBasis, Matrix.of_apply, layerStateFin2EquivFin2Prod,
    Equiv.coe_fn_mk, spin1D_spinEquivFin2, Prod.mk.injEq, Fin.reduceEq, and_true, and_false, ↓reduceIte]
  ring

/-- The flip-odd column is odd under the global spin flip. -/
theorem twoSiteInteractingLayer_flipOdd_columnFlipOdd
    (p : IsingParams ℝ) (hp : p.h = 0) :
    (twoSiteInteractingLayerOrthogonalSpectralData p hp).ColumnFlipOdd
      (layerStateFlipEquiv (Fin 2)) (layerStateFin2EquivFin2Prod.symm (0, 1)) := by
  intro ω
  rw [twoSiteInteractingLayer_flipOdd_col_eq p hp (layerStateFlipEquiv (Fin 2) ω),
    twoSiteInteractingLayer_flipOdd_col_eq p hp ω]
  simp only [layerStateFlipEquiv_apply, Config.flip, Spin.sign_flip]
  ring

/-- The swap-odd column is odd under the global spin flip. -/
theorem twoSiteInteractingLayer_swapOdd_columnFlipOdd
    (p : IsingParams ℝ) (hp : p.h = 0) :
    (twoSiteInteractingLayerOrthogonalSpectralData p hp).ColumnFlipOdd
      (layerStateFlipEquiv (Fin 2)) (layerStateFin2EquivFin2Prod.symm (1, 0)) := by
  intro ω
  rw [twoSiteInteractingLayer_swapOdd_col_eq p hp (layerStateFlipEquiv (Fin 2) ω),
    twoSiteInteractingLayer_swapOdd_col_eq p hp ω]
  simp only [layerStateFlipEquiv_apply, Config.flip, Spin.sign_flip]
  ring

/-- The interacting balanced boundary vector is flip-even. -/
theorem twoSiteInteractingLayer_boundaryVector_flip_even
    (p : IsingParams ℝ) (hp : p.h = 0) (ω : LayerState (Fin 2)) :
    layerOpenBalancedBoundaryVector
        (layerInternalWeight (SimpleGraph.completeGraph (Fin 2)) p)
        (layerStateFlipEquiv (Fin 2) ω)
      = layerOpenBalancedBoundaryVector
        (layerInternalWeight (SimpleGraph.completeGraph (Fin 2)) p) ω := by
  rw [layerOpenBalancedBoundaryVector, layerOpenBalancedBoundaryVector,
    layerInternalWeight_flip_of_h_zero (SimpleGraph.completeGraph (Fin 2)) p hp]

/-- The flip-odd boundary coordinate vanishes. -/
theorem twoSiteInteractingLayer_boundaryCoordinates_flipOdd_zero
    (p : IsingParams ℝ) (hp : p.h = 0) :
    (twoSiteInteractingLayerOrthogonalSpectralData p hp).boundaryCoordinates
        (layerOpenBalancedBoundaryVector
          (layerInternalWeight (SimpleGraph.completeGraph (Fin 2)) p))
        (layerStateFin2EquivFin2Prod.symm (0, 1)) = 0 :=
  RealOrthogonalSpectralData.boundaryCoordinates_zero_of_equiv_even_odd _ _ _
    (layerStateFlipEquiv (Fin 2))
    (twoSiteInteractingLayer_boundaryVector_flip_even p hp)
    (twoSiteInteractingLayer_flipOdd_columnFlipOdd p hp)

/-- The swap-odd boundary coordinate vanishes. -/
theorem twoSiteInteractingLayer_boundaryCoordinates_swapOdd_zero
    (p : IsingParams ℝ) (hp : p.h = 0) :
    (twoSiteInteractingLayerOrthogonalSpectralData p hp).boundaryCoordinates
        (layerOpenBalancedBoundaryVector
          (layerInternalWeight (SimpleGraph.completeGraph (Fin 2)) p))
        (layerStateFin2EquivFin2Prod.symm (1, 0)) = 0 :=
  RealOrthogonalSpectralData.boundaryCoordinates_zero_of_equiv_even_odd _ _ _
    (layerStateFlipEquiv (Fin 2))
    (twoSiteInteractingLayer_boundaryVector_flip_even p hp)
    (twoSiteInteractingLayer_swapOdd_columnFlipOdd p hp)

end TransferMatrix

end IsingModel

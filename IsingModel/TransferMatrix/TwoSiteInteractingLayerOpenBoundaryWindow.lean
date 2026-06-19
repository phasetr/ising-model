import IsingModel.TransferMatrix.TwoSiteInteractingLayerSpectralWindow
import IsingModel.TransferMatrix.LayerOpenBoundaryWindowSimple
import IsingModel.TransferMatrix.LayerOpenSimpleSpectrum

/-!
# Two-site interacting open boundary-window discharge

This file completes the interacting `K2` open-boundary discharge: it proves the
decay parameter is strictly below the open boundary-window cap and feeds the
simple-spectrum / signed-positive / spectral-window inputs of
`TwoSiteInteractingLayerSpectralWindow` through the columnwise-simple-eigenspace
boundary-window consumer.  The result is the first unconditional finite
*interacting* transverse-edge open-slab same-transverse-site correlation bound,
in prefactor form with decay parameter `theta = flipOdd / top`.

The balanced boundary vector `v(ω) = sqrt(internalWeight ω)` is not constant for
the interacting layer, but it is flip-even, so the two odd spectral columns have
vanishing boundary coordinates; only the even-bottom coordinate survives, so the
off-top boundary mass equals the squared norm minus the squared top coordinate.
That mass is at most the squared top coordinate (the squared norm is at most
twice it), so the boundary-window cap is `1` and strictly exceeds `theta`.

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
    Equiv.coe_fn_mk, spin1D_spinEquivFin2, Prod.mk.injEq, Fin.reduceEq, and_true,
    and_false, ↓reduceIte]
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
    Equiv.coe_fn_mk, spin1D_spinEquivFin2, Prod.mk.injEq, Fin.reduceEq, and_true,
    and_false, ↓reduceIte]
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

/-! ## The surviving top boundary coordinate -/

/-- The balanced boundary vector in spin form. -/
theorem twoSiteInteractingLayer_boundaryVector_eq
    (p : IsingParams ℝ) (hp : p.h = 0) (ω : LayerState (Fin 2)) :
    layerOpenBalancedBoundaryVector
        (layerInternalWeight (SimpleGraph.completeGraph (Fin 2)) p) ω
      = Real.exp ((p.β * p.J) * (Spin.sign ℝ (ω 0) * Spin.sign ℝ (ω 1)) / 2) := by
  rw [layerOpenBalancedBoundaryVector, layerInternalWeight_completeGraph_fin2 p hp,
    ← Real.exp_half]

/-- The top rotation column of the physical layer in spin form. -/
theorem twoSiteInteractingLayer_top_col_eq
    (p : IsingParams ℝ) (hp : p.h = 0) (ω : LayerState (Fin 2)) :
    (twoSiteInteractingLayerOrthogonalSpectralData p hp).changeOfBasis ω
        twoSiteInteractingLayerTop
      = (1 / Real.sqrt 2) * ((twoSiteK2RotC (p.β * p.J) + twoSiteK2RotS (p.β * p.J))
          + (twoSiteK2RotC (p.β * p.J) - twoSiteK2RotS (p.β * p.J)) *
            (Spin.sign ℝ (ω 0) * Spin.sign ℝ (ω 1))) / 2 := by
  rw [twoSiteInteractingLayerTop]
  simp only [twoSiteInteractingLayerOrthogonalSpectralData,
    RealOrthogonalSpectralData.reindex, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm, Equiv.apply_symm_apply]
  simp only [twoSiteInteractingTransferOrthogonalSpectralData,
    twoSiteInteractingChangeOfBasis, Matrix.of_apply, layerStateFin2EquivFin2Prod,
    Equiv.coe_fn_mk, spin1D_spinEquivFin2, Prod.mk.injEq, Fin.reduceEq, and_true, and_false,
    ↓reduceIte]
  ring

/-- The spins of a reindexed layer state are the `spin1D` coordinates. -/
theorem twoSiteInteractingLayer_sign_symm (i : Fin 2 × Fin 2) :
    Spin.sign ℝ ((layerStateFin2EquivFin2Prod.symm i) 0) = spin1D i.1 ∧
    Spin.sign ℝ ((layerStateFin2EquivFin2Prod.symm i) 1) = spin1D i.2 := by
  constructor
  · simp only [layerStateFin2EquivFin2Prod, Equiv.coe_fn_symm_mk]
    rw [← spin1D_spinEquivFin2]; congr 1; simp
  · simp only [layerStateFin2EquivFin2Prod, Equiv.coe_fn_symm_mk]
    rw [← spin1D_spinEquivFin2]; congr 1; simp

/-- Explicit value of the surviving top boundary coordinate. -/
theorem twoSiteInteractingLayer_boundaryCoordinates_top
    (p : IsingParams ℝ) (hp : p.h = 0) :
    (twoSiteInteractingLayerOrthogonalSpectralData p hp).boundaryCoordinates
        (layerOpenBalancedBoundaryVector
          (layerInternalWeight (SimpleGraph.completeGraph (Fin 2)) p))
        twoSiteInteractingLayerTop
      = Real.sqrt 2 * (twoSiteK2RotC (p.β * p.J) * Real.exp ((p.β * p.J) / 2)
          + twoSiteK2RotS (p.β * p.J) * Real.exp (-(p.β * p.J) / 2)) := by
  rw [RealOrthogonalSpectralData.boundaryCoordinates]
  rw [← Equiv.sum_comp layerStateFin2EquivFin2Prod.symm
    (fun ω => layerOpenBalancedBoundaryVector
      (layerInternalWeight (SimpleGraph.completeGraph (Fin 2)) p) ω *
      (twoSiteInteractingLayerOrthogonalSpectralData p hp).changeOfBasis ω
        twoSiteInteractingLayerTop)]
  simp only [twoSiteInteractingLayer_boundaryVector_eq p hp,
    twoSiteInteractingLayer_top_col_eq p hp, (twoSiteInteractingLayer_sign_symm _).1,
    (twoSiteInteractingLayer_sign_symm _).2]
  have hd : (1 : ℝ) / Real.sqrt 2 = Real.sqrt 2 / 2 := by
    rw [div_eq_div_iff (ne_of_gt (Real.sqrt_pos.2 (by norm_num))) two_ne_zero, one_mul,
      Real.mul_self_sqrt (by norm_num)]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, spin1D, Matrix.cons_val_zero,
    Matrix.cons_val_one, mul_one, mul_neg, neg_neg, hd]
  ring

/-! ## Squared-norm, rest mass, and the unit boundary-window cap -/

/-- The even-sector gap is positive for `0 < βJ`. -/
theorem twoSiteK2Delta_pos {a : ℝ} (ha : 0 < a) : 0 < twoSiteK2Delta a := by
  rw [twoSiteK2Delta, twoSiteK2EvenA, twoSiteK2EvenB]
  have h1 : Real.exp a < Real.exp (3 * a) := Real.exp_lt_exp.mpr (by linarith)
  have h2 : Real.exp (-(3 * a)) < Real.exp (-a) := Real.exp_lt_exp.mpr (by linarith)
  linarith

set_option maxHeartbeats 1000000 in
-- The 4-state boundary-vector sum exceeds the default heartbeat budget.
/-- The squared norm of the balanced boundary vector. -/
theorem twoSiteInteractingLayer_vectorSqNorm
    (p : IsingParams ℝ) (hp : p.h = 0) :
    vectorSqNorm (layerOpenBalancedBoundaryVector
        (layerInternalWeight (SimpleGraph.completeGraph (Fin 2)) p))
      = 2 * Real.exp (p.β * p.J) + 2 * Real.exp (-(p.β * p.J)) := by
  have hv2 : ∀ ω : LayerState (Fin 2),
      layerOpenBalancedBoundaryVector
          (layerInternalWeight (SimpleGraph.completeGraph (Fin 2)) p) ω ^ 2
        = layerInternalWeight (SimpleGraph.completeGraph (Fin 2)) p ω := by
    intro ω
    rw [layerOpenBalancedBoundaryVector, Real.sq_sqrt]
    rw [layerInternalWeight_completeGraph_fin2 p hp]; exact (Real.exp_pos _).le
  rw [vectorSqNorm]
  simp only [hv2]
  rw [← Equiv.sum_comp layerStateFin2EquivFin2Prod.symm
    (fun ω => layerInternalWeight (SimpleGraph.completeGraph (Fin 2)) p ω)]
  simp only [layerInternalWeight_completeGraph_fin2 p hp,
    (twoSiteInteractingLayer_sign_symm _).1, (twoSiteInteractingLayer_sign_symm _).2,
    Fintype.sum_prod_type, Fin.sum_univ_two, spin1D, Matrix.cons_val_zero,
    Matrix.cons_val_one, mul_one, mul_neg_one]
  ring

set_option maxHeartbeats 1600000 in
-- The squared-coordinate algebra with the rotation identities exceeds the default budget.
/-- The squared norm is at most twice the squared top boundary coordinate. -/
theorem twoSiteInteractingLayer_vectorSqNorm_le_two_mul_top_sq
    (p : IsingParams ℝ) (hp : p.h = 0) (hβJ : 0 < p.β * p.J) :
    vectorSqNorm (layerOpenBalancedBoundaryVector
        (layerInternalWeight (SimpleGraph.completeGraph (Fin 2)) p))
      ≤ 2 * ((twoSiteInteractingLayerOrthogonalSpectralData p hp).boundaryCoordinates
        (layerOpenBalancedBoundaryVector
          (layerInternalWeight (SimpleGraph.completeGraph (Fin 2)) p))
        twoSiteInteractingLayerTop) ^ 2 := by
  set a := p.β * p.J with ha_def
  rw [twoSiteInteractingLayer_vectorSqNorm p hp,
    twoSiteInteractingLayer_boundaryCoordinates_top p hp]
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hE2 : Real.exp (a / 2) ^ 2 = Real.exp a := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hEp2 : Real.exp (-a / 2) ^ 2 = Real.exp (-a) := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hEE : Real.exp (a / 2) * Real.exp (-a / 2) = 1 := by
    rw [← Real.exp_add, show (a / 2 + -a / 2 : ℝ) = 0 from by ring, Real.exp_zero]
  have hexp : (Real.sqrt 2 * (twoSiteK2RotC a * Real.exp (a / 2)
          + twoSiteK2RotS a * Real.exp (-a / 2))) ^ 2
        = 2 * (twoSiteK2RotC a ^ 2 * Real.exp a + 2 * (twoSiteK2RotC a * twoSiteK2RotS a)
            + twoSiteK2RotS a ^ 2 * Real.exp (-a)) := by
    have h : (Real.sqrt 2 * (twoSiteK2RotC a * Real.exp (a / 2)
          + twoSiteK2RotS a * Real.exp (-a / 2))) ^ 2
        = 2 * (twoSiteK2RotC a ^ 2 * Real.exp (a / 2) ^ 2
            + 2 * (twoSiteK2RotC a * twoSiteK2RotS a) * (Real.exp (a / 2) * Real.exp (-a / 2))
            + twoSiteK2RotS a ^ 2 * Real.exp (-a / 2) ^ 2) := by rw [mul_pow, hs2]; ring
    rw [h, hE2, hEp2, hEE]; ring
  rw [hexp, twoSiteK2RotC_sq, twoSiteK2RotS_sq, twoSiteK2RotC_mul_RotS]
  have hrad := twoSiteK2Rad_pos a
  have hΔ := twoSiteK2Delta_pos hβJ
  have hsinh : Real.exp (-a) < Real.exp a := Real.exp_lt_exp.mpr (by linarith)
  rw [← sub_nonneg]
  have hradne : twoSiteK2Rad a ≠ 0 := ne_of_gt hrad
  field_simp
  nlinarith [hrad, hΔ, hsinh, Real.exp_pos a, Real.exp_pos (-a),
    mul_pos hΔ (sub_pos.mpr hsinh)]

/-- The off-top boundary mass equals the squared norm minus the squared top
coordinate. -/
theorem twoSiteInteractingLayer_boundaryCoordinateRestSq_eq
    (p : IsingParams ℝ) (hp : p.h = 0) :
    (twoSiteInteractingLayerOrthogonalSpectralData p hp).boundaryCoordinateRestSq
        (layerOpenBalancedBoundaryVector
          (layerInternalWeight (SimpleGraph.completeGraph (Fin 2)) p))
        twoSiteInteractingLayerTop
      = vectorSqNorm (layerOpenBalancedBoundaryVector
          (layerInternalWeight (SimpleGraph.completeGraph (Fin 2)) p))
        - ((twoSiteInteractingLayerOrthogonalSpectralData p hp).boundaryCoordinates
            (layerOpenBalancedBoundaryVector
              (layerInternalWeight (SimpleGraph.completeGraph (Fin 2)) p))
            twoSiteInteractingLayerTop) ^ 2 := by
  have h := Finset.add_sum_erase Finset.univ
    (fun i => ((twoSiteInteractingLayerOrthogonalSpectralData p hp).boundaryCoordinates
      (layerOpenBalancedBoundaryVector
        (layerInternalWeight (SimpleGraph.completeGraph (Fin 2)) p)) i) ^ 2)
    (Finset.mem_univ twoSiteInteractingLayerTop)
  rw [RealOrthogonalSpectralData.sum_boundaryCoordinates_sq] at h
  rw [RealOrthogonalSpectralData.boundaryCoordinateRestSq]
  linarith [h]

/-- The off-top boundary mass is at most the squared top coordinate. -/
theorem twoSiteInteractingLayer_boundaryCoordinateRestSq_le
    (p : IsingParams ℝ) (hp : p.h = 0) (hβJ : 0 < p.β * p.J) :
    (twoSiteInteractingLayerOrthogonalSpectralData p hp).boundaryCoordinateRestSq
        (layerOpenBalancedBoundaryVector
          (layerInternalWeight (SimpleGraph.completeGraph (Fin 2)) p))
        twoSiteInteractingLayerTop
      ≤ ((twoSiteInteractingLayerOrthogonalSpectralData p hp).boundaryCoordinates
          (layerOpenBalancedBoundaryVector
            (layerInternalWeight (SimpleGraph.completeGraph (Fin 2)) p))
          twoSiteInteractingLayerTop) ^ 2 := by
  rw [twoSiteInteractingLayer_boundaryCoordinateRestSq_eq p hp]
  have := twoSiteInteractingLayer_vectorSqNorm_le_two_mul_top_sq p hp hβJ
  linarith

/-- The interacting open boundary-window cap strictly exceeds the decay
parameter. -/
theorem twoSiteInteractingLayer_theta_lt_cap
    (p : IsingParams ℝ) (hp : p.h = 0) (hβJ : 0 < p.β * p.J) :
    twoSiteInteractingTheta (p.β * p.J) <
      layerOpenBoundarySpectralWindowCap
        (layerInternalWeight (SimpleGraph.completeGraph (Fin 2)) p)
        (twoSiteInteractingLayerOrthogonalSpectralData p hp) twoSiteInteractingLayerTop := by
  rw [layerOpenBoundarySpectralWindowCap,
    RealOrthogonalSpectralData.boundarySpectralWindowCap, lt_min_iff]
  refine ⟨twoSiteInteractingTheta_lt_one (p.β * p.J), ?_⟩
  rw [RealOrthogonalSpectralData.boundarySpectralWindowThreshold]
  have hrest_le := twoSiteInteractingLayer_boundaryCoordinateRestSq_le p hp hβJ
  have htheta1 := twoSiteInteractingTheta_lt_one (p.β * p.J)
  have htheta0 := twoSiteInteractingTheta_nonneg hβJ
  split_ifs with hzero
  · exact htheta1
  · have hrest_pos : 0 <
        (twoSiteInteractingLayerOrthogonalSpectralData p hp).boundaryCoordinateRestSq
          (layerOpenBalancedBoundaryVector
            (layerInternalWeight (SimpleGraph.completeGraph (Fin 2)) p))
          twoSiteInteractingLayerTop :=
      lt_of_le_of_ne
        ((twoSiteInteractingLayerOrthogonalSpectralData p hp).boundaryCoordinateRestSq_nonneg _ _)
        (Ne.symm hzero)
    rw [lt_div_iff₀ hrest_pos]
    nlinarith [hrest_le, htheta1, htheta0, hrest_pos]

/-! ## The interacting open-slab decay discharge -/

/-- First unconditional finite *interacting* transverse-edge open-slab
same-transverse-site correlation bound, in prefactor form with decay parameter
`theta = flipOdd / top`. -/
theorem correlation_twoSiteInteractingLayerOpenSlabGraph_abs_le_of_simpleSpectrum
    (p : IsingParams ℝ) (hp : p.h = 0) (hβJ : 0 < p.β * p.J)
    (x : Fin 2) (left sep right : ℕ) (hsep : 0 < sep) :
    |correlation
        (layerOpenSlabGraph (S := Fin 2) (SimpleGraph.completeGraph (Fin 2))
          (layerIdentityTransitionPairs (Fin 2)) (left + sep + right)) p
        ({Prod.mk (layerOpenLeftIndex left sep right) x,
          Prod.mk (layerOpenRightIndex left sep right) x} :
            Finset (LayerOpenSlabSite (left + sep + right) (Fin 2)))|
      ≤
        ((twoSiteInteractingLayerOrthogonalSpectralData p hp).boundaryMarkedSpectralPrefactor
            (layerSpinAt x)
            (layerOpenBalancedBoundaryVector
              (layerInternalWeight (SimpleGraph.completeGraph (Fin 2)) p))
            (layerOpenBalancedBoundaryVector
              (layerInternalWeight (SimpleGraph.completeGraph (Fin 2)) p)) /
          (twoSiteInteractingLayerOrthogonalSpectralData p hp).boundarySpectralPartitionPrefactor
            (layerOpenBalancedBoundaryVector
              (layerInternalWeight (SimpleGraph.completeGraph (Fin 2)) p))
            twoSiteInteractingLayerTop (twoSiteInteractingTheta (p.β * p.J))) *
          twoSiteInteractingTheta (p.β * p.J) ^ sep :=
  correlation_layerOpenSlabGraph_abs_le_of_signedPositiveSimpleParity_boundaryWindow
    (SimpleGraph.completeGraph (Fin 2)) (layerIdentityTransitionPairs (Fin 2)) p hp x
    (twoSiteInteractingLayerOrthogonalSpectralData p hp) twoSiteInteractingLayerTop
    (twoSiteInteractingTheta (p.β * p.J)) (twoSiteInteractingTheta_nonneg hβJ)
    (twoSiteInteractingLayer_theta_lt_cap p hp hβJ)
    (twoSiteInteractingLayerSpectralWindow_theta p hp hβJ)
    ((twoSiteInteractingLayerOrthogonalSpectralData p hp).columnSimpleEigenspaces_of_simpleSpectrum
      (twoSiteInteractingLayerOrthogonalSpectralData_simpleSpectrum p hp hβJ))
    (twoSiteInteractingLayerOrthogonalSpectralData_top_signedPositiveColumn p hp)
    left sep right hsep

end TransferMatrix

end IsingModel

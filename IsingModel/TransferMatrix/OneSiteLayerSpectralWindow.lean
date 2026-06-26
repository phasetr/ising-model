import IsingModel.TransferMatrix.LayerSpectralWindowSmallRatio
import IsingModel.TransferMatrix.OneDimFreeEnergy
import IsingModel.TransferMatrix.CycleGraphZ
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# One-site layer spectral window

This file records the first positive-temperature physical layer spectral window.
For a one-site transverse layer, with no internal edges and identity
longitudinal coupling, the balanced layer transfer matrix is exactly the usual
`2 × 2` one-dimensional Ising transfer matrix.  The Hadamard diagonalization
therefore gives the concrete spectral-window parameter
`theta = tanh (p.β * p.J)`.

This is deliberately only a one-site bridge.  It does not prove a multi-site
high-temperature estimate, does not make `theta < 1` sufficient for larger
transverse layers, and does not address open slabs, thermodynamic limits, or
final hyperplane exponential decay.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

open scoped Matrix

namespace RealOrthogonalSpectralData

/-- Transport explicit orthogonal spectral data across equivalent index types. -/
noncomputable def reindex
    {Ω Ω' : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Ω'] [DecidableEq Ω']
    {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M) (e : Ω ≃ Ω') :
    RealOrthogonalSpectralData ((Matrix.reindex e e) M) where
  eigenvalue := fun i => E.eigenvalue (e.symm i)
  changeOfBasis := (Matrix.reindex e e) E.changeOfBasis
  orthogonal_left := by
    calc
      ((Matrix.reindex e e) E.changeOfBasis)ᵀ * (Matrix.reindex e e) E.changeOfBasis
          = (Matrix.reindex e e) (E.changeOfBasisᵀ * E.changeOfBasis) := by
            rw [Matrix.transpose_reindex]
            simpa only [Matrix.reindexLinearEquiv_apply] using
              Matrix.reindexLinearEquiv_mul ℝ ℝ e e e
                E.changeOfBasisᵀ E.changeOfBasis
      _ = (Matrix.reindex e e) (1 : Matrix Ω Ω ℝ) := by rw [E.orthogonal_left]
      _ = 1 := by
            simpa only [Matrix.reindexLinearEquiv_apply] using
              Matrix.reindexLinearEquiv_one ℝ ℝ e
  orthogonal_right := by
    calc
      (Matrix.reindex e e) E.changeOfBasis * ((Matrix.reindex e e) E.changeOfBasis)ᵀ
          = (Matrix.reindex e e) (E.changeOfBasis * E.changeOfBasisᵀ) := by
            rw [Matrix.transpose_reindex]
            simpa only [Matrix.reindexLinearEquiv_apply] using
              Matrix.reindexLinearEquiv_mul ℝ ℝ e e e
                E.changeOfBasis E.changeOfBasisᵀ
      _ = (Matrix.reindex e e) (1 : Matrix Ω Ω ℝ) := by rw [E.orthogonal_right]
      _ = 1 := by
            simpa only [Matrix.reindexLinearEquiv_apply] using
              Matrix.reindexLinearEquiv_one ℝ ℝ e
  diagonalizes := by
    have hdiag :
        Matrix.diagonal (fun i : Ω' => E.eigenvalue (e.symm i)) =
          (Matrix.reindex e e) (Matrix.diagonal E.eigenvalue) := by
      ext i j
      rw [Matrix.reindex_apply]
      by_cases hij : i = j
      · subst j
        simp [Matrix.diagonal_apply_eq]
      · have hsymm : e.symm i ≠ e.symm j := fun h => hij (e.symm.injective h)
        simp [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hsymm]
    calc
      (Matrix.reindex e e) M =
          (Matrix.reindex e e)
            (E.changeOfBasis * Matrix.diagonal E.eigenvalue * E.changeOfBasisᵀ) := by
            exact congrArg (fun M => (Matrix.reindex e e) M) E.diagonalizes
      _ = (Matrix.reindex e e) (E.changeOfBasis * Matrix.diagonal E.eigenvalue) *
          (Matrix.reindex e e) E.changeOfBasisᵀ := by
            simpa only [Matrix.reindexLinearEquiv_apply] using
              (Matrix.reindexLinearEquiv_mul ℝ ℝ e e e
                (E.changeOfBasis * Matrix.diagonal E.eigenvalue) E.changeOfBasisᵀ).symm
      _ = ((Matrix.reindex e e) E.changeOfBasis *
            (Matrix.reindex e e) (Matrix.diagonal E.eigenvalue)) *
          (Matrix.reindex e e) E.changeOfBasisᵀ := by
            rw [← (show
              (Matrix.reindex e e) E.changeOfBasis *
                  (Matrix.reindex e e) (Matrix.diagonal E.eigenvalue) =
                (Matrix.reindex e e) (E.changeOfBasis * Matrix.diagonal E.eigenvalue) by
                  simpa only [Matrix.reindexLinearEquiv_apply] using
                    Matrix.reindexLinearEquiv_mul ℝ ℝ e e e
                      E.changeOfBasis (Matrix.diagonal E.eigenvalue))]
      _ = (Matrix.reindex e e) E.changeOfBasis *
          Matrix.diagonal (fun i : Ω' => E.eigenvalue (e.symm i)) *
          ((Matrix.reindex e e) E.changeOfBasis)ᵀ := by
            rw [hdiag, Matrix.transpose_reindex]

end RealOrthogonalSpectralData

/-! ## The one-dimensional transfer matrix as orthogonal spectral data -/

/-- The normalized Hadamard matrix. -/
noncomputable def normalizedHadamardMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  (1 / Real.sqrt 2) • hadamardMatrix

theorem normalizedHadamardMatrix_transpose :
    normalizedHadamardMatrixᵀ = normalizedHadamardMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [normalizedHadamardMatrix, hadamardMatrix]

theorem normalizedHadamardMatrix_mul_self :
    normalizedHadamardMatrix * normalizedHadamardMatrix =
      (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [normalizedHadamardMatrix, Matrix.smul_mul, Matrix.mul_smul,
    hadamardMatrix_mul_self, smul_smul, smul_smul]
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hsqrt_ne : Real.sqrt 2 ≠ 0 :=
    ne_of_gt ((Real.sqrt_pos).2 (by norm_num : (0 : ℝ) < 2))
  have hcoef : (1 / Real.sqrt 2) * (1 / Real.sqrt 2) * 2 = (1 : ℝ) := by
    field_simp [hsqrt_ne]
    exact hsqrt_sq.symm
  rw [hcoef]
  simp

/-- The Hadamard orthogonal spectral data for the one-dimensional transfer
matrix. -/
noncomputable def isingTransferMatrix1DOrthogonalSpectralData (a : ℝ) :
    RealOrthogonalSpectralData (isingTransferMatrix1D a) where
  eigenvalue := ![transferEigenvalueTop a, transferEigenvalueBot a]
  changeOfBasis := normalizedHadamardMatrix
  orthogonal_left := by
    rw [normalizedHadamardMatrix_transpose, normalizedHadamardMatrix_mul_self]
  orthogonal_right := by
    rw [normalizedHadamardMatrix_transpose, normalizedHadamardMatrix_mul_self]
  diagonalizes := by
    let D : Matrix (Fin 2) (Fin 2) ℝ :=
      Matrix.diagonal ![transferEigenvalueTop a, transferEigenvalueBot a]
    have hsqrt_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hsqrt_ne : Real.sqrt 2 ≠ 0 :=
      ne_of_gt ((Real.sqrt_pos).2 (by norm_num : (0 : ℝ) < 2))
    have hcoef : (1 / Real.sqrt 2) * (1 / Real.sqrt 2) = (1 / 2 : ℝ) := by
      field_simp [hsqrt_ne]
      exact hsqrt_sq.symm
    have hQ :
        normalizedHadamardMatrix * D * normalizedHadamardMatrixᵀ =
          hadamardMatrix * D * hadamardMatrix⁻¹ := by
      rw [normalizedHadamardMatrix_transpose, normalizedHadamardMatrix,
        hadamardMatrix_inv]
      calc
        ((1 / Real.sqrt 2) • hadamardMatrix) * D *
            ((1 / Real.sqrt 2) • hadamardMatrix) =
            ((1 / Real.sqrt 2) * (1 / Real.sqrt 2)) •
              (hadamardMatrix * D * hadamardMatrix) := by
              rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
        _ = (1 / 2 : ℝ) • (hadamardMatrix * D * hadamardMatrix) := by
              rw [hcoef]
        _ = hadamardMatrix * D * ((1 / 2 : ℝ) • hadamardMatrix) := by
              rw [Matrix.mul_smul]
    rw [hQ]
    simpa [D, transferDiagonal, pow_one] using isingTransferMatrix1D_pow_eq_conj a 1

/-- The explicit top Hadamard column is constant. -/
theorem isingTransferMatrix1DOrthogonalSpectralData_top_column
    (a : ℝ) (i : Fin 2) :
    (isingTransferMatrix1DOrthogonalSpectralData a).changeOfBasis i 0 =
      1 / Real.sqrt 2 := by
  fin_cases i <;>
    simp [isingTransferMatrix1DOrthogonalSpectralData, normalizedHadamardMatrix,
      hadamardMatrix]

/-- The lower transfer eigenvalue is nonnegative for `a ≥ 0`. -/
theorem transferEigenvalueBot_nonneg_of_nonneg {a : ℝ} (ha : 0 ≤ a) :
    0 ≤ transferEigenvalueBot a := by
  rw [transferEigenvalueBot_eq]
  exact mul_nonneg (by norm_num) (Real.sinh_nonneg_iff.mpr ha)

/-- The lower transfer eigenvalue is `tanh a` times the top eigenvalue. -/
theorem transferEigenvalueBot_eq_tanh_mul_top (a : ℝ) :
    transferEigenvalueBot a = Real.tanh a * transferEigenvalueTop a := by
  have htop_ne : transferEigenvalueTop a ≠ 0 := ne_of_gt (transferEigenvalueTop_pos a)
  calc
    transferEigenvalueBot a =
        (transferEigenvalueBot a / transferEigenvalueTop a) * transferEigenvalueTop a := by
          rw [div_mul_cancel₀ _ htop_ne]
    _ = Real.tanh a * transferEigenvalueTop a := by
          rw [transferEigenvalue_ratio]

/-- The explicit 1D spectral data satisfies the spectral window
`theta = tanh a` away from the explicit top index `0`, for `a ≥ 0`. -/
theorem isingTransferMatrix1DOrthogonalSpectralData_subdominant_abs_le_tanh_top
    {a : ℝ} (ha : 0 ≤ a) :
    ∀ i, i ≠ (0 : Fin 2) →
      |(isingTransferMatrix1DOrthogonalSpectralData a).eigenvalue i| ≤
        Real.tanh a *
          (isingTransferMatrix1DOrthogonalSpectralData a).eigenvalue 0 := by
  intro i hi
  fin_cases i
  · exact False.elim (hi rfl)
  · have hbot_nonneg := transferEigenvalueBot_nonneg_of_nonneg ha
    simp only [isingTransferMatrix1DOrthogonalSpectralData, Fin.mk_one, Fin.isValue,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_zero, ge_iff_le]
    rw [abs_of_nonneg hbot_nonneg, transferEigenvalueBot_eq_tanh_mul_top]

/-! ## The one-site physical layer -/

/-- A one-site layer state is equivalently a spin. -/
def layerStatePUnitEquivSpin : LayerState PUnit ≃ Spin where
  toFun ω := ω PUnit.unit
  invFun s := fun _ => s
  left_inv ω := by
    funext x
    cases x
    rfl
  right_inv s := rfl

/-- A one-site layer state encoded by the transfer-matrix `Fin 2` spin index. -/
def layerStatePUnitEquivFin2 : LayerState PUnit ≃ Fin 2 :=
  layerStatePUnitEquivSpin.trans spinEquivFin2

/-- The one-site internal layer weight is trivial at zero field. -/
theorem layerInternalWeight_punit_bot_h_zero
    (p : IsingParams ℝ) (hp : p.h = 0) (ω : LayerState PUnit) :
    layerInternalWeight (⊥ : SimpleGraph PUnit) p ω = 1 := by
  simp [layerInternalWeight, hp]

/-- The one-site identity transition weight is the 1D transfer-matrix entry. -/
theorem layerTransitionWeight_punit_identity_eq_isingTransferMatrix1D
    (p : IsingParams ℝ) (ω η : LayerState PUnit) :
    layerTransitionWeight (layerIdentityTransitionPairs PUnit) p ω η =
      isingTransferMatrix1D (p.β * p.J)
        (layerStatePUnitEquivFin2 ω) (layerStatePUnitEquivFin2 η) := by
  change layerTransitionWeight (layerIdentityTransitionPairs PUnit) p ω η =
      isingTransferMatrix1D (p.β * p.J)
        (spinEquivFin2 (ω PUnit.unit)) (spinEquivFin2 (η PUnit.unit))
  rw [isingTransferMatrix1D_spinEquivFin2]
  simp [layerTransitionWeight, layerIdentityTransitionPairs]

/-- At zero field, the one-site balanced layer matrix is the reindexed 1D
transfer matrix. -/
theorem layerSymmetricTransferMatrix_punit_eq_reindex_isingTransferMatrix1D
    (p : IsingParams ℝ) (hp : p.h = 0) :
    layerSymmetricTransferMatrix
        (layerInternalWeight (⊥ : SimpleGraph PUnit) p)
        (layerTransitionWeight (layerIdentityTransitionPairs PUnit) p) =
      (Matrix.reindex layerStatePUnitEquivFin2.symm layerStatePUnitEquivFin2.symm)
        (isingTransferMatrix1D (p.β * p.J)) := by
  ext ω η
  rw [Matrix.reindex_apply]
  simp [layerSymmetricTransferMatrix, layerInternalWeight_punit_bot_h_zero p hp,
    layerTransitionWeight_punit_identity_eq_isingTransferMatrix1D]

/-- Explicit orthogonal spectral data for the one-site physical layer. -/
noncomputable def oneSiteLayerOrthogonalSpectralData
    (p : IsingParams ℝ) (hp : p.h = 0) :
    RealOrthogonalSpectralData
      (layerSymmetricTransferMatrix
        (layerInternalWeight (⊥ : SimpleGraph PUnit) p)
        (layerTransitionWeight (layerIdentityTransitionPairs PUnit) p)) where
  eigenvalue :=
    ((isingTransferMatrix1DOrthogonalSpectralData (p.β * p.J)).reindex
      layerStatePUnitEquivFin2.symm).eigenvalue
  changeOfBasis :=
    ((isingTransferMatrix1DOrthogonalSpectralData (p.β * p.J)).reindex
      layerStatePUnitEquivFin2.symm).changeOfBasis
  orthogonal_left :=
    ((isingTransferMatrix1DOrthogonalSpectralData (p.β * p.J)).reindex
      layerStatePUnitEquivFin2.symm).orthogonal_left
  orthogonal_right :=
    ((isingTransferMatrix1DOrthogonalSpectralData (p.β * p.J)).reindex
      layerStatePUnitEquivFin2.symm).orthogonal_right
  diagonalizes := by
    rw [layerSymmetricTransferMatrix_punit_eq_reindex_isingTransferMatrix1D p hp]
    exact
      ((isingTransferMatrix1DOrthogonalSpectralData (p.β * p.J)).reindex
        layerStatePUnitEquivFin2.symm).diagonalizes

/-- In the one-site layer spectral data, the explicit top index has eigenvalue
`transferEigenvalueTop (p.β * p.J)`. -/
theorem oneSiteLayerOrthogonalSpectralData_top_eigenvalue
    (p : IsingParams ℝ) (hp : p.h = 0) :
    (oneSiteLayerOrthogonalSpectralData p hp).eigenvalue
        (layerStatePUnitEquivFin2.symm 0) =
      transferEigenvalueTop (p.β * p.J) := by
  simp [oneSiteLayerOrthogonalSpectralData, RealOrthogonalSpectralData.reindex,
    isingTransferMatrix1DOrthogonalSpectralData]

/-- The one-site layer spectral data has spectral window `tanh (βJ)`. -/
theorem oneSiteLayerSpectralWindow_tanh
    (p : IsingParams ℝ) (hp : p.h = 0) (hβJ : 0 ≤ p.β * p.J) :
    ∀ i, i ≠ layerStatePUnitEquivFin2.symm 0 →
      |(oneSiteLayerOrthogonalSpectralData p hp).eigenvalue i| ≤
        Real.tanh (p.β * p.J) *
          (oneSiteLayerOrthogonalSpectralData p hp).eigenvalue
            (layerStatePUnitEquivFin2.symm 0) := by
  have hbase :=
    isingTransferMatrix1DOrthogonalSpectralData_subdominant_abs_le_tanh_top hβJ
  intro i hi
  simpa [oneSiteLayerOrthogonalSpectralData, RealOrthogonalSpectralData.reindex,
    layerSymmetricTransferMatrix_punit_eq_reindex_isingTransferMatrix1D] using
    hbase (layerStatePUnitEquivFin2 i) (by
      intro h
      apply hi
      apply layerStatePUnitEquivFin2.injective
      simpa using h)

/-- The explicit top column of the one-site layer Hadamard basis is invariant
under global spin flip. -/
theorem oneSiteLayerOrthogonalSpectralData_top_flip_even
    (p : IsingParams ℝ) (hp : p.h = 0) :
    ∀ ω : LayerState PUnit,
      (oneSiteLayerOrthogonalSpectralData p hp).changeOfBasis
          (layerStateFlipEquiv PUnit ω) (layerStatePUnitEquivFin2.symm 0) =
        (oneSiteLayerOrthogonalSpectralData p hp).changeOfBasis
          ω (layerStatePUnitEquivFin2.symm 0) := by
  intro ω
  cases hω : ω PUnit.unit <;>
    simp only [oneSiteLayerOrthogonalSpectralData, layerStatePUnitEquivFin2,
      layerStatePUnitEquivSpin, Matrix.reindex_apply, Equiv.symm_symm, Equiv.coe_trans,
      Equiv.coe_fn_mk, RealOrthogonalSpectralData.reindex, Equiv.trans_apply,
      layerStateFlipEquiv_apply, Fin.isValue, Equiv.symm_trans_apply, Equiv.coe_fn_symm_mk,
      Matrix.submatrix_apply, Function.comp_apply, Equiv.apply_symm_apply, hω] <;>
    rw [isingTransferMatrix1DOrthogonalSpectralData_top_column,
      isingTransferMatrix1DOrthogonalSpectralData_top_column]

/-- One-site positive-temperature balanced min-gap certificate with the
concrete physical spectral window `tanh (p.β * p.J)`. -/
noncomputable def oneSiteLayerBalancedMinGapCertificate_tanh
    (p : IsingParams ℝ) (hp : p.h = 0) (hβJ : 0 < p.β * p.J) (x : PUnit) :
    LayerBalancedMinSpectralGapCertificate
      (layerInternalWeight (⊥ : SimpleGraph PUnit) p)
      (layerTransitionWeight (layerIdentityTransitionPairs PUnit) p)
      (layerSpinAt x) := by
  let E := oneSiteLayerOrthogonalSpectralData p hp
  let top : LayerState PUnit := layerStatePUnitEquivFin2.symm 0
  refine
    layerBalancedMinSpectralGapCertificate_of_orthogonalDominantBounds_flipEvenSpin
      (layerInternalWeight (⊥ : SimpleGraph PUnit) p)
      (layerTransitionWeight (layerIdentityTransitionPairs PUnit) p)
      x
      E top
      (transferEigenvalueTop (p.β * p.J)) (Real.tanh (p.β * p.J))
      (transferEigenvalueTop_pos (p.β * p.J)) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [Real.tanh_eq_sinh_div_cosh]
    exact le_of_lt (div_pos (Real.sinh_pos_iff.mpr hβJ) (Real.cosh_pos _))
  · exact Real.tanh_lt_one (p.β * p.J)
  · have hcard : Fintype.card (LayerState PUnit) = 2 := by
      exact layerState_card_eq_two_of_card_eq_one PUnit Fintype.card_punit
    rw [hcard]
    norm_num
    exact Real.tanh_lt_one (p.β * p.J)
  · simp [E, oneSiteLayerOrthogonalSpectralData, RealOrthogonalSpectralData.reindex,
      isingTransferMatrix1DOrthogonalSpectralData, top]
  · intro i hi
    have hbase :=
      isingTransferMatrix1DOrthogonalSpectralData_subdominant_abs_le_tanh_top
        (le_of_lt hβJ) (layerStatePUnitEquivFin2 i) (by
          intro h
          apply hi
          apply layerStatePUnitEquivFin2.injective
          simpa [top] using h)
    simpa [E, top, oneSiteLayerOrthogonalSpectralData,
      RealOrthogonalSpectralData.reindex, isingTransferMatrix1DOrthogonalSpectralData]
      using hbase
  · simpa [E, top] using oneSiteLayerOrthogonalSpectralData_top_flip_even p hp

end TransferMatrix

end IsingModel

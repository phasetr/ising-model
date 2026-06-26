import IsingModel.TransferMatrix.OneSiteLayerSpectralWindow
import Mathlib.LinearAlgebra.Matrix.Kronecker
import IsingModel.RealTanhAux

/-!
# Two-site free-layer spectral window

This file records the first larger-than-one-site positive-temperature physical
layer spectral window.  The transverse layer is `Fin 2`, the transverse graph is
empty, the external field is zero, and adjacent layers are coupled by identity
pairs.  The balanced layer matrix is the Kronecker product of two one-site
transfer matrices, so the tensor Hadamard basis gives the concrete spectral
window `theta = tanh (p.β * p.J)`.

The final small-ratio certificate uses the true four-state finite prefactor
threshold `tanh (p.β * p.J) < 1 / 3`.  This deliberately does not claim an
interacting cubic-layer spectral window, an arbitrary finite-layer theorem, or
that `theta < 1` is enough beyond one site.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

open scoped BigOperators Matrix Kronecker

/-! ## The free two-site transfer matrix -/

/-- A two-site layer state encoded by the two one-site transfer-matrix spin
indices. -/
def layerStateFin2EquivFin2Prod : LayerState (Fin 2) ≃ Fin 2 × Fin 2 where
  toFun ω := (spinEquivFin2 (ω 0), spinEquivFin2 (ω 1))
  invFun i := fun x => if x = 0 then spinEquivFin2.symm i.1 else spinEquivFin2.symm i.2
  left_inv := by
    intro ω
    funext x
    fin_cases x <;> simp
  right_inv := by
    intro i
    ext <;> simp

/-- The one-site eigenvalue vector, made independent of the spectral-data
record so it rewrites smoothly inside Kronecker products. -/
noncomputable def oneSiteTransferEigenvalue (a : ℝ) : Fin 2 → ℝ :=
  ![transferEigenvalueTop a, transferEigenvalueBot a]

/-- The two-site free-layer eigenvalues in the tensor Hadamard basis. -/
noncomputable def twoSiteFreeTransferEigenvalue (a : ℝ) (i : Fin 2 × Fin 2) : ℝ :=
  oneSiteTransferEigenvalue a i.1 * oneSiteTransferEigenvalue a i.2

/-- The tensor product of the two normalized one-site Hadamard bases. -/
noncomputable def twoSiteFreeHadamardMatrix :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  normalizedHadamardMatrix ⊗ₖ normalizedHadamardMatrix

/-- The tensor Hadamard matrix is left-orthogonal. -/
theorem twoSiteFreeHadamardMatrix_orthogonal_left :
    twoSiteFreeHadamardMatrixᵀ * twoSiteFreeHadamardMatrix =
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) := by
  rw [twoSiteFreeHadamardMatrix]
  rw [← Matrix.kroneckerMap_transpose (fun x y : ℝ => x * y)]
  rw [← Matrix.mul_kronecker_mul]
  rw [normalizedHadamardMatrix_transpose, normalizedHadamardMatrix_mul_self]
  rw [Matrix.one_kronecker_one]

/-- The tensor Hadamard matrix is right-orthogonal. -/
theorem twoSiteFreeHadamardMatrix_orthogonal_right :
    twoSiteFreeHadamardMatrix * twoSiteFreeHadamardMatrixᵀ =
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) := by
  rw [twoSiteFreeHadamardMatrix]
  rw [← Matrix.kroneckerMap_transpose (fun x y : ℝ => x * y)]
  rw [← Matrix.mul_kronecker_mul]
  rw [normalizedHadamardMatrix_transpose, normalizedHadamardMatrix_mul_self]
  rw [Matrix.one_kronecker_one]

/-- Kronecker diagonalization of the two-site free transfer matrix. -/
theorem twoSiteFreeTransferMatrix_diagonalizes (a : ℝ) :
    (isingTransferMatrix1D a ⊗ₖ isingTransferMatrix1D a) =
      twoSiteFreeHadamardMatrix *
        Matrix.diagonal (twoSiteFreeTransferEigenvalue a) *
        twoSiteFreeHadamardMatrixᵀ := by
  have h1 : isingTransferMatrix1D a =
      normalizedHadamardMatrix * Matrix.diagonal (oneSiteTransferEigenvalue a) *
        normalizedHadamardMatrixᵀ := by
    simpa [isingTransferMatrix1DOrthogonalSpectralData, oneSiteTransferEigenvalue] using
      (isingTransferMatrix1DOrthogonalSpectralData a).diagonalizes
  calc
    (isingTransferMatrix1D a ⊗ₖ isingTransferMatrix1D a)
        = ((normalizedHadamardMatrix * Matrix.diagonal (oneSiteTransferEigenvalue a) *
              normalizedHadamardMatrixᵀ) ⊗ₖ
            (normalizedHadamardMatrix * Matrix.diagonal (oneSiteTransferEigenvalue a) *
              normalizedHadamardMatrixᵀ)) := by
          rw [h1]
    _ = (normalizedHadamardMatrix ⊗ₖ normalizedHadamardMatrix) *
        (Matrix.diagonal (oneSiteTransferEigenvalue a) ⊗ₖ
          Matrix.diagonal (oneSiteTransferEigenvalue a)) *
        (normalizedHadamardMatrixᵀ ⊗ₖ normalizedHadamardMatrixᵀ) := by
          rw [← Matrix.mul_kronecker_mul]
          rw [← Matrix.mul_kronecker_mul]
    _ = twoSiteFreeHadamardMatrix *
        Matrix.diagonal (twoSiteFreeTransferEigenvalue a) *
        twoSiteFreeHadamardMatrixᵀ := by
          rw [twoSiteFreeHadamardMatrix, Matrix.diagonal_kronecker_diagonal]
          rw [← Matrix.kroneckerMap_transpose (fun x y : ℝ => x * y)]
          rfl

/-- Explicit orthogonal spectral data for the two-site free transfer matrix. -/
noncomputable def twoSiteFreeTransferOrthogonalSpectralData (a : ℝ) :
    RealOrthogonalSpectralData (isingTransferMatrix1D a ⊗ₖ isingTransferMatrix1D a) where
  eigenvalue := twoSiteFreeTransferEigenvalue a
  changeOfBasis := twoSiteFreeHadamardMatrix
  orthogonal_left := twoSiteFreeHadamardMatrix_orthogonal_left
  orthogonal_right := twoSiteFreeHadamardMatrix_orthogonal_right
  diagonalizes := twoSiteFreeTransferMatrix_diagonalizes a

/-- At zero field, the free two-site balanced layer matrix is the Kronecker
product of two one-site transfer matrices. -/
theorem layerSymmetricTransferMatrix_fin2_bot_eq_reindex_kronecker
    (p : IsingParams ℝ) (hp : p.h = 0) :
    layerSymmetricTransferMatrix
        (layerInternalWeight (⊥ : SimpleGraph (Fin 2)) p)
        (layerTransitionWeight (layerIdentityTransitionPairs (Fin 2)) p) =
      (Matrix.reindex layerStateFin2EquivFin2Prod.symm layerStateFin2EquivFin2Prod.symm)
        (isingTransferMatrix1D (p.β * p.J) ⊗ₖ
          isingTransferMatrix1D (p.β * p.J)) := by
  ext ω η
  rw [Matrix.reindex_apply]
  suffices
      Real.exp
          (p.β * p.J *
            ∑ xy ∈ Finset.image (fun x => (x, x)) Finset.univ,
              Spin.sign ℝ (ω xy.1) * Spin.sign ℝ (η xy.2)) =
        Real.exp ((p.β * p.J) * (Spin.sign ℝ (ω 0) * Spin.sign ℝ (η 0))) *
          Real.exp ((p.β * p.J) * (Spin.sign ℝ (ω 1) * Spin.sign ℝ (η 1))) by
    simpa [layerSymmetricTransferMatrix, layerInternalWeight, hp, layerTransitionWeight,
      layerIdentityTransitionPairs, isingTransferMatrix1D_spinEquivFin2,
      layerStateFin2EquivFin2Prod, Fin.sum_univ_two] using this
  rw [Finset.sum_image]
  · simp only [Fin.sum_univ_two, Fin.isValue]
    rw [← Real.exp_add]
    congr 1
    ring
  · intro x _ y _ hxy
    exact (Prod.ext_iff.mp hxy).1

/-- Explicit orthogonal spectral data for the physical two-site free layer. -/
noncomputable def twoSiteFreeLayerOrthogonalSpectralData
    (p : IsingParams ℝ) (hp : p.h = 0) :
    RealOrthogonalSpectralData
      (layerSymmetricTransferMatrix
        (layerInternalWeight (⊥ : SimpleGraph (Fin 2)) p)
        (layerTransitionWeight (layerIdentityTransitionPairs (Fin 2)) p)) where
  eigenvalue :=
    ((twoSiteFreeTransferOrthogonalSpectralData (p.β * p.J)).reindex
      layerStateFin2EquivFin2Prod.symm).eigenvalue
  changeOfBasis :=
    ((twoSiteFreeTransferOrthogonalSpectralData (p.β * p.J)).reindex
      layerStateFin2EquivFin2Prod.symm).changeOfBasis
  orthogonal_left :=
    ((twoSiteFreeTransferOrthogonalSpectralData (p.β * p.J)).reindex
      layerStateFin2EquivFin2Prod.symm).orthogonal_left
  orthogonal_right :=
    ((twoSiteFreeTransferOrthogonalSpectralData (p.β * p.J)).reindex
      layerStateFin2EquivFin2Prod.symm).orthogonal_right
  diagonalizes := by
    rw [layerSymmetricTransferMatrix_fin2_bot_eq_reindex_kronecker p hp]
    exact
      ((twoSiteFreeTransferOrthogonalSpectralData (p.β * p.J)).reindex
        layerStateFin2EquivFin2Prod.symm).diagonalizes

/-! ## The concrete spectral window -/

/-- The explicit tensor top index has top eigenvalue squared. -/
theorem twoSiteFreeTransferEigenvalue_top (a : ℝ) :
    twoSiteFreeTransferEigenvalue a (0, 0) = transferEigenvalueTop a ^ 2 := by
  simp [twoSiteFreeTransferEigenvalue, oneSiteTransferEigenvalue, sq]

/-- The two-site free transfer spectral data has spectral window `tanh a` away
from the explicit tensor top index `(0,0)`, for `a ≥ 0`. -/
theorem twoSiteFreeTransferSpectralWindow_tanh {a : ℝ} (ha : 0 ≤ a) :
    ∀ i : Fin 2 × Fin 2, i ≠ (0, 0) →
      |twoSiteFreeTransferEigenvalue a i| ≤
        Real.tanh a * (transferEigenvalueTop a ^ 2) := by
  intro i hi
  rcases i with ⟨i, j⟩
  fin_cases i <;> fin_cases j
  · exact False.elim (hi rfl)
  · have hbot_nonneg := transferEigenvalueBot_nonneg_of_nonneg ha
    calc
      |twoSiteFreeTransferEigenvalue a (0, 1)| =
          |transferEigenvalueTop a * transferEigenvalueBot a| := by
            simp [twoSiteFreeTransferEigenvalue, oneSiteTransferEigenvalue]
      _ = transferEigenvalueTop a * transferEigenvalueBot a := by
            rw [abs_of_nonneg (mul_nonneg (transferEigenvalueTop_pos a).le hbot_nonneg)]
      _ = Real.tanh a * (transferEigenvalueTop a ^ 2) := by
            rw [transferEigenvalueBot_eq_tanh_mul_top]
            ring
      _ ≤ Real.tanh a * (transferEigenvalueTop a ^ 2) := le_rfl
  · have hbot_nonneg := transferEigenvalueBot_nonneg_of_nonneg ha
    calc
      |twoSiteFreeTransferEigenvalue a (1, 0)| =
          |transferEigenvalueBot a * transferEigenvalueTop a| := by
            simp [twoSiteFreeTransferEigenvalue, oneSiteTransferEigenvalue]
      _ = transferEigenvalueBot a * transferEigenvalueTop a := by
            rw [abs_of_nonneg (mul_nonneg hbot_nonneg (transferEigenvalueTop_pos a).le)]
      _ = Real.tanh a * (transferEigenvalueTop a ^ 2) := by
            rw [transferEigenvalueBot_eq_tanh_mul_top]
            ring
      _ ≤ Real.tanh a * (transferEigenvalueTop a ^ 2) := le_rfl
  · have hbot_nonneg := transferEigenvalueBot_nonneg_of_nonneg ha
    have htanh_nonneg : 0 ≤ Real.tanh a := real_tanh_nonneg ha
    have htanh_le_one : Real.tanh a ≤ 1 := le_of_lt (Real.tanh_lt_one a)
    have htop_sq_nonneg : 0 ≤ transferEigenvalueTop a ^ 2 := sq_nonneg _
    have htanh_sq_le : Real.tanh a * Real.tanh a ≤ Real.tanh a := by
      nlinarith [mul_le_mul_of_nonneg_left htanh_le_one htanh_nonneg]
    calc
      |twoSiteFreeTransferEigenvalue a (1, 1)| =
          |transferEigenvalueBot a * transferEigenvalueBot a| := by
            simp [twoSiteFreeTransferEigenvalue, oneSiteTransferEigenvalue]
      _ = transferEigenvalueBot a * transferEigenvalueBot a := by
            rw [abs_of_nonneg (mul_nonneg hbot_nonneg hbot_nonneg)]
      _ = (Real.tanh a * Real.tanh a) * (transferEigenvalueTop a ^ 2) := by
            rw [transferEigenvalueBot_eq_tanh_mul_top]
            ring
      _ ≤ Real.tanh a * (transferEigenvalueTop a ^ 2) := by
            exact mul_le_mul_of_nonneg_right htanh_sq_le htop_sq_nonneg

/-- The reindexed physical two-site free layer has the expected top
eigenvalue. -/
theorem twoSiteFreeLayerOrthogonalSpectralData_top_eigenvalue
    (p : IsingParams ℝ) (hp : p.h = 0) :
    (twoSiteFreeLayerOrthogonalSpectralData p hp).eigenvalue
        (layerStateFin2EquivFin2Prod.symm (0, 0)) =
      transferEigenvalueTop (p.β * p.J) ^ 2 := by
  simp [twoSiteFreeLayerOrthogonalSpectralData, RealOrthogonalSpectralData.reindex,
    twoSiteFreeTransferOrthogonalSpectralData, twoSiteFreeTransferEigenvalue_top]

/-- The physical two-site free layer has spectral window `tanh (βJ)`. -/
theorem twoSiteFreeLayerSpectralWindow_tanh
    (p : IsingParams ℝ) (hp : p.h = 0) (hβJ : 0 ≤ p.β * p.J) :
    ∀ i, i ≠ layerStateFin2EquivFin2Prod.symm (0, 0) →
      |(twoSiteFreeLayerOrthogonalSpectralData p hp).eigenvalue i| ≤
        Real.tanh (p.β * p.J) *
          (transferEigenvalueTop (p.β * p.J) ^ 2) := by
  intro i hi
  have hbase :=
    twoSiteFreeTransferSpectralWindow_tanh hβJ (layerStateFin2EquivFin2Prod i) (by
      intro h
      apply hi
      apply layerStateFin2EquivFin2Prod.injective
      simpa using h)
  simpa [twoSiteFreeLayerOrthogonalSpectralData, RealOrthogonalSpectralData.reindex,
    twoSiteFreeTransferOrthogonalSpectralData] using hbase

/-- The explicit top tensor-Hadamard column is invariant under global spin flip. -/
theorem twoSiteFreeLayerOrthogonalSpectralData_top_flip_even
    (p : IsingParams ℝ) (hp : p.h = 0) :
    ∀ ω : LayerState (Fin 2),
      (twoSiteFreeLayerOrthogonalSpectralData p hp).changeOfBasis
          (layerStateFlipEquiv (Fin 2) ω)
          (layerStateFin2EquivFin2Prod.symm (0, 0)) =
        (twoSiteFreeLayerOrthogonalSpectralData p hp).changeOfBasis
          ω (layerStateFin2EquivFin2Prod.symm (0, 0)) := by
  intro ω
  have hQ : ∀ i : Fin 2, normalizedHadamardMatrix i 0 = 1 / Real.sqrt 2 := by
    intro i
    simpa [isingTransferMatrix1DOrthogonalSpectralData] using
      isingTransferMatrix1DOrthogonalSpectralData_top_column (p.β * p.J) i
  simp [twoSiteFreeLayerOrthogonalSpectralData, RealOrthogonalSpectralData.reindex,
    twoSiteFreeTransferOrthogonalSpectralData, twoSiteFreeHadamardMatrix, hQ]

/-! ## Small-ratio certificate -/

/-- Two-site positive-temperature free-layer balanced min-gap certificate with
the concrete physical spectral window `tanh (p.β * p.J)`.

The smallness hypothesis is the four-state finite prefactor threshold
`tanh (p.β * p.J) < 1 / 3`. -/
noncomputable def twoSiteFreeLayerBalancedMinGapCertificate_tanh
    (p : IsingParams ℝ) (hp : p.h = 0) (hβJ : 0 < p.β * p.J)
    (hsmall : Real.tanh (p.β * p.J) < (3 : ℝ)⁻¹) (x : Fin 2) :
    LayerBalancedMinSpectralGapCertificate
      (layerInternalWeight (⊥ : SimpleGraph (Fin 2)) p)
      (layerTransitionWeight (layerIdentityTransitionPairs (Fin 2)) p)
      (layerSpinAt x) := by
  let E := twoSiteFreeLayerOrthogonalSpectralData p hp
  let top : LayerState (Fin 2) := layerStateFin2EquivFin2Prod.symm (0, 0)
  refine
    layerBalancedMinSpectralGapCertificate_of_orthogonalDominantBounds_flipEvenSpin
      (layerInternalWeight (⊥ : SimpleGraph (Fin 2)) p)
      (layerTransitionWeight (layerIdentityTransitionPairs (Fin 2)) p)
      x
      E top
      (transferEigenvalueTop (p.β * p.J) ^ 2) (Real.tanh (p.β * p.J))
      (sq_pos_of_pos (transferEigenvalueTop_pos (p.β * p.J))) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [Real.tanh_eq_sinh_div_cosh]
    exact le_of_lt (div_pos (Real.sinh_pos_iff.mpr hβJ) (Real.cosh_pos _))
  · exact Real.tanh_lt_one (p.β * p.J)
  · have hcard : Fintype.card (LayerState (Fin 2)) = 4 := by
      rw [layerState_card_eq_two_pow]
      norm_num
    rw [hcard]
    norm_num at hsmall ⊢
    nlinarith
  · simp [E, top, twoSiteFreeLayerOrthogonalSpectralData,
      RealOrthogonalSpectralData.reindex, twoSiteFreeTransferOrthogonalSpectralData,
      twoSiteFreeTransferEigenvalue_top]
  · intro i hi
    simpa [E, top] using
      twoSiteFreeLayerSpectralWindow_tanh p hp (le_of_lt hβJ) i hi
  · simpa [E, top] using twoSiteFreeLayerOrthogonalSpectralData_top_flip_even p hp

end TransferMatrix

end IsingModel

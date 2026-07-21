import IsingModel.TransferMatrix.FreeLayerWalshSpectralWindow.WalshDiagonalization
import IsingModel.RealTanhAux
import IsingModel.TransferMatrix.OneSiteLayerSpectralWindow

/-!
# Finite free-layer Walsh spectral window (3/4): physical bridge and spectral window

Structural split (3/4) of `TransferMatrix.FreeLayerWalshSpectralWindow`.  This child
bridges the abstract Walsh diagonalization to the physical zero-field free layer: the
identity transition weight factors into one-dimensional transfer entries, the internal
weight is trivial at `h = 0`, so the balanced layer transfer matrix is the free product
transfer matrix.  It then records the spectral-window consequences: a non-top Walsh index
has a nonempty down-spin set, the absolute Walsh eigenvalue is `tanh a ^ |A|` times the
all-top eigenvalue, hence the subdominant bound with `theta = tanh a`, and packages the
free-layer Walsh data as a `RealOrthogonalSpectralData`.  It builds on the sibling
`...WalshDiagonalization`.  See the `TransferMatrix.FreeLayerWalshSpectralWindow` facade
module for the full contents overview.
-/

namespace IsingModel

namespace TransferMatrix

open scoped BigOperators Matrix
open Finset

variable {S : Type*} [Fintype S] [DecidableEq S]

/-! ## Physical free-layer bridge -/

/-- The identity transition weight over a finite free layer factors into the
product of one-dimensional transfer-matrix entries. -/
theorem layerTransitionWeight_identity_eq_freeLayerTransferMatrix
    (p : IsingParams ℝ) (ω η : LayerState S) :
    layerTransitionWeight (layerIdentityTransitionPairs S) p ω η =
      freeLayerTransferMatrix (S := S) (p.β * p.J) ω η := by
  classical
  unfold layerTransitionWeight layerIdentityTransitionPairs freeLayerTransferMatrix
  rw [Finset.sum_image]
  · simp_rw [isingTransferMatrix1D_spinEquivFin2]
    rw [Finset.mul_sum, Real.exp_sum]
  · intro x _ y _ hxy
    exact (Prod.ext_iff.mp hxy).1

omit [DecidableEq S] in
/-- The internal free-layer weight is trivial at zero field. -/
theorem layerInternalWeight_bot_h_zero
    (p : IsingParams ℝ) (hp : p.h = 0) (ω : LayerState S) :
    layerInternalWeight (⊥ : SimpleGraph S) p ω = 1 := by
  simp [layerInternalWeight, hp]

/-- At zero field, the finite free-layer balanced matrix is the free product
transfer matrix. -/
theorem layerSymmetricTransferMatrix_bot_identity_eq_freeLayerTransferMatrix
    (p : IsingParams ℝ) (hp : p.h = 0) :
    layerSymmetricTransferMatrix
        (layerInternalWeight (⊥ : SimpleGraph S) p)
        (layerTransitionWeight (layerIdentityTransitionPairs S) p) =
      freeLayerTransferMatrix (S := S) (p.β * p.J) := by
  ext ω η
  simp [layerSymmetricTransferMatrix, layerInternalWeight_bot_h_zero p hp,
    layerTransitionWeight_identity_eq_freeLayerTransferMatrix]

/-! ## Spectral-window consequences -/

/-- A non-top Walsh index has a nonempty down-spin set. -/
theorem layerStateDownSet_nonempty_of_ne_freeLayerWalshTop
    {χ : LayerState S} (hχ : χ ≠ freeLayerWalshTop (S := S)) :
    (layerStateDownSet χ).Nonempty := by
  classical
  by_contra hnonempty
  have hset : layerStateDownSet χ = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hnonempty
  have htop : χ = freeLayerWalshTop (S := S) := by
    calc
      χ = layerStateDownSetEquivFinset.symm (layerStateDownSet χ) :=
        (layerStateDownSetEquivFinset.left_inv χ).symm
      _ = layerStateDownSetEquivFinset.symm ∅ := by rw [hset]
      _ = freeLayerWalshTop (S := S) := rfl
  exact hχ htop

/-- A non-top Walsh index has a positive down-spin-set cardinality. -/
theorem layerStateDownSet_card_pos_of_ne_freeLayerWalshTop
    {χ : LayerState S} (hχ : χ ≠ freeLayerWalshTop (S := S)) :
    0 < (layerStateDownSet χ).card := by
  exact Finset.card_pos.mpr
    (layerStateDownSet_nonempty_of_ne_freeLayerWalshTop (S := S) hχ)

omit [DecidableEq S] in
/-- The absolute free-layer Walsh eigenvalue is the corresponding power of
`tanh a` times the all-top eigenvalue. -/
theorem freeLayerWalshEigenvalue_abs_eq_tanh_pow_mul_top_pow
    {a : ℝ} (ha : 0 ≤ a) (χ : LayerState S) :
    |freeLayerWalshEigenvalue (S := S) a χ| =
      Real.tanh a ^ (layerStateDownSet χ).card *
        transferEigenvalueTop a ^ Fintype.card S := by
  classical
  let A : Finset S := layerStateDownSet χ
  have hA_le : A.card ≤ Fintype.card S := Finset.card_le_univ A
  have htop_nonneg : 0 ≤ transferEigenvalueTop a :=
    le_of_lt (transferEigenvalueTop_pos a)
  have hbot_nonneg : 0 ≤ transferEigenvalueBot a :=
    transferEigenvalueBot_nonneg_of_nonneg ha
  have heig_nonneg : 0 ≤ freeLayerWalshEigenvalue (S := S) a χ := by
    dsimp [freeLayerWalshEigenvalue]
    exact mul_nonneg (pow_nonneg htop_nonneg _) (pow_nonneg hbot_nonneg _)
  calc
    |freeLayerWalshEigenvalue (S := S) a χ|
        = freeLayerWalshEigenvalue (S := S) a χ := by
            rw [abs_of_nonneg heig_nonneg]
    _ = transferEigenvalueTop a ^ (Fintype.card S - A.card) *
          (Real.tanh a * transferEigenvalueTop a) ^ A.card := by
            simp [freeLayerWalshEigenvalue, A, transferEigenvalueBot_eq_tanh_mul_top]
    _ = transferEigenvalueTop a ^ (Fintype.card S - A.card) *
          (Real.tanh a ^ A.card * transferEigenvalueTop a ^ A.card) := by
            rw [mul_pow]
    _ = Real.tanh a ^ A.card *
          (transferEigenvalueTop a ^ (Fintype.card S - A.card) *
            transferEigenvalueTop a ^ A.card) := by
            ring
    _ = Real.tanh a ^ A.card *
          transferEigenvalueTop a ^ ((Fintype.card S - A.card) + A.card) := by
            rw [← pow_add]
    _ = Real.tanh a ^ (layerStateDownSet χ).card *
          transferEigenvalueTop a ^ Fintype.card S := by
            rw [Nat.sub_add_cancel hA_le]

/-- The arbitrary finite free-layer Walsh spectral window with
`theta = tanh a`. -/
theorem freeLayerWalshSpectralWindow_tanh
    {a : ℝ} (ha : 0 ≤ a) :
    ∀ i, i ≠ freeLayerWalshTop (S := S) →
      |freeLayerWalshEigenvalue (S := S) a i| ≤
        Real.tanh a * transferEigenvalueTop a ^ Fintype.card S := by
  intro i hi
  have htanh_nonneg : 0 ≤ Real.tanh a := real_tanh_nonneg ha
  have htanh_le_one : Real.tanh a ≤ 1 := le_of_lt (Real.tanh_lt_one a)
  have hcard_pos : 0 < (layerStateDownSet i).card :=
    layerStateDownSet_card_pos_of_ne_freeLayerWalshTop (S := S) hi
  have hpow :
      Real.tanh a ^ (layerStateDownSet i).card ≤ Real.tanh a :=
    pow_le_of_le_one htanh_nonneg htanh_le_one (Nat.ne_of_gt hcard_pos)
  have htop_pow_nonneg :
      0 ≤ transferEigenvalueTop a ^ Fintype.card S :=
    pow_nonneg (le_of_lt (transferEigenvalueTop_pos a)) _
  calc
    |freeLayerWalshEigenvalue (S := S) a i|
        = Real.tanh a ^ (layerStateDownSet i).card *
            transferEigenvalueTop a ^ Fintype.card S := by
            exact freeLayerWalshEigenvalue_abs_eq_tanh_pow_mul_top_pow (S := S) ha i
    _ ≤ Real.tanh a * transferEigenvalueTop a ^ Fintype.card S := by
            exact mul_le_mul_of_nonneg_right hpow htop_pow_nonneg

/-- The finite free-layer Walsh transfer data. -/
noncomputable def freeLayerTransferOrthogonalSpectralData
    (a : ℝ) :
    RealOrthogonalSpectralData (freeLayerTransferMatrix (S := S) a) where
  eigenvalue := freeLayerWalshEigenvalue (S := S) a
  changeOfBasis := freeLayerWalshMatrix (S := S)
  orthogonal_left := freeLayerWalshMatrix_orthogonal_left (S := S)
  orthogonal_right := freeLayerWalshMatrix_orthogonal_right (S := S)
  diagonalizes := freeLayerTransferMatrix_diagonalizes (S := S) a

end TransferMatrix

end IsingModel

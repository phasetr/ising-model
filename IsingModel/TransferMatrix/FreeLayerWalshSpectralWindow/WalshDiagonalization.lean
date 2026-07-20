import IsingModel.TransferMatrix.FreeLayerWalshSpectralWindow.WalshBasisOrthogonality
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Finite free-layer Walsh spectral window (2/4): Walsh diagonalization

Structural split (2/4) of `TransferMatrix.FreeLayerWalshSpectralWindow`.  This child
holds the diagonalization of the free-layer product transfer matrix by the Walsh basis:
the factorization of layer-state sums into independent one-site spin sums, the one-site
signed and unsigned transfer row sums giving the top and bottom `1D` eigenvalues, the
resulting eigenvector property of each (normalized) Walsh character, the column-wise
identity `T · W = W · diag(λ)`, and — using the sibling orthogonality — the full
diagonalization `T = W · diag(λ) · Wᵀ`.  It builds on the sibling
`...WalshBasisOrthogonality`.  See the `TransferMatrix.FreeLayerWalshSpectralWindow`
facade module for the full contents overview.
-/

namespace IsingModel

namespace TransferMatrix

open scoped BigOperators Matrix
open Finset

variable {S : Type*} [Fintype S] [DecidableEq S]

/-! ## Walsh diagonalization -/

/-- A spin product can be read as a product over all sites with trivial
factors off the index set. -/
theorem spinProduct_eq_univ_prod_ite (A : Finset S) (ω : LayerState S) :
    spinProduct A ω =
      ∏ x : S, if x ∈ A then Spin.sign ℝ (ω x) else 1 := by
  classical
  simp [spinProduct, Spin.sign]

/-- Sums over all layer states factor into independent one-site spin sums. -/
theorem sum_layerState_prod_eq_prod_sum_spin (g : S → Spin → ℝ) :
    ∑ η : LayerState S, ∏ x : S, g x (η x) =
      ∏ x : S, ∑ s : Spin, g x s := by
  classical
  simpa [LayerState, Config] using
    (Fintype.prod_sum (ι := S) (κ := fun _ => Spin) (R := ℝ) g).symm

/-- The one-site transfer row sum is the top eigenvalue. -/
theorem isingTransferMatrix1D_sum_spin (a : ℝ) (s : Spin) :
    ∑ t : Spin,
      isingTransferMatrix1D a (spinEquivFin2 s) (spinEquivFin2 t) =
        transferEigenvalueTop a := by
  rw [Fintype.sum_equiv spinEquivFin2
    (fun t : Spin => isingTransferMatrix1D a (spinEquivFin2 s) (spinEquivFin2 t))
    (fun i : Fin 2 => isingTransferMatrix1D a (spinEquivFin2 s) i) (by intro x; rfl)]
  cases s
  · simp [Fin.sum_univ_two, isingTransferMatrix1D, spinEquivFin2, spin1D,
      transferEigenvalueTop]
  · simp [Fin.sum_univ_two, isingTransferMatrix1D, spinEquivFin2, spin1D,
      transferEigenvalueTop]
    ring

/-- The signed one-site transfer row sum is the bottom eigenvalue times the
input spin sign. -/
theorem isingTransferMatrix1D_sum_spin_sign (a : ℝ) (s : Spin) :
    ∑ t : Spin,
      isingTransferMatrix1D a (spinEquivFin2 s) (spinEquivFin2 t) *
        Spin.sign ℝ t =
        transferEigenvalueBot a * Spin.sign ℝ s := by
  rw [Fintype.sum_equiv spinEquivFin2
    (fun t : Spin =>
      isingTransferMatrix1D a (spinEquivFin2 s) (spinEquivFin2 t) * Spin.sign ℝ t)
    (fun i : Fin 2 =>
      isingTransferMatrix1D a (spinEquivFin2 s) i *
        Spin.sign ℝ (spinEquivFin2.symm i)) (by intro x; simp)]
  cases s <;>
    simp [Fin.sum_univ_two, isingTransferMatrix1D, spinEquivFin2, spin1D,
      transferEigenvalueBot, Spin.sign, Spin.toSign] <;>
    ring

/-- The row product times a Walsh character is a single product of signed
one-site factors. -/
theorem freeLayerTransferMatrix_row_mul_spinProduct_eq_prod
    (a : ℝ) (A : Finset S) (ω η : LayerState S) :
    freeLayerTransferMatrix (S := S) a ω η * spinProduct A η =
      ∏ x : S,
        isingTransferMatrix1D a (spinEquivFin2 (ω x)) (spinEquivFin2 (η x)) *
          (if x ∈ A then Spin.sign ℝ (η x) else 1) := by
  classical
  rw [freeLayerTransferMatrix, spinProduct_eq_univ_prod_ite]
  rw [← Finset.prod_mul_distrib]

/-- The number of sites outside an index set. -/
theorem card_univ_filter_not_mem (A : Finset S) :
    #(Finset.univ.filter fun x : S => ¬ x ∈ A) = Fintype.card S - A.card := by
  classical
  have h :=
    Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset S))
      (p := fun x : S => x ∈ A)
  simp at h
  omega

/-- The all-site product of one-site Walsh eigenvalues gives the finite-layer
Walsh eigenvalue times the character. -/
theorem freeLayerWalsh_product_if_eigen
    (a : ℝ) (A : Finset S) (ω : LayerState S) :
    (∏ x : S,
        if x ∈ A then transferEigenvalueBot a * Spin.sign ℝ (ω x)
        else transferEigenvalueTop a) =
      (transferEigenvalueTop a ^ (Fintype.card S - A.card) *
        transferEigenvalueBot a ^ A.card) * spinProduct A ω := by
  classical
  rw [← Finset.prod_filter_mul_prod_filter_not (s := (Finset.univ : Finset S))
    (p := fun x : S => x ∈ A)
    (f := fun x =>
      if x ∈ A then transferEigenvalueBot a * Spin.sign ℝ (ω x)
      else transferEigenvalueTop a)]
  have hmem :
      (∏ x ∈ (Finset.univ.filter fun x : S => x ∈ A),
        if x ∈ A then transferEigenvalueBot a * Spin.sign ℝ (ω x)
        else transferEigenvalueTop a) =
        transferEigenvalueBot a ^ A.card * spinProduct A ω := by
    calc
      (∏ x ∈ (Finset.univ.filter fun x : S => x ∈ A),
        if x ∈ A then transferEigenvalueBot a * Spin.sign ℝ (ω x)
        else transferEigenvalueTop a)
          = ∏ x ∈ A, transferEigenvalueBot a * Spin.sign ℝ (ω x) := by
            refine Finset.prod_congr ?_ ?_
            · ext x
              simp
            · intro x hx
              simp at hx
              simp [hx]
      _ = transferEigenvalueBot a ^ A.card * spinProduct A ω := by
            simp [spinProduct, Spin.sign, Finset.prod_mul_distrib, Finset.prod_const]
  have hnot :
      (∏ x ∈ (Finset.univ.filter fun x : S => ¬ x ∈ A),
        if x ∈ A then transferEigenvalueBot a * Spin.sign ℝ (ω x)
        else transferEigenvalueTop a) =
        transferEigenvalueTop a ^ (Fintype.card S - A.card) := by
    calc
      (∏ x ∈ (Finset.univ.filter fun x : S => ¬ x ∈ A),
        if x ∈ A then transferEigenvalueBot a * Spin.sign ℝ (ω x)
        else transferEigenvalueTop a)
          = ∏ x ∈ (Finset.univ.filter fun x : S => ¬ x ∈ A),
              transferEigenvalueTop a := by
            refine Finset.prod_congr rfl ?_
            intro x hx
            simp at hx
            simp [hx]
      _ = transferEigenvalueTop a ^ #(Finset.univ.filter fun x : S => ¬ x ∈ A) := by
            rw [Finset.prod_const]
      _ = transferEigenvalueTop a ^ (Fintype.card S - A.card) := by
            rw [card_univ_filter_not_mem]
  rw [hmem, hnot]
  ring

/-- Each unnormalized Walsh character is an eigenvector of the finite
free-layer transfer matrix. -/
theorem freeLayerTransferMatrix_mulVec_spinProduct
    (a : ℝ) (A : Finset S) :
    (freeLayerTransferMatrix (S := S) a).mulVec (spinProduct A) =
      (transferEigenvalueTop a ^ (Fintype.card S - A.card) *
        transferEigenvalueBot a ^ A.card) • spinProduct A := by
  classical
  funext ω
  calc
    (freeLayerTransferMatrix (S := S) a).mulVec (spinProduct A) ω
        = ∑ η : LayerState S,
            freeLayerTransferMatrix (S := S) a ω η * spinProduct A η := by
          simp [Matrix.mulVec, dotProduct]
    _ = ∑ η : LayerState S,
          ∏ x : S,
            isingTransferMatrix1D a (spinEquivFin2 (ω x)) (spinEquivFin2 (η x)) *
              (if x ∈ A then Spin.sign ℝ (η x) else 1) := by
          refine Finset.sum_congr rfl ?_
          intro η _
          exact freeLayerTransferMatrix_row_mul_spinProduct_eq_prod a A ω η
    _ = ∏ x : S,
          ∑ t : Spin,
            isingTransferMatrix1D a (spinEquivFin2 (ω x)) (spinEquivFin2 t) *
              (if x ∈ A then Spin.sign ℝ t else 1) := by
          exact
            sum_layerState_prod_eq_prod_sum_spin (S := S)
              (g := fun x t =>
                isingTransferMatrix1D a (spinEquivFin2 (ω x)) (spinEquivFin2 t) *
                  (if x ∈ A then Spin.sign ℝ t else 1))
    _ = ∏ x : S,
          if x ∈ A then transferEigenvalueBot a * Spin.sign ℝ (ω x)
          else transferEigenvalueTop a := by
          refine Finset.prod_congr rfl ?_
          intro x _
          by_cases hx : x ∈ A
          · simp [hx, isingTransferMatrix1D_sum_spin_sign]
          · simp [hx, isingTransferMatrix1D_sum_spin]
    _ = (transferEigenvalueTop a ^ (Fintype.card S - A.card) *
          transferEigenvalueBot a ^ A.card) * spinProduct A ω := by
          exact freeLayerWalsh_product_if_eigen a A ω
    _ = ((transferEigenvalueTop a ^ (Fintype.card S - A.card) *
          transferEigenvalueBot a ^ A.card) • spinProduct A) ω := by
          rfl

/-- Each normalized Walsh column is an eigenvector of the finite free-layer
transfer matrix. -/
theorem freeLayerTransferMatrix_mulVec_freeLayerWalshColumn
    (a : ℝ) (A : Finset S) :
    (freeLayerTransferMatrix (S := S) a).mulVec
        (freeLayerWalshColumn (S := S) A) =
      freeLayerWalshEigenvalue (S := S) a
        (layerStateDownSetEquivFinset.symm A) •
          freeLayerWalshColumn (S := S) A := by
  classical
  let c : ℝ := (Fintype.card (LayerState S) : ℝ)⁻¹.sqrt
  have hcol : freeLayerWalshColumn (S := S) A = c • spinProduct A := by
    funext ω
    simp [freeLayerWalshColumn, c]
  have heig :
      freeLayerWalshEigenvalue (S := S) a (layerStateDownSetEquivFinset.symm A) =
        transferEigenvalueTop a ^ (Fintype.card S - A.card) *
          transferEigenvalueBot a ^ A.card := by
    have hdown :
        layerStateDownSet (layerStateDownSetEquivFinset.symm A : LayerState S) = A :=
      layerStateDownSetEquivFinset.right_inv A
    simp [freeLayerWalshEigenvalue, hdown]
  rw [hcol, Matrix.mulVec_smul, freeLayerTransferMatrix_mulVec_spinProduct]
  funext ω
  simp [heig, Pi.smul_apply, smul_eq_mul]
  ring_nf

/-- The finite free-layer transfer matrix maps the Walsh matrix columns by
their Walsh eigenvalues. -/
theorem freeLayerTransferMatrix_mul_freeLayerWalshMatrix (a : ℝ) :
    freeLayerTransferMatrix (S := S) a * freeLayerWalshMatrix (S := S) =
      freeLayerWalshMatrix (S := S) *
        Matrix.diagonal (freeLayerWalshEigenvalue (S := S) a) := by
  classical
  ext ω χ
  have h :=
    congr_fun
      (freeLayerTransferMatrix_mulVec_freeLayerWalshColumn (S := S) a
        (layerStateDownSet χ)) ω
  have hχ : layerStateDownSetEquivFinset.symm (layerStateDownSet χ) = χ :=
    layerStateDownSetEquivFinset.left_inv χ
  rw [Matrix.mul_diagonal]
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, freeLayerWalshMatrix,
    hχ, smul_eq_mul, mul_comm] using h

/-! ## Full diagonalization -/

/-- The finite free-layer transfer matrix is diagonalized by the Walsh matrix. -/
theorem freeLayerTransferMatrix_diagonalizes (a : ℝ) :
    freeLayerTransferMatrix (S := S) a =
      freeLayerWalshMatrix (S := S) *
        Matrix.diagonal (freeLayerWalshEigenvalue (S := S) a) *
        (freeLayerWalshMatrix (S := S))ᵀ := by
  calc
    freeLayerTransferMatrix (S := S) a
        = freeLayerTransferMatrix (S := S) a *
          (1 : Matrix (LayerState S) (LayerState S) ℝ) := by
          rw [Matrix.mul_one]
    _ = freeLayerTransferMatrix (S := S) a *
          (freeLayerWalshMatrix (S := S) * (freeLayerWalshMatrix (S := S))ᵀ) := by
          rw [freeLayerWalshMatrix_orthogonal_right]
    _ = (freeLayerTransferMatrix (S := S) a * freeLayerWalshMatrix (S := S)) *
          (freeLayerWalshMatrix (S := S))ᵀ := by
          rw [Matrix.mul_assoc]
    _ = (freeLayerWalshMatrix (S := S) *
          Matrix.diagonal (freeLayerWalshEigenvalue (S := S) a)) *
          (freeLayerWalshMatrix (S := S))ᵀ := by
          rw [freeLayerTransferMatrix_mul_freeLayerWalshMatrix]
    _ = freeLayerWalshMatrix (S := S) *
          Matrix.diagonal (freeLayerWalshEigenvalue (S := S) a) *
          (freeLayerWalshMatrix (S := S))ᵀ := rfl

end TransferMatrix

end IsingModel

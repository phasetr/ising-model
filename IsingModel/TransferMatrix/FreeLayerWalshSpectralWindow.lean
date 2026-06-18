import IsingModel.TransferMatrix.TwoSiteFreeLayerSpectralWindow
import IsingModel.TransferMatrix.LayerCardinalitySmallRatio
import IsingModel.Inequalities.NonnegCorrelations
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.SymmDiff

/-!
# Finite free-layer Walsh spectral window

This file extends the one-site and two-site free-layer spectral-window bridges
to an arbitrary finite transverse layer with no transverse edges, zero external
field, and identity longitudinal transition pairs.  The balanced transfer
matrix factors into independent one-dimensional transfer matrices, and the
finite Walsh characters give an explicit orthogonal spectral basis.

The final certificate uses the honest finite prefactor threshold
`tanh (p.β * p.J) < (2 ^ Fintype.card S - 1)⁻¹`.  This deliberately does not
claim an interacting transverse-layer spectral window or make `theta < 1`
sufficient in a larger state space.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

open scoped BigOperators Matrix
open Finset

variable {S : Type*} [Fintype S] [DecidableEq S]

/-! ## Walsh coordinates -/

/-- The down-spin set of a layer state. -/
def layerStateDownSet (ω : LayerState S) : Finset S :=
  Finset.univ.filter fun x => ω x = Spin.down

/-- A layer state is equivalently its finite set of down spins. -/
def layerStateDownSetEquivFinset : LayerState S ≃ Finset S where
  toFun := layerStateDownSet
  invFun A := fun x => if x ∈ A then Spin.down else Spin.up
  left_inv := by
    intro ω
    funext x
    by_cases hx : x ∈ layerStateDownSet ω
    · have hω : ω x = Spin.down := by
        simpa [layerStateDownSet] using hx
      simp [layerStateDownSet, hω]
    · have hω : ω x ≠ Spin.down := by
        simpa [layerStateDownSet] using hx
      cases hspin : ω x <;> simp [layerStateDownSet, hspin] at hω ⊢
  right_inv := by
    intro A
    ext x
    simp [layerStateDownSet]

/-- The all-up Walsh index, transported back to layer states. -/
def freeLayerWalshTop : LayerState S :=
  layerStateDownSetEquivFinset.symm ∅

/-- The Walsh column indexed by a finite set of sites. -/
noncomputable def freeLayerWalshColumn (A : Finset S) (ω : LayerState S) : ℝ :=
  (Fintype.card (LayerState S) : ℝ)⁻¹.sqrt * spinProduct A ω

/-- The finite Walsh matrix with layer-state columns encoded by down-spin sets. -/
noncomputable def freeLayerWalshMatrix : Matrix (LayerState S) (LayerState S) ℝ :=
  fun ω χ => freeLayerWalshColumn (layerStateDownSet χ) ω

/-- The free-layer transfer matrix as a product of independent 1D transfer
matrix entries. -/
noncomputable def freeLayerTransferMatrix (a : ℝ) :
    Matrix (LayerState S) (LayerState S) ℝ :=
  fun ω η =>
    ∏ x : S,
      isingTransferMatrix1D a (spinEquivFin2 (ω x)) (spinEquivFin2 (η x))

/-- Walsh eigenvalues for the finite free-layer transfer matrix. -/
noncomputable def freeLayerWalshEigenvalue (a : ℝ) (χ : LayerState S) : ℝ :=
  transferEigenvalueTop a ^ (Fintype.card S - (layerStateDownSet χ).card) *
    transferEigenvalueBot a ^ (layerStateDownSet χ).card

/-- The Walsh top index has the empty down-spin set. -/
@[simp]
theorem layerStateDownSet_freeLayerWalshTop :
    layerStateDownSet (freeLayerWalshTop (S := S)) = ∅ := by
  exact layerStateDownSetEquivFinset.right_inv ∅

/-- The Walsh top eigenvalue is the all-top product. -/
theorem freeLayerWalshEigenvalue_top (a : ℝ) :
    freeLayerWalshEigenvalue (S := S) a (freeLayerWalshTop (S := S)) =
      transferEigenvalueTop a ^ Fintype.card S := by
  simp [freeLayerWalshEigenvalue]

/-- A one-dimensional transfer entry in the Hadamard eigenbasis, written in
spin coordinates. -/
theorem isingTransferMatrix1D_spinEquivFin2_eq_half_top_bot
    (a : ℝ) (s t : Spin) :
    isingTransferMatrix1D a (spinEquivFin2 s) (spinEquivFin2 t) =
      (1 / 2) *
        (transferEigenvalueTop a +
          transferEigenvalueBot a * (Spin.sign ℝ s * Spin.sign ℝ t)) := by
  cases s <;> cases t <;>
    simp [isingTransferMatrix1D, spinEquivFin2, spin1D, transferEigenvalueTop,
      transferEigenvalueBot, Spin.sign, Spin.toSign] <;>
    ring

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

/-! ## Orthogonality -/

/-- The Walsh column product sums to zero unless the indices are equal. -/
theorem freeLayerWalsh_sum_spinProduct_mul (A B : Finset S) :
    ∑ ω : LayerState S, spinProduct A ω * spinProduct B ω =
      if A = B then (Fintype.card (LayerState S) : ℝ) else 0 := by
  classical
  by_cases hAB : A = B
  · subst B
    simp_rw [← sq]
    simp [spinProduct_sq]
  · have hne : (symmDiff A B).Nonempty := by
      exact Finset.symmDiff_nonempty.mpr hAB
    rw [show (∑ ω : LayerState S, spinProduct A ω * spinProduct B ω)
        = ∑ ω : LayerState S, spinProduct (symmDiff A B) ω by
          refine Finset.sum_congr rfl ?_
          intro ω _
          exact spinProduct_mul A B ω]
    simpa [hAB] using sum_config_spinProduct_eq_zero (symmDiff A B) hne

/-- The finite Walsh matrix is left-orthogonal. -/
theorem freeLayerWalshMatrix_orthogonal_left :
    (freeLayerWalshMatrix (S := S))ᵀ * freeLayerWalshMatrix =
      (1 : Matrix (LayerState S) (LayerState S) ℝ) := by
  classical
  ext χ ψ
  rw [Matrix.mul_apply]
  by_cases hχψ : χ = ψ
  · subst ψ
    have hcard_pos : 0 < (Fintype.card (LayerState S) : ℝ) := by
      exact_mod_cast Fintype.card_pos
    have hsqrt_sq :
        (√((Fintype.card (LayerState S) : ℝ))) ^ 2 =
          (Fintype.card (LayerState S) : ℝ) :=
      Real.sq_sqrt hcard_pos.le
    have hsum :
        ∑ x : LayerState S,
          spinProduct (layerStateDownSet χ) x *
            spinProduct (layerStateDownSet χ) x =
        (Fintype.card (LayerState S) : ℝ) := by
      simpa using
        freeLayerWalsh_sum_spinProduct_mul (S := S)
          (layerStateDownSet χ) (layerStateDownSet χ)
    have hentry :
        ∑ x : LayerState S,
            freeLayerWalshMatrix x χ * freeLayerWalshMatrix x χ = 1 := by
      calc
      ∑ x : LayerState S,
          freeLayerWalshMatrix x χ * freeLayerWalshMatrix x χ
          =
          ∑ x : LayerState S,
            (√((Fintype.card (LayerState S) : ℝ)))⁻¹ *
              (√((Fintype.card (LayerState S) : ℝ)))⁻¹ *
              (spinProduct (layerStateDownSet χ) x *
                spinProduct (layerStateDownSet χ) x) := by
            refine Finset.sum_congr rfl ?_
            intro x _
            simp [freeLayerWalshMatrix, freeLayerWalshColumn]
            ring
      _ =
        (√((Fintype.card (LayerState S) : ℝ)))⁻¹ *
          (√((Fintype.card (LayerState S) : ℝ)))⁻¹ *
            (∑ x : LayerState S,
              spinProduct (layerStateDownSet χ) x *
                spinProduct (layerStateDownSet χ) x) := by
            rw [Finset.mul_sum]
      _ = 1 := by
            rw [hsum]
            field_simp [hcard_pos.ne']
            exact hsqrt_sq.symm
    simpa using hentry
  · have hsets : layerStateDownSet χ ≠ layerStateDownSet ψ := by
      intro h
      exact hχψ (layerStateDownSetEquivFinset.injective h)
    have hsum :
        ∑ x : LayerState S,
          spinProduct (layerStateDownSet χ) x *
            spinProduct (layerStateDownSet ψ) x = 0 := by
      simpa [hsets] using
        freeLayerWalsh_sum_spinProduct_mul (S := S)
          (layerStateDownSet χ) (layerStateDownSet ψ)
    have hentry :
        ∑ x : LayerState S,
            freeLayerWalshMatrix x χ * freeLayerWalshMatrix x ψ = 0 := by
      calc
      ∑ x : LayerState S,
          freeLayerWalshMatrix x χ * freeLayerWalshMatrix x ψ
          =
          ∑ x : LayerState S,
            (√((Fintype.card (LayerState S) : ℝ)))⁻¹ *
              (√((Fintype.card (LayerState S) : ℝ)))⁻¹ *
              (spinProduct (layerStateDownSet χ) x *
                spinProduct (layerStateDownSet ψ) x) := by
            refine Finset.sum_congr rfl ?_
            intro x _
            simp [freeLayerWalshMatrix, freeLayerWalshColumn]
            ring
      _ =
        (√((Fintype.card (LayerState S) : ℝ)))⁻¹ *
          (√((Fintype.card (LayerState S) : ℝ)))⁻¹ *
            (∑ x : LayerState S,
              spinProduct (layerStateDownSet χ) x *
                spinProduct (layerStateDownSet ψ) x) := by
            rw [Finset.mul_sum]
      _ = 0 := by
            rw [hsum, mul_zero]
    simpa [hχψ] using hentry

/-- The finite Walsh matrix is right-orthogonal. -/
theorem freeLayerWalshMatrix_orthogonal_right :
    freeLayerWalshMatrix (S := S) * (freeLayerWalshMatrix (S := S))ᵀ =
      (1 : Matrix (LayerState S) (LayerState S) ℝ) := by
  classical
  exact mul_eq_one_comm.mp (freeLayerWalshMatrix_orthogonal_left (S := S))

/-! ## Walsh diagonalization, continued -/

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

/-- The finite free-layer Walsh transfer data. -/
noncomputable def freeLayerTransferOrthogonalSpectralData
    (a : ℝ) :
    RealOrthogonalSpectralData (freeLayerTransferMatrix (S := S) a) where
  eigenvalue := freeLayerWalshEigenvalue (S := S) a
  changeOfBasis := freeLayerWalshMatrix (S := S)
  orthogonal_left := freeLayerWalshMatrix_orthogonal_left (S := S)
  orthogonal_right := freeLayerWalshMatrix_orthogonal_right (S := S)
  diagonalizes := freeLayerTransferMatrix_diagonalizes (S := S) a

/-- The finite free-layer Walsh top column is invariant under global spin
flip. -/
theorem freeLayerWalshMatrix_top_flip_even :
    ∀ ω : LayerState S,
      freeLayerWalshMatrix (S := S) (layerStateFlipEquiv S ω)
          (freeLayerWalshTop (S := S)) =
        freeLayerWalshMatrix (S := S) ω (freeLayerWalshTop (S := S)) := by
  intro ω
  simp [freeLayerWalshMatrix, freeLayerWalshColumn]

/-- Physical finite free-layer Walsh spectral data. -/
noncomputable def freeLayerPhysicalOrthogonalSpectralData
    (p : IsingParams ℝ) (hp : p.h = 0) :
    RealOrthogonalSpectralData
      (layerSymmetricTransferMatrix
        (layerInternalWeight (⊥ : SimpleGraph S) p)
        (layerTransitionWeight (layerIdentityTransitionPairs S) p)) where
  eigenvalue :=
    (freeLayerTransferOrthogonalSpectralData (S := S) (p.β * p.J)).eigenvalue
  changeOfBasis :=
    (freeLayerTransferOrthogonalSpectralData (S := S) (p.β * p.J)).changeOfBasis
  orthogonal_left :=
    (freeLayerTransferOrthogonalSpectralData (S := S) (p.β * p.J)).orthogonal_left
  orthogonal_right :=
    (freeLayerTransferOrthogonalSpectralData (S := S) (p.β * p.J)).orthogonal_right
  diagonalizes := by
    rw [layerSymmetricTransferMatrix_bot_identity_eq_freeLayerTransferMatrix p hp]
    exact (freeLayerTransferOrthogonalSpectralData (S := S) (p.β * p.J)).diagonalizes

/-- Conditional finite free-layer balanced min-gap certificate from the explicit
Walsh subdominant bound.

The smallness hypothesis uses the honest finite-cardinality threshold
`tanh (p.β * p.J) < (2 ^ Fintype.card S - 1)⁻¹`. -/
noncomputable def freeLayerBalancedMinGapCertificate_tanh_of_walshBounds
    [Nonempty S] (p : IsingParams ℝ) (hp : p.h = 0) (hβJ : 0 < p.β * p.J)
    (hsmall :
      Real.tanh (p.β * p.J) <
        (((2 ^ Fintype.card S - 1 : ℕ) : ℝ))⁻¹)
    (hsub :
      ∀ i, i ≠ freeLayerWalshTop (S := S) →
        |freeLayerWalshEigenvalue (S := S) (p.β * p.J) i| ≤
          Real.tanh (p.β * p.J) *
            (transferEigenvalueTop (p.β * p.J) ^ Fintype.card S))
    (x : S) :
    LayerBalancedMinSpectralGapCertificate
      (layerInternalWeight (⊥ : SimpleGraph S) p)
      (layerTransitionWeight (layerIdentityTransitionPairs S) p)
      (layerSpinAt x) := by
  let E := freeLayerPhysicalOrthogonalSpectralData (S := S) p hp
  let top : LayerState S := freeLayerWalshTop (S := S)
  refine
    layerBalancedMinSpectralGapCertificate_of_orthogonalDominantBounds_flipEvenSpin
      (layerInternalWeight (⊥ : SimpleGraph S) p)
      (layerTransitionWeight (layerIdentityTransitionPairs S) p)
      x
      E top
      (transferEigenvalueTop (p.β * p.J) ^ Fintype.card S)
      (Real.tanh (p.β * p.J))
      (pow_pos (transferEigenvalueTop_pos (p.β * p.J)) _) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [Real.tanh_eq_sinh_div_cosh]
    exact le_of_lt (div_pos (Real.sinh_pos_iff.mpr hβJ) (Real.cosh_pos _))
  · exact Real.tanh_lt_one (p.β * p.J)
  · exact
      finiteSpectralPartitionPrefactor_small_of_layerState_lt_inv_two_pow_cardSubOne
        S hsmall
  · simp [E, top, freeLayerPhysicalOrthogonalSpectralData,
      freeLayerTransferOrthogonalSpectralData, freeLayerWalshEigenvalue_top]
  · intro i hi
    simpa [E, top, freeLayerPhysicalOrthogonalSpectralData,
      freeLayerTransferOrthogonalSpectralData] using hsub i hi
  · simpa [E, top, freeLayerPhysicalOrthogonalSpectralData,
      freeLayerTransferOrthogonalSpectralData] using
        freeLayerWalshMatrix_top_flip_even (S := S)

end TransferMatrix

end IsingModel

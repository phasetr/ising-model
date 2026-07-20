import IsingModel.Inequalities.NonnegCorrelations
import IsingModel.TransferMatrix.OneSiteLayerSpectralWindow
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Finite free-layer Walsh spectral window (1/4): Walsh basis and orthogonality

Structural split (1/4) of `TransferMatrix.FreeLayerWalshSpectralWindow`.  This child
holds the Walsh coordinates on a finite transverse layer — the down-spin set of a layer
state and its equivalence with `Finset S`, the all-up Walsh index, the normalized Walsh
columns and the Walsh matrix, the free-layer product transfer matrix and its Walsh
eigenvalues — together with the orthogonality of the Walsh matrix: the character sum
`∑_ω σ_A(ω) σ_B(ω)` vanishes unless `A = B`, whence the Walsh matrix is orthogonal on
both sides.  It is the base of the chain and is imported by all sibling children.  See
the `TransferMatrix.FreeLayerWalshSpectralWindow` facade module for the full contents
overview.
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

end TransferMatrix

end IsingModel

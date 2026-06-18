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

/-- The finite free-layer Walsh transfer data, conditional on the displayed
diagonalization identity for the free product matrix. -/
noncomputable def freeLayerTransferOrthogonalSpectralData
    (a : ℝ)
    (hdiag :
      freeLayerTransferMatrix (S := S) a =
        freeLayerWalshMatrix (S := S) *
          Matrix.diagonal (freeLayerWalshEigenvalue (S := S) a) *
          (freeLayerWalshMatrix (S := S))ᵀ) :
    RealOrthogonalSpectralData (freeLayerTransferMatrix (S := S) a) where
  eigenvalue := freeLayerWalshEigenvalue (S := S) a
  changeOfBasis := freeLayerWalshMatrix (S := S)
  orthogonal_left := freeLayerWalshMatrix_orthogonal_left (S := S)
  orthogonal_right := freeLayerWalshMatrix_orthogonal_right (S := S)
  diagonalizes := hdiag

/-- The finite free-layer Walsh top column is invariant under global spin
flip. -/
theorem freeLayerWalshMatrix_top_flip_even :
    ∀ ω : LayerState S,
      freeLayerWalshMatrix (S := S) (layerStateFlipEquiv S ω)
          (freeLayerWalshTop (S := S)) =
        freeLayerWalshMatrix (S := S) ω (freeLayerWalshTop (S := S)) := by
  intro ω
  simp [freeLayerWalshMatrix, freeLayerWalshColumn]

/-- Physical finite free-layer Walsh spectral data, conditional on the explicit
Walsh diagonalization of the free product matrix. -/
noncomputable def freeLayerPhysicalOrthogonalSpectralData
    (p : IsingParams ℝ) (hp : p.h = 0)
    (hdiag :
      freeLayerTransferMatrix (S := S) (p.β * p.J) =
        freeLayerWalshMatrix (S := S) *
          Matrix.diagonal (freeLayerWalshEigenvalue (S := S) (p.β * p.J)) *
          (freeLayerWalshMatrix (S := S))ᵀ) :
    RealOrthogonalSpectralData
      (layerSymmetricTransferMatrix
        (layerInternalWeight (⊥ : SimpleGraph S) p)
        (layerTransitionWeight (layerIdentityTransitionPairs S) p)) where
  eigenvalue :=
    (freeLayerTransferOrthogonalSpectralData (S := S) (p.β * p.J) hdiag).eigenvalue
  changeOfBasis :=
    (freeLayerTransferOrthogonalSpectralData (S := S) (p.β * p.J) hdiag).changeOfBasis
  orthogonal_left :=
    (freeLayerTransferOrthogonalSpectralData (S := S) (p.β * p.J) hdiag).orthogonal_left
  orthogonal_right :=
    (freeLayerTransferOrthogonalSpectralData (S := S) (p.β * p.J) hdiag).orthogonal_right
  diagonalizes := by
    rw [layerSymmetricTransferMatrix_bot_identity_eq_freeLayerTransferMatrix p hp]
    exact (freeLayerTransferOrthogonalSpectralData (S := S) (p.β * p.J) hdiag).diagonalizes

/-- Conditional finite free-layer balanced min-gap certificate from the Walsh
diagonalization identity and the explicit Walsh subdominant bound.

The smallness hypothesis uses the honest finite-cardinality threshold
`tanh (p.β * p.J) < (2 ^ Fintype.card S - 1)⁻¹`. -/
noncomputable def freeLayerBalancedMinGapCertificate_tanh_of_walshBounds
    [Nonempty S] (p : IsingParams ℝ) (hp : p.h = 0) (hβJ : 0 < p.β * p.J)
    (hsmall :
      Real.tanh (p.β * p.J) <
        (((2 ^ Fintype.card S - 1 : ℕ) : ℝ))⁻¹)
    (hdiag :
      freeLayerTransferMatrix (S := S) (p.β * p.J) =
        freeLayerWalshMatrix (S := S) *
          Matrix.diagonal (freeLayerWalshEigenvalue (S := S) (p.β * p.J)) *
          (freeLayerWalshMatrix (S := S))ᵀ)
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
  let E := freeLayerPhysicalOrthogonalSpectralData (S := S) p hp hdiag
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

import IsingModel.TransferMatrix.FreeLayerWalshSpectralWindow.PhysicalBridgeSpectralWindow
import IsingModel.TransferMatrix.LayerCardinalitySmallRatio
import Mathlib.Algebra.Ring.Parity

/-!
# Finite free-layer Walsh spectral window (4/4): flip parity and min-gap certificates

Structural split (4/4) of `TransferMatrix.FreeLayerWalshSpectralWindow`.  This child
holds the behaviour of the Walsh basis under the global layer spin flip — a Walsh column
acquires the parity sign of its index, so even columns are flip-even and odd columns are
flip-odd, and the top column is flip-even and signed-positive — and assembles the
physical zero-field free-layer spectral data with its flip-parity adaptation.  It closes
with the conditional and the unconditional finite free-layer balanced min-gap
certificates, whose smallness hypothesis is the honest finite-cardinality threshold
`tanh (p.β * p.J) < (2 ^ Fintype.card S - 1)⁻¹`.  It builds on the sibling
`...PhysicalBridgeSpectralWindow`.  See the
`TransferMatrix.FreeLayerWalshSpectralWindow` facade module for the full contents
overview.
-/

namespace IsingModel

namespace TransferMatrix

open scoped BigOperators Matrix
open Finset

variable {S : Type*} [Fintype S] [DecidableEq S]

omit [Fintype S] [DecidableEq S] in
/-- Spin products acquire the parity sign of their support under global layer
spin flip. -/
theorem spinProduct_layerStateFlipEquiv (A : Finset S) (ω : LayerState S) :
    spinProduct A (layerStateFlipEquiv S ω) =
      (-1 : ℝ) ^ A.card * spinProduct A ω := by
  simp only [layerStateFlipEquiv_apply, spinProduct, Config.flip]
  simp_rw [Spin.toSign_flip, Int.cast_neg]
  exact Finset.prod_neg _

/-- A Walsh column acquires the parity sign of its index under global layer
spin flip. -/
theorem freeLayerWalshColumn_flip (A : Finset S) (ω : LayerState S) :
    freeLayerWalshColumn A (layerStateFlipEquiv S ω) =
      (-1 : ℝ) ^ A.card * freeLayerWalshColumn A ω := by
  simp only [freeLayerWalshColumn, spinProduct_layerStateFlipEquiv]
  ring

/-- Even Walsh columns are invariant under global layer spin flip. -/
theorem freeLayerWalshColumn_flip_even_of_card_even
    {A : Finset S} (hA : Even A.card) :
    ∀ ω : LayerState S,
      freeLayerWalshColumn A (layerStateFlipEquiv S ω) =
        freeLayerWalshColumn A ω := by
  intro ω
  rw [freeLayerWalshColumn_flip, hA.neg_one_pow]
  ring

/-- Odd Walsh columns change sign under global layer spin flip. -/
theorem freeLayerWalshColumn_flip_odd_of_card_odd
    {A : Finset S} (hA : Odd A.card) :
    ∀ ω : LayerState S,
      freeLayerWalshColumn A (layerStateFlipEquiv S ω) =
        -freeLayerWalshColumn A ω := by
  intro ω
  rw [freeLayerWalshColumn_flip, hA.neg_one_pow]
  ring

/-- The finite free-layer Walsh top column is invariant under global spin
flip. -/
theorem freeLayerWalshMatrix_top_flip_even :
    ∀ ω : LayerState S,
      freeLayerWalshMatrix (S := S) (layerStateFlipEquiv S ω)
          (freeLayerWalshTop (S := S)) =
        freeLayerWalshMatrix (S := S) ω (freeLayerWalshTop (S := S)) := by
  intro ω
  simp [freeLayerWalshMatrix, freeLayerWalshColumn]

/-- A Walsh spectral-data column with even down-set cardinality is flip-even. -/
theorem freeLayerTransferOrthogonalSpectralData_columnFlipEven_of_even_downSet
    (a : ℝ) {χ : LayerState S} (hχ : Even (layerStateDownSet χ).card) :
    (freeLayerTransferOrthogonalSpectralData (S := S) a).ColumnFlipEven
      (layerStateFlipEquiv S) χ := by
  intro ω
  exact freeLayerWalshColumn_flip_even_of_card_even (S := S) hχ ω

/-- A Walsh spectral-data column with odd down-set cardinality is flip-odd. -/
theorem freeLayerTransferOrthogonalSpectralData_columnFlipOdd_of_odd_downSet
    (a : ℝ) {χ : LayerState S} (hχ : Odd (layerStateDownSet χ).card) :
    (freeLayerTransferOrthogonalSpectralData (S := S) a).ColumnFlipOdd
      (layerStateFlipEquiv S) χ := by
  intro ω
  exact freeLayerWalshColumn_flip_odd_of_card_odd (S := S) hχ ω

/-- The finite free-layer Walsh spectral basis is adapted to global spin-flip
parity. -/
theorem freeLayerTransferOrthogonalSpectralData_columnFlipParity (a : ℝ) :
    (freeLayerTransferOrthogonalSpectralData (S := S) a).ColumnFlipParity
      (layerStateFlipEquiv S) := by
  intro χ
  rcases Nat.even_or_odd (layerStateDownSet χ).card with hχ | hχ
  · exact Or.inl
      (freeLayerTransferOrthogonalSpectralData_columnFlipEven_of_even_downSet
        (S := S) a hχ)
  · exact Or.inr
      (freeLayerTransferOrthogonalSpectralData_columnFlipOdd_of_odd_downSet
        (S := S) a hχ)

/-- The finite free-layer Walsh top spectral column is signed-positive. -/
noncomputable def freeLayerTransferOrthogonalSpectralData_top_signedPositiveColumn
    (a : ℝ) :
    (freeLayerTransferOrthogonalSpectralData (S := S) a).SignedPositiveColumn
      (freeLayerWalshTop (S := S)) := by
  refine ⟨1, by ring, ?_⟩
  intro ω
  have hcard_pos : 0 < (Fintype.card (LayerState S) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hinv_pos : 0 < (Fintype.card (LayerState S) : ℝ)⁻¹ :=
    inv_pos.mpr hcard_pos
  change 0 < 1 *
    freeLayerWalshMatrix (S := S) ω (freeLayerWalshTop (S := S))
  rw [one_mul]
  dsimp [freeLayerWalshMatrix, freeLayerWalshColumn]
  have htop : layerStateDownSet (freeLayerWalshTop (S := S)) = ∅ := by
    exact layerStateDownSetEquivFinset.right_inv ∅
  rw [htop, spinProduct_empty, mul_one]
  exact Real.sqrt_pos.mpr hinv_pos

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

/-- The physical zero-field free-layer Walsh spectral basis is adapted to
global spin-flip parity. -/
theorem freeLayerPhysicalOrthogonalSpectralData_columnFlipParity
    (p : IsingParams ℝ) (hp : p.h = 0) :
    (freeLayerPhysicalOrthogonalSpectralData (S := S) p hp).ColumnFlipParity
      (layerStateFlipEquiv S) := by
  simpa [freeLayerPhysicalOrthogonalSpectralData] using
    freeLayerTransferOrthogonalSpectralData_columnFlipParity
      (S := S) (p.β * p.J)

/-- The physical zero-field free-layer Walsh top spectral column is
signed-positive. -/
noncomputable def freeLayerPhysicalOrthogonalSpectralData_top_signedPositiveColumn
    (p : IsingParams ℝ) (hp : p.h = 0) :
    (freeLayerPhysicalOrthogonalSpectralData (S := S) p hp).SignedPositiveColumn
      (freeLayerWalshTop (S := S)) := by
  exact
    { freeLayerTransferOrthogonalSpectralData_top_signedPositiveColumn
        (S := S) (p.β * p.J) with }

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

/-- Finite free-layer balanced min-gap certificate from the proved Walsh
spectral window. -/
noncomputable def freeLayerBalancedMinGapCertificate_tanh
    [Nonempty S] (p : IsingParams ℝ) (hp : p.h = 0) (hβJ : 0 < p.β * p.J)
    (hsmall :
      Real.tanh (p.β * p.J) <
        (((2 ^ Fintype.card S - 1 : ℕ) : ℝ))⁻¹)
    (x : S) :
    LayerBalancedMinSpectralGapCertificate
      (layerInternalWeight (⊥ : SimpleGraph S) p)
      (layerTransitionWeight (layerIdentityTransitionPairs S) p)
      (layerSpinAt x) :=
  freeLayerBalancedMinGapCertificate_tanh_of_walshBounds
    (S := S) p hp hβJ hsmall
    (freeLayerWalshSpectralWindow_tanh (S := S) (le_of_lt hβJ)) x

end TransferMatrix

end IsingModel

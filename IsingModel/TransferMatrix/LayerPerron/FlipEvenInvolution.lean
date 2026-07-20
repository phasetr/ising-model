import IsingModel.TransferMatrix.LayerSpectral.Positivity
import IsingModel.TransferMatrix.LayerSpectral.BalancedMatrix
import IsingModel.TransferMatrix.LayerGibbs
import IsingModel.Basic
import Mathlib.Data.Matrix.Mul

/-!
# Positive/simple Perron bridge (3/5): involutions and flip-evenness

Structural split (3/5) of `TransferMatrix.LayerPerron`.  This child holds the involution
block: a strictly positive vector that is proportional to its pullback by an involution is
in fact invariant under it, hence a positive eigenvector spanning a simple eigenspace of a
matrix commuting with the involution is even; together with the layer-state global spin
flip as an involution and the corresponding statement for the balanced layer transfer
matrix.  See the `IsingModel.TransferMatrix.LayerPerron` facade module for the full
contents overview.
-/

namespace IsingModel

namespace TransferMatrix

open Matrix

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-! ## Positive simple eigenvectors and involutions -/

omit [Fintype Ω] [DecidableEq Ω] in
/-- A strictly positive vector cannot be a nontrivial scalar multiple of its
pullback by an involution. -/
theorem vectorPositive_comp_eq_self_of_involutive_smul [Nonempty Ω]
    (τ : Ω ≃ Ω) (hτ : ∀ i, τ (τ i) = i)
    {v : Ω → ℝ} (hv : VectorPositive v) {c : ℝ}
    (hc : v ∘ τ = c • v) :
    ∀ i, v (τ i) = v i := by
  have hc_apply : ∀ i, v (τ i) = c * v i := by
    intro i
    have h := congr_fun hc i
    simpa [Function.comp, Pi.smul_apply, smul_eq_mul] using h
  let i0 : Ω := Classical.arbitrary Ω
  have hc_pos : 0 < c := by
    have h := hc_apply i0
    have hvi : 0 < v i0 := hv i0
    have hvt : 0 < v (τ i0) := hv (τ i0)
    rw [h] at hvt
    nlinarith
  have hc_sq : c * c = 1 := by
    have h1 := hc_apply i0
    have h2 := hc_apply (τ i0)
    rw [hτ i0] at h2
    rw [h1] at h2
    have hvi : 0 < v i0 := hv i0
    nlinarith
  have hc_one : c = 1 := by
    nlinarith
  intro i
  rw [hc_apply i, hc_one, one_mul]

omit [DecidableEq Ω] in
/-- If a matrix commutes with an involution and a positive eigenvector spans its
eigenspace, then that eigenvector is invariant under the involution. -/
theorem vectorPositive_eigenvector_flip_even_of_simple_eigenspace [Nonempty Ω]
    {M : Matrix Ω Ω ℝ} (τ : Ω ≃ Ω) (hτ : ∀ i, τ (τ i) = i)
    {lam : ℝ} {v : Ω → ℝ}
    (hvpos : VectorPositive v)
    (hveig : M.mulVec v = lam • v)
    (hcomm : ∀ w : Ω → ℝ, M.mulVec (w ∘ τ) = M.mulVec w ∘ τ)
    (hsimple : ∀ w : Ω → ℝ, M.mulVec w = lam • w → ∃ c : ℝ, w = c • v) :
    ∀ i, v (τ i) = v i := by
  have hcomp_eig : M.mulVec (v ∘ τ) = lam • (v ∘ τ) := by
    rw [hcomm v, hveig]
    ext i
    simp [Function.comp, Pi.smul_apply, smul_eq_mul]
  rcases hsimple (v ∘ τ) hcomp_eig with ⟨c, hc⟩
  exact vectorPositive_comp_eq_self_of_involutive_smul τ hτ hvpos hc

/-! ## Balanced layer transfer matrix wrappers -/

/-- The global spin flip on layer states is an involution. -/
theorem layerStateFlipEquiv_involutive (S : Type*) (ω : LayerState S) :
    layerStateFlipEquiv S (layerStateFlipEquiv S ω) = ω := by
  rw [layerStateFlipEquiv_apply, layerStateFlipEquiv_apply]
  exact Config.flip_flip ω

/-- A positive eigenvector spanning a simple eigenspace of a balanced layer
transfer matrix is flip-even when the balanced transfer matrix commutes with
the global spin flip. -/
theorem layerSymmetricTransfer_positive_eigenvector_flip_even_of_simple_eigenspace
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    {lam : ℝ} {v : LayerState S → ℝ}
    (hvpos : VectorPositive v)
    (hveig : (layerSymmetricTransferMatrix u k).mulVec v = lam • v)
    (hsimple : ∀ w : LayerState S → ℝ,
      (layerSymmetricTransferMatrix u k).mulVec w = lam • w →
        ∃ c : ℝ, w = c • v) :
    ∀ ω, v (layerStateFlipEquiv S ω) = v ω := by
  letI : Nonempty (LayerState S) := ⟨fun _ => Spin.up⟩
  exact vectorPositive_eigenvector_flip_even_of_simple_eigenspace
    (τ := layerStateFlipEquiv S)
    (layerStateFlipEquiv_involutive S) hvpos hveig
    (layerSymmetricTransferMatrix_mulVec_comp_equiv u k (layerStateFlipEquiv S)
      hu_flip hk_flip)
    hsimple

end TransferMatrix

end IsingModel

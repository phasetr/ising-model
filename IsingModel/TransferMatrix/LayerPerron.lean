import IsingModel.TransferMatrix.LayerSpectral

/-!
# Positive/simple Perron-facing bridge for finite layer transfer matrices

This file records finite-dimensional consequences that are useful after a
Perron--Frobenius analysis has supplied a positive dominant eigenvector and a
one-dimensional dominant eigenspace.  It deliberately does not prove existence
of that eigenvector, spectral-radius maximality, a strict spectral gap,
thermodynamic limits, or open-slab estimates.

The main use for the layer route is to replace the direct `flip-even` dominant
column hypothesis from the spin-observable cancellation constructors by the
more natural inputs that the dominant column is positive and spans its
eigenspace.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.1, pp. 304--306.
-/

namespace IsingModel

namespace TransferMatrix

open Matrix

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

namespace RealOrthogonalSpectralData

/-- A column of explicit real orthogonal spectral data is a right eigenvector
with the corresponding spectral-data eigenvalue. -/
theorem mulVec_changeOfBasis_column {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (i : Ω) :
    M.mulVec (fun x => E.changeOfBasis x i)
      = E.eigenvalue i • (fun x => E.changeOfBasis x i) := by
  have hcol :
      E.changeOfBasisᵀ.mulVec (fun x => E.changeOfBasis x i) = Pi.single i 1 := by
    ext j
    have h := congr_fun (congr_fun E.orthogonal_left j) i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.one_apply,
      Pi.single_apply] using h
  calc
    M.mulVec (fun x => E.changeOfBasis x i)
        = (E.changeOfBasis * Matrix.diagonal E.eigenvalue * E.changeOfBasisᵀ).mulVec
            (fun x => E.changeOfBasis x i) := by
          exact congrArg (fun A => A.mulVec (fun x => E.changeOfBasis x i))
            E.diagonalizes
    _ = (E.changeOfBasis * Matrix.diagonal E.eigenvalue).mulVec (Pi.single i 1) := by
          rw [← Matrix.mulVec_mulVec, hcol]
    _ = E.eigenvalue i • (fun x => E.changeOfBasis x i) := by
          rw [Matrix.mulVec_single_one]
          ext j
          change (E.changeOfBasis * Matrix.diagonal E.eigenvalue) j i
            = (E.eigenvalue i • fun x => E.changeOfBasis x i) j
          rw [Matrix.mul_apply]
          rw [Finset.sum_eq_single i]
          · simp [Pi.smul_apply, smul_eq_mul, mul_comm]
          · intro b _ hb
            simp [hb]
          · intro hi
            exact (hi (Finset.mem_univ i)).elim

end RealOrthogonalSpectralData

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

/-- Orthogonal spectral-data constructor for spin observables using positive
simple dominant-column inputs instead of a direct flip-evenness hypothesis. -/
noncomputable def
    layerBalancedMinSpectralGapCertificate_of_orthogonalDominantBounds_positiveSimpleFlipSpin
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (top : LayerState S) (scale theta : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (partitionPrefactor_small :
      (((Fintype.card (LayerState S) - 1 : ℕ) : ℝ) * theta) < 1)
    (dominant_eigenvalue : E.eigenvalue top = scale)
    (subdominant_abs_le : ∀ i, i ≠ top → |E.eigenvalue i| ≤ theta * scale)
    (dominant_column_pos : VectorPositive (fun ω => E.changeOfBasis ω top))
    (dominant_eigenspace_simple : ∀ w : LayerState S → ℝ,
      (layerSymmetricTransferMatrix u k).mulVec w = E.eigenvalue top • w →
        ∃ c : ℝ, w = c • (fun ω => E.changeOfBasis ω top)) :
    LayerBalancedMinSpectralGapCertificate u k (layerSpinAt x) :=
  layerBalancedMinSpectralGapCertificate_of_orthogonalDominantBounds_flipEvenSpin
    u k x E top scale theta scale_pos theta_nonneg theta_lt_one
    partitionPrefactor_small dominant_eigenvalue subdominant_abs_le
    (layerSymmetricTransfer_positive_eigenvector_flip_even_of_simple_eigenspace
      u k hu_flip hk_flip dominant_column_pos (E.mulVec_changeOfBasis_column top)
      dominant_eigenspace_simple)

/-- Hermitian spectral-data constructor for spin observables using positive
simple dominant-column inputs instead of a direct flip-evenness hypothesis. -/
noncomputable def
    layerBalancedMinSpectralGapCertificate_of_layerHermitianDominantBounds_positiveSimpleFlipSpin
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hk : ∀ a b, k a b = k b a)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (top : LayerState S) (scale theta : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (partitionPrefactor_small :
      (((Fintype.card (LayerState S) - 1 : ℕ) : ℝ) * theta) < 1)
    (dominant_eigenvalue :
      (layerSymmetricTransferOrthogonalSpectralData u k hk).eigenvalue top = scale)
    (subdominant_abs_le : ∀ i, i ≠ top →
      |(layerSymmetricTransferOrthogonalSpectralData u k hk).eigenvalue i|
        ≤ theta * scale)
    (dominant_column_pos :
      VectorPositive
        (fun ω =>
          (layerSymmetricTransferOrthogonalSpectralData u k hk).changeOfBasis ω top))
    (dominant_eigenspace_simple : ∀ w : LayerState S → ℝ,
      (layerSymmetricTransferMatrix u k).mulVec w =
          (layerSymmetricTransferOrthogonalSpectralData u k hk).eigenvalue top • w →
        ∃ c : ℝ,
          w = c •
            (fun ω =>
              (layerSymmetricTransferOrthogonalSpectralData u k hk).changeOfBasis ω top)) :
    LayerBalancedMinSpectralGapCertificate u k (layerSpinAt x) :=
  layerBalancedMinSpectralGapCertificate_of_orthogonalDominantBounds_positiveSimpleFlipSpin
    u k x hu_flip hk_flip (layerSymmetricTransferOrthogonalSpectralData u k hk)
    top scale theta scale_pos theta_nonneg theta_lt_one partitionPrefactor_small
    dominant_eigenvalue subdominant_abs_le dominant_column_pos
    dominant_eigenspace_simple

end TransferMatrix

end IsingModel

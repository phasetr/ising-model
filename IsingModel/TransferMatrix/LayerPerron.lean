import IsingModel.TransferMatrix.LayerSpectral
import Mathlib.Data.Finset.Max

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

/-! ## Positive-column eigenvalue bounds -/

omit [Fintype Ω] [DecidableEq Ω] in
/-- A finite nonzero vector is bounded in absolute value by a positive vector,
with the optimal relative scale attained at some coordinate. -/
theorem exists_positive_vector_abs_bound_attained [Finite Ω] [Nonempty Ω]
    {v w : Ω → ℝ} (hv : VectorPositive v) (hw : w ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ (∀ i, |w i| ≤ C * v i) ∧ ∃ i, |w i| = C * v i := by
  classical
  letI := Fintype.ofFinite Ω
  obtain ⟨i0, hi0⟩ : ∃ i, w i ≠ 0 := by
    by_contra h
    apply hw
    ext i
    by_contra hwi
    exact h ⟨i, hwi⟩
  obtain ⟨i, _hi, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset Ω) (fun j => |w j| / v j)
      Finset.univ_nonempty
  refine ⟨|w i| / v i, ?_, ?_, ⟨i, ?_⟩⟩
  · have hratio0 : 0 < |w i0| / v i0 := div_pos (abs_pos.mpr hi0) (hv i0)
    exact hratio0.trans_le (hmax i0 (Finset.mem_univ i0))
  · intro j
    exact (div_le_iff₀ (hv j)).mp (hmax j (Finset.mem_univ j))
  · exact (div_mul_cancel₀ |w i| (hv i).ne').symm

omit [DecidableEq Ω] in
/-- If an entrywise positive real matrix has a strictly positive right
eigenpair, then any real right eigenvalue is bounded in absolute value by that
positive eigenvalue. -/
theorem abs_eigenvalue_le_of_entrywisePositive_positive_eigenpair [Nonempty Ω]
    {M : Matrix Ω Ω ℝ} (hM : MatrixEntrywisePositive M)
    {lam : ℝ} {v : Ω → ℝ} (hv : StrictPositiveRightEigenpair M lam v)
    {mu : ℝ} {w : Ω → ℝ} (hw_ne : w ≠ 0)
    (hw_eig : M.mulVec w = mu • w) :
    |mu| ≤ lam := by
  rcases exists_positive_vector_abs_bound_attained hv.1 hw_ne with
    ⟨C, hCpos, hbound, ⟨i, hatt⟩⟩
  have hCv_pos : 0 < C * v i := mul_pos hCpos (hv.1 i)
  have hsum_abs :
      |M.mulVec w i| ≤ ∑ j, M i j * |w j| := by
    calc
      |M.mulVec w i| = |∑ j, M i j * w j| := by
        simp [Matrix.mulVec, dotProduct]
      _ ≤ ∑ j, |M i j * w j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, M i j * |w j| := by
        apply Finset.sum_congr rfl
        intro j _hj
        rw [abs_mul, abs_of_pos (hM i j)]
  have hsum_bound :
      ∑ j, M i j * |w j| ≤ ∑ j, M i j * (C * v j) := by
    exact Finset.sum_le_sum fun j _hj =>
      mul_le_mul_of_nonneg_left (hbound j) (hM i j).le
  have hsum_eval :
      ∑ j, M i j * (C * v j) = lam * (C * v i) := by
    have hv_apply := congr_fun hv.2 i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hv_apply
    calc
      ∑ j, M i j * (C * v j) = ∑ j, C * (M i j * v j) := by
        apply Finset.sum_congr rfl
        intro j _hj
        ring
      _ = C * ∑ j, M i j * v j := by
        rw [Finset.mul_sum]
      _ = lam * (C * v i) := by
        rw [hv_apply]
        ring
  have hmain : |mu| * (C * v i) ≤ lam * (C * v i) := by
    calc
      |mu| * (C * v i) = |mu * w i| := by
        rw [← hatt, abs_mul]
      _ = |M.mulVec w i| := by
        have h := congr_fun hw_eig i
        simp only [Pi.smul_apply, smul_eq_mul] at h
        rw [h]
      _ ≤ ∑ j, M i j * |w j| := hsum_abs
      _ ≤ ∑ j, M i j * (C * v j) := hsum_bound
      _ = lam * (C * v i) := hsum_eval
  exact le_of_mul_le_mul_right hmain hCv_pos

namespace RealOrthogonalSpectralData

/-- A column of explicit orthogonal spectral data is nonzero. -/
theorem changeOfBasis_column_ne_zero {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (i : Ω) :
    (fun x => E.changeOfBasis x i) ≠ 0 := by
  intro hzero
  have hcol :
      E.changeOfBasisᵀ.mulVec (fun x => E.changeOfBasis x i) = Pi.single i 1 := by
    ext j
    have h := congr_fun (congr_fun E.orthogonal_left j) i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.one_apply,
      Pi.single_apply] using h
  have hleft : (E.changeOfBasisᵀ.mulVec (fun x => E.changeOfBasis x i)) i = 0 := by
    rw [hzero]
    simp [Matrix.mulVec, dotProduct]
  have hright : (Pi.single i 1 : Ω → ℝ) i = 1 := by
    simp
  have h := congr_fun hcol i
  rw [hleft, hright] at h
  norm_num at h

/-- A positive spectral-data column of an entrywise positive matrix has a
positive eigenvalue. -/
theorem eigenvalue_pos_of_positive_column [Nonempty Ω]
    {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M)
    (hM : MatrixEntrywisePositive M) (top : Ω)
    (hpos : VectorPositive (fun x => E.changeOfBasis x top)) :
    0 < E.eigenvalue top :=
  eigenvalue_pos_of_strictPositiveRightEigenpair hM
    ⟨hpos, E.mulVec_changeOfBasis_column top⟩

/-- A positive spectral-data column of an entrywise positive matrix bounds all
spectral-data eigenvalues in absolute value. -/
theorem eigenvalue_abs_le_of_positive_column [Nonempty Ω]
    {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M)
    (hM : MatrixEntrywisePositive M) (top i : Ω)
    (hpos : VectorPositive (fun x => E.changeOfBasis x top)) :
    |E.eigenvalue i| ≤ E.eigenvalue top :=
  abs_eigenvalue_le_of_entrywisePositive_positive_eigenpair hM
    ⟨hpos, E.mulVec_changeOfBasis_column top⟩
    (E.changeOfBasis_column_ne_zero i)
    (E.mulVec_changeOfBasis_column i)

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

/-- For a balanced positive layer transfer matrix, a positive Hermitian spectral
column has an eigenvalue that bounds all spectral-data eigenvalues in absolute
value. -/
theorem layerSymmetricTransfer_eigenvalue_abs_le_of_positive_column
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (hk_symm : ∀ ω η, k ω η = k η ω)
    (top i : LayerState S)
    (hpos : VectorPositive
      (fun ω =>
        (layerSymmetricTransferOrthogonalSpectralData u k hk_symm).changeOfBasis ω top)) :
    |(layerSymmetricTransferOrthogonalSpectralData u k hk_symm).eigenvalue i|
      ≤ (layerSymmetricTransferOrthogonalSpectralData u k hk_symm).eigenvalue top :=
  RealOrthogonalSpectralData.eigenvalue_abs_le_of_positive_column
    (layerSymmetricTransferOrthogonalSpectralData u k hk_symm)
    (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos)
    top i hpos

/-- Orthogonal spectral-data constructor with the transfer scale fixed to the
positive top spectral column's eigenvalue.  This removes the separate
`scale`, `scale_pos`, and `dominant_eigenvalue` inputs, but still assumes the
quantitative subdominant bound. -/
noncomputable def layerBalancedMinSpectralGapCertificate_of_orthogonalSubdominantBounds
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (hu : ∀ a, 0 < u a) (hk_pos : ∀ a b, 0 < k a b)
    (top : Ω) (theta : ℝ)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (partitionPrefactor_small :
      (((Fintype.card Ω - 1 : ℕ) : ℝ) * theta) < 1)
    (subdominant_abs_le : ∀ i, i ≠ top →
      |E.eigenvalue i| ≤ theta * E.eigenvalue top)
    (dominant_column_pos : VectorPositive (fun a => E.changeOfBasis a top))
    (dominant_markedDiagonal_zero : E.markedMatrix f top top = 0) :
    LayerBalancedMinSpectralGapCertificate u k f := by
  letI : Nonempty Ω := ⟨top⟩
  exact layerBalancedMinSpectralGapCertificate_of_orthogonalDominantBounds
    u k f E top (E.eigenvalue top) theta
    (E.eigenvalue_pos_of_positive_column
      (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos) top
      dominant_column_pos)
    theta_nonneg theta_lt_one partitionPrefactor_small rfl subdominant_abs_le
    dominant_markedDiagonal_zero

/-- Hermitian spectral-data constructor with the transfer scale fixed to the
positive top spectral column's eigenvalue. -/
noncomputable def layerBalancedMinSpectralGapCertificate_of_layerHermitianSubdominantBounds
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (hu : ∀ a, 0 < u a) (hk_pos : ∀ a b, 0 < k a b)
    (hk : ∀ a b, k a b = k b a)
    (top : Ω) (theta : ℝ)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (partitionPrefactor_small :
      (((Fintype.card Ω - 1 : ℕ) : ℝ) * theta) < 1)
    (subdominant_abs_le : ∀ i, i ≠ top →
      |(layerSymmetricTransferOrthogonalSpectralData u k hk).eigenvalue i|
        ≤ theta * (layerSymmetricTransferOrthogonalSpectralData u k hk).eigenvalue top)
    (dominant_column_pos : VectorPositive
      (fun a => (layerSymmetricTransferOrthogonalSpectralData u k hk).changeOfBasis a top))
    (dominant_markedDiagonal_zero :
      (layerSymmetricTransferOrthogonalSpectralData u k hk).markedMatrix f top top = 0) :
    LayerBalancedMinSpectralGapCertificate u k f :=
  layerBalancedMinSpectralGapCertificate_of_orthogonalSubdominantBounds
    u k f (layerSymmetricTransferOrthogonalSpectralData u k hk) hu hk_pos
    top theta theta_nonneg theta_lt_one partitionPrefactor_small
    subdominant_abs_le dominant_column_pos dominant_markedDiagonal_zero

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

/-- Spin-observable constructor with the transfer scale fixed to the positive
top spectral column's eigenvalue, using positive simple dominant-column inputs
instead of a direct flip-evenness hypothesis. -/
noncomputable def
    layerBalancedMinSpectralGapCertificate_of_orthogonalSubdominantBounds_positiveSimpleFlipSpin
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (top : LayerState S) (theta : ℝ)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (partitionPrefactor_small :
      (((Fintype.card (LayerState S) - 1 : ℕ) : ℝ) * theta) < 1)
    (subdominant_abs_le : ∀ i, i ≠ top → |E.eigenvalue i| ≤ theta * E.eigenvalue top)
    (dominant_column_pos : VectorPositive (fun ω => E.changeOfBasis ω top))
    (dominant_eigenspace_simple : ∀ w : LayerState S → ℝ,
      (layerSymmetricTransferMatrix u k).mulVec w = E.eigenvalue top • w →
        ∃ c : ℝ, w = c • (fun ω => E.changeOfBasis ω top)) :
    LayerBalancedMinSpectralGapCertificate u k (layerSpinAt x) := by
  letI : Nonempty (LayerState S) := ⟨top⟩
  exact layerBalancedMinSpectralGapCertificate_of_orthogonalDominantBounds_positiveSimpleFlipSpin
    u k x hu_flip hk_flip E top (E.eigenvalue top) theta
    (E.eigenvalue_pos_of_positive_column
      (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos) top
      dominant_column_pos)
    theta_nonneg theta_lt_one partitionPrefactor_small rfl subdominant_abs_le
    dominant_column_pos dominant_eigenspace_simple

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

/-- Hermitian spin-observable constructor with the transfer scale fixed to the
positive top spectral column's eigenvalue, using positive simple
dominant-column inputs instead of a direct flip-evenness hypothesis. -/
noncomputable def
    layerBalancedMinSpectralGapCertificate_of_layerHermitianSubdominantBounds_positiveSimpleFlipSpin
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (hk : ∀ a b, k a b = k b a)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (top : LayerState S) (theta : ℝ)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (partitionPrefactor_small :
      (((Fintype.card (LayerState S) - 1 : ℕ) : ℝ) * theta) < 1)
    (subdominant_abs_le : ∀ i, i ≠ top →
      |(layerSymmetricTransferOrthogonalSpectralData u k hk).eigenvalue i|
        ≤ theta * (layerSymmetricTransferOrthogonalSpectralData u k hk).eigenvalue top)
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
  layerBalancedMinSpectralGapCertificate_of_orthogonalSubdominantBounds_positiveSimpleFlipSpin
    u k x hu hk_pos hu_flip hk_flip
    (layerSymmetricTransferOrthogonalSpectralData u k hk) top theta
    theta_nonneg theta_lt_one partitionPrefactor_small subdominant_abs_le
    dominant_column_pos dominant_eigenspace_simple

end TransferMatrix

end IsingModel

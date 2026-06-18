import IsingModel.TransferMatrix.LayerPerron

/-!
# Signed positive dominant columns for finite layer transfer matrices

This file records the sign-invariant interface needed for the finite
Perron--Frobenius step.  A real orthogonal spectral column is only determined up
to sign, so the useful statement is that a chosen column is positive after
multiplication by a scalar sign with square one.

The file connects such signed-positive columns to the positive-column radius,
simplicity, strict-ratio, and spin-cancellation API developed in
`LayerPerron.lean`.  It does not yet prove the Perron--Frobenius existence
theorem that a maximal spectral column is signed-positive, nor does it
discharge the finite-cardinality prefactor condition in the certificates.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.1, pp. 304--306.
-/

namespace IsingModel

namespace TransferMatrix

open Matrix

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

namespace RealOrthogonalSpectralData

/-- A spectral-data index where the finite eigenvalue family attains its
maximum. -/
noncomputable def maxEigenIndex [Nonempty Ω] {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) : Ω :=
  Classical.choose
    (Finset.exists_max_image (Finset.univ : Finset Ω) E.eigenvalue
      Finset.univ_nonempty)

/-- The eigenvalue at `maxEigenIndex` is maximal among the finite spectral-data
eigenvalues. -/
theorem eigenvalue_le_maxEigenIndex [Nonempty Ω] {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (i : Ω) :
    E.eigenvalue i ≤ E.eigenvalue E.maxEigenIndex :=
  (Classical.choose_spec
    (Finset.exists_max_image (Finset.univ : Finset Ω) E.eigenvalue
      Finset.univ_nonempty)).2 i (Finset.mem_univ i)

/-- A spectral-data column that becomes strictly positive after multiplying by
a scalar sign.  Orthogonal eigenvectors are only fixed up to sign, so this is
the sign-invariant positivity package used by the Perron-facing layer API. -/
structure SignedPositiveColumn {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (top : Ω) where
  /-- The scalar sign used to orient the spectral column. -/
  sign : ℝ
  /-- The sign has square one. -/
  sign_mul_self : sign * sign = 1
  /-- The oriented top column is strictly positive. -/
  positive : VectorPositive (fun x => sign * E.changeOfBasis x top)

namespace SignedPositiveColumn

/-- The sign in a signed-positive column is nonzero. -/
theorem sign_ne_zero {M : Matrix Ω Ω ℝ}
    {E : RealOrthogonalSpectralData M} {top : Ω}
    (h : E.SignedPositiveColumn top) : h.sign ≠ 0 := by
  intro hzero
  have : (0 : ℝ) = 1 := by
    simpa [hzero] using h.sign_mul_self
  norm_num at this

/-- The oriented column of a signed-positive column is an eigenvector with the
same eigenvalue as the raw spectral column. -/
theorem mulVec_signedColumn {M : Matrix Ω Ω ℝ}
    {E : RealOrthogonalSpectralData M} {top : Ω}
    (h : E.SignedPositiveColumn top) :
    M.mulVec (fun x => h.sign * E.changeOfBasis x top)
      = E.eigenvalue top • (fun x => h.sign * E.changeOfBasis x top) := by
  change M.mulVec (h.sign • (fun x => E.changeOfBasis x top))
      = E.eigenvalue top • (h.sign • (fun x => E.changeOfBasis x top))
  rw [Matrix.mulVec_smul, E.mulVec_changeOfBasis_column top]
  ext x
  simp [Pi.smul_apply, smul_eq_mul, mul_left_comm]

/-- A signed-positive column gives a strictly positive right eigenpair. -/
theorem strictPositiveRightEigenpair {M : Matrix Ω Ω ℝ}
    {E : RealOrthogonalSpectralData M} {top : Ω}
    (h : E.SignedPositiveColumn top) :
    StrictPositiveRightEigenpair M (E.eigenvalue top)
      (fun x => h.sign * E.changeOfBasis x top) :=
  ⟨h.positive, h.mulVec_signedColumn⟩

/-- If a vector is a scalar multiple of the oriented column, then it is also a
scalar multiple of the raw spectral column. -/
theorem smul_signedColumn_eq_smul_raw {M : Matrix Ω Ω ℝ}
    {E : RealOrthogonalSpectralData M} {top : Ω}
    (h : E.SignedPositiveColumn top) {w : Ω → ℝ} {c : ℝ}
    (hw : w = c • (fun x => h.sign * E.changeOfBasis x top)) :
    ∃ c' : ℝ, w = c' • (fun x => E.changeOfBasis x top) := by
  refine ⟨c * h.sign, ?_⟩
  ext x
  have hx := congr_fun hw x
  simpa [Pi.smul_apply, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using hx

end SignedPositiveColumn

/-- A signed-positive top column has a positive eigenvalue. -/
theorem eigenvalue_pos_of_signedPositiveColumn [Nonempty Ω]
    {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M)
    (hM : MatrixEntrywisePositive M) (top : Ω)
    (hpos : E.SignedPositiveColumn top) :
    0 < E.eigenvalue top :=
  eigenvalue_pos_of_strictPositiveRightEigenpair hM
    hpos.strictPositiveRightEigenpair

/-- A signed-positive top column bounds every spectral-data eigenvalue in
absolute value. -/
theorem eigenvalue_abs_le_of_signedPositiveColumn [Nonempty Ω]
    {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M)
    (hM : MatrixEntrywisePositive M) (top i : Ω)
    (hpos : E.SignedPositiveColumn top) :
    |E.eigenvalue i| ≤ E.eigenvalue top :=
  abs_eigenvalue_le_of_entrywisePositive_positive_eigenpair hM
    hpos.strictPositiveRightEigenpair
    (E.changeOfBasis_column_ne_zero i)
    (E.mulVec_changeOfBasis_column i)

/-- A signed-positive top column spans the eigenspace for its eigenvalue. -/
theorem eigenspace_simple_of_signedPositiveColumn [Nonempty Ω]
    {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M)
    (hM : MatrixEntrywisePositive M) (top : Ω)
    (hpos : E.SignedPositiveColumn top)
    {w : Ω → ℝ} (hw_eig : M.mulVec w = E.eigenvalue top • w) :
    ∃ c : ℝ, w = c • (fun x => E.changeOfBasis x top) := by
  rcases eigenvector_smul_of_entrywisePositive_positive_eigenpair hM
      hpos.strictPositiveRightEigenpair hw_eig with
    ⟨c, hc⟩
  exact hpos.smul_signedColumn_eq_smul_raw hc

/-- A signed-positive top spectral column gives strict absolute inequality for
every different spectral-data column. -/
theorem eigenvalue_abs_lt_of_signedPositiveColumn [Nonempty Ω]
    {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M)
    (hM : MatrixEntrywisePositive M) (top i : Ω) (hi : i ≠ top)
    (hpos : E.SignedPositiveColumn top) :
    |E.eigenvalue i| < E.eigenvalue top := by
  have hne : E.eigenvalue i ≠ E.eigenvalue top := by
    intro heq
    have hi_eig :
        M.mulVec (fun x => E.changeOfBasis x i)
          = E.eigenvalue top • (fun x => E.changeOfBasis x i) := by
      simpa [heq] using E.mulVec_changeOfBasis_column i
    rcases E.eigenspace_simple_of_signedPositiveColumn hM top hpos hi_eig with
      ⟨c, hc⟩
    exact E.changeOfBasis_columns_not_smul hi c hc
  exact abs_eigenvalue_lt_of_entrywisePositive_positive_eigenpair hM
    hpos.strictPositiveRightEigenpair
    (E.changeOfBasis_column_ne_zero i)
    (E.mulVec_changeOfBasis_column i) hne

/-- A signed-positive spectral-data top column gives some strict finite
subdominant ratio for all non-top spectral-data eigenvalues.  The finite
certificate prefactor condition remains a separate quantitative input. -/
theorem exists_subdominant_abs_ratio_of_signedPositiveColumn [Nonempty Ω]
    {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M)
    (hM : MatrixEntrywisePositive M) (top : Ω)
    (hpos : E.SignedPositiveColumn top) :
    ∃ theta : ℝ, 0 ≤ theta ∧ theta < 1 ∧
      ∀ i, i ≠ top → |E.eigenvalue i| ≤ theta * E.eigenvalue top := by
  let rest : Finset Ω := Finset.univ.erase top
  have htop_pos : 0 < E.eigenvalue top :=
    E.eigenvalue_pos_of_signedPositiveColumn hM top hpos
  by_cases hrest : rest = ∅
  · refine ⟨0, le_rfl, zero_lt_one, ?_⟩
    intro i hi
    have himem : i ∈ rest := by
      exact Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩
    rw [hrest] at himem
    simp at himem
  · obtain ⟨i0, hi0, hmax⟩ :=
      Finset.exists_max_image rest (fun i => |E.eigenvalue i| / E.eigenvalue top)
        (Finset.nonempty_iff_ne_empty.mpr hrest)
    refine ⟨|E.eigenvalue i0| / E.eigenvalue top, ?_, ?_, ?_⟩
    · exact div_nonneg (abs_nonneg _) htop_pos.le
    · have hi0_ne : i0 ≠ top := (Finset.mem_erase.mp hi0).1
      have hlt := E.eigenvalue_abs_lt_of_signedPositiveColumn hM top i0 hi0_ne hpos
      exact (div_lt_one htop_pos).mpr hlt
    · intro i hi
      have himem : i ∈ rest := Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩
      exact (div_le_iff₀ htop_pos).mp (hmax i himem)

end RealOrthogonalSpectralData

/-! ## Layer wrappers for signed-positive columns -/

/-- A signed-positive balanced-layer spectral column bounds every spectral-data
eigenvalue in absolute value. -/
theorem layerSymmetricTransfer_eigenvalue_abs_le_of_signedPositiveColumn
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (top i : LayerState S) (hpos : E.SignedPositiveColumn top) :
    |E.eigenvalue i| ≤ E.eigenvalue top := by
  letI : Nonempty (LayerState S) := ⟨top⟩
  exact E.eigenvalue_abs_le_of_signedPositiveColumn
    (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos) top i hpos

/-- A signed-positive balanced-layer spectral column spans its eigenspace. -/
theorem layerSymmetricTransfer_signedPositiveColumn_eigenspace_simple
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (top : LayerState S) (hpos : E.SignedPositiveColumn top)
    {w : LayerState S → ℝ}
    (hw_eig : (layerSymmetricTransferMatrix u k).mulVec w =
      E.eigenvalue top • w) :
    ∃ c : ℝ, w = c • (fun ω => E.changeOfBasis ω top) := by
  letI : Nonempty (LayerState S) := ⟨top⟩
  exact E.eigenspace_simple_of_signedPositiveColumn
    (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos) top hpos hw_eig

/-- A signed-positive balanced-layer spectral column gives strict absolute
inequality for each different spectral-data column. -/
theorem layerSymmetricTransfer_eigenvalue_abs_lt_of_signedPositiveColumn
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (top i : LayerState S) (hi : i ≠ top)
    (hpos : E.SignedPositiveColumn top) :
    |E.eigenvalue i| < E.eigenvalue top := by
  letI : Nonempty (LayerState S) := ⟨top⟩
  exact E.eigenvalue_abs_lt_of_signedPositiveColumn
    (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos) top i hi hpos

/-- A signed-positive balanced-layer spectral column gives some strict finite
subdominant ratio for all non-top spectral-data eigenvalues. -/
theorem layerSymmetricTransfer_exists_subdominant_abs_ratio_of_signedPositiveColumn
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (top : LayerState S) (hpos : E.SignedPositiveColumn top) :
    ∃ theta : ℝ, 0 ≤ theta ∧ theta < 1 ∧
      ∀ i, i ≠ top → |E.eigenvalue i| ≤ theta * E.eigenvalue top := by
  letI : Nonempty (LayerState S) := ⟨top⟩
  exact E.exists_subdominant_abs_ratio_of_signedPositiveColumn
    (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos) top hpos

/-! ## Signed-positive spin-observable certificate constructors -/

/-- A signed-positive spectral column of a balanced layer transfer matrix is
flip-even when the layer weights and transition weights are invariant under
global spin flip. -/
theorem layerSymmetricTransfer_signedPositiveColumn_flip_even
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (top : LayerState S) (hpos : E.SignedPositiveColumn top) :
    ∀ ω : LayerState S,
      E.changeOfBasis (layerStateFlipEquiv S ω) top = E.changeOfBasis ω top := by
  letI : Nonempty (LayerState S) := ⟨top⟩
  let v : LayerState S → ℝ := fun ω => hpos.sign * E.changeOfBasis ω top
  have hveig :
      (layerSymmetricTransferMatrix u k).mulVec v = E.eigenvalue top • v :=
    hpos.mulVec_signedColumn
  have hsimple :
      ∀ w : LayerState S → ℝ,
        (layerSymmetricTransferMatrix u k).mulVec w = E.eigenvalue top • w →
          ∃ c : ℝ, w = c • v := by
    intro w hw
    exact eigenvector_smul_of_entrywisePositive_positive_eigenpair
      (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos)
      hpos.strictPositiveRightEigenpair hw
  have hsigned_even :
      ∀ ω : LayerState S,
        v (layerStateFlipEquiv S ω) = v ω :=
    vectorPositive_eigenvector_flip_even_of_simple_eigenspace
      (layerStateFlipEquiv S)
      (fun ω => layerStateFlipEquiv_involutive S ω)
      hpos.positive hveig
      (layerSymmetricTransferMatrix_mulVec_comp_equiv u k (layerStateFlipEquiv S)
        hu_flip hk_flip)
      hsimple
  intro ω
  exact mul_left_cancel₀ hpos.sign_ne_zero (hsigned_even ω)

/-- Spin-observable constructor using a signed-positive dominant column.  The
flip-even marked-channel cancellation is derived after orienting the spectral
column by its sign. -/
noncomputable def
    layerBalancedMinSpectralGapCertificate_of_orthogonalDominantBounds_signedPositiveColumnFlipSpin
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
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
    (dominant_column_signed_pos : E.SignedPositiveColumn top) :
    LayerBalancedMinSpectralGapCertificate u k (layerSpinAt x) :=
  layerBalancedMinSpectralGapCertificate_of_orthogonalDominantBounds_flipEvenSpin
    u k x E top scale theta scale_pos theta_nonneg theta_lt_one
    partitionPrefactor_small dominant_eigenvalue subdominant_abs_le
    (layerSymmetricTransfer_signedPositiveColumn_flip_even
      u k hu hk_pos hu_flip hk_flip E top dominant_column_signed_pos)

/-- Spin-observable constructor using a signed-positive dominant column with
the transfer scale fixed to that column's eigenvalue. -/
noncomputable def
layerBalancedMinSpectralGapCertificate_of_orthogonalSubdominantBounds_signedPositiveColumnFlipSpin
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
    (subdominant_abs_le :
      ∀ i, i ≠ top → |E.eigenvalue i| ≤ theta * E.eigenvalue top)
    (dominant_column_signed_pos : E.SignedPositiveColumn top) :
    LayerBalancedMinSpectralGapCertificate u k (layerSpinAt x) := by
  letI : Nonempty (LayerState S) := ⟨top⟩
  exact
    layerBalancedMinSpectralGapCertificate_of_orthogonalDominantBounds_signedPositiveColumnFlipSpin
      u k x hu hk_pos hu_flip hk_flip E top (E.eigenvalue top) theta
      (E.eigenvalue_pos_of_signedPositiveColumn
        (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos) top
        dominant_column_signed_pos)
      theta_nonneg theta_lt_one partitionPrefactor_small rfl subdominant_abs_le
      dominant_column_signed_pos

end TransferMatrix

end IsingModel

import IsingModel.TransferMatrix.LayerSpectralWindowSmallRatio

/-!
# Infinite-temperature layer spectral windows

This file records the concrete spectral-window estimate at the
infinite-temperature slice `p.β = 0`.  At this slice the physical layer weights
are identically one, so the balanced transfer matrix is the all-ones matrix.
Its spectrum consists of the single positive eigenvalue `Fintype.card Ω` and
zero on every non-maximal spectral-data column.  Consequently the explicit
spectral-window bridge from `LayerSpectralWindowSmallRatio` applies with
`theta = 0`.

This is only the `β = 0` slice.  It does not prove a high-temperature
neighborhood, a Walsh diagonalization, open slabs, thermodynamic limits, or
final hyperplane exponential decay.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

open Matrix

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-! ## The all-ones matrix -/

/-- The finite square matrix whose entries are all equal to one. -/
def allOnesMatrix (Ω : Type*) [Fintype Ω] : Matrix Ω Ω ℝ :=
  fun _ _ => 1

omit [DecidableEq Ω] in
/-- The all-ones matrix is entrywise positive. -/
theorem allOnesMatrix_entrywisePositive :
    MatrixEntrywisePositive (allOnesMatrix Ω) :=
  fun _ _ => zero_lt_one

omit [DecidableEq Ω] in
/-- Multiplication by the all-ones matrix returns the constant vector with
value equal to the coordinate sum of the input vector. -/
theorem allOnesMatrix_mulVec (v : Ω → ℝ) :
    (allOnesMatrix Ω).mulVec v = fun _ => ∑ j, v j := by
  ext i
  simp [allOnesMatrix, Matrix.mulVec, dotProduct]

/-- Any nonzero eigenvalue of the all-ones matrix equals the cardinality of the
index type. -/
theorem allOnesMatrix_eigenvalue_eq_card_of_ne_zero
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {lam : ℝ} {v : Ω → ℝ} (hv_ne : v ≠ 0)
    (hv_eig : (allOnesMatrix Ω).mulVec v = lam • v) (hlam : lam ≠ 0) :
    lam = (Fintype.card Ω : ℝ) := by
  obtain ⟨i0, hi0⟩ : ∃ i0, v i0 ≠ 0 := by
    by_contra h
    apply hv_ne
    ext i
    by_contra hi
    exact h ⟨i, hi⟩
  have hsum : ∀ i, (∑ j, v j) = lam * v i := by
    intro i
    have h := congr_fun hv_eig i
    simpa [allOnesMatrix_mulVec, Pi.smul_apply, smul_eq_mul] using h
  have hconst : ∀ i, v i = v i0 := by
    intro i
    have hsame : lam * v i = lam * v i0 := by
      rw [← hsum i, ← hsum i0]
    exact mul_left_cancel₀ hlam hsame
  have hsum_card : (∑ j, v j) = (Fintype.card Ω : ℝ) * v i0 := by
    simp [hconst]
  have hmul : lam * v i0 = (Fintype.card Ω : ℝ) * v i0 := by
    rw [← hsum i0, hsum_card]
  exact mul_right_cancel₀ hi0 hmul

namespace RealOrthogonalSpectralData

/-- Every spectral-data eigenvalue of the all-ones matrix is either the
cardinality eigenvalue or zero. -/
theorem eigenvalue_eq_card_or_zero_allOnes [Nonempty Ω]
    (E : RealOrthogonalSpectralData (allOnesMatrix Ω)) (i : Ω) :
    E.eigenvalue i = (Fintype.card Ω : ℝ) ∨ E.eigenvalue i = 0 := by
  by_cases hzero : E.eigenvalue i = 0
  · exact Or.inr hzero
  · exact Or.inl
      (allOnesMatrix_eigenvalue_eq_card_of_ne_zero
        (E.changeOfBasis_column_ne_zero i) (E.mulVec_changeOfBasis_column i) hzero)

/-- The maximal spectral-data eigenvalue of the all-ones matrix is the
cardinality eigenvalue. -/
theorem maxEigenIndex_eigenvalue_allOnes [Nonempty Ω]
    (E : RealOrthogonalSpectralData (allOnesMatrix Ω)) :
    E.eigenvalue E.maxEigenIndex = (Fintype.card Ω : ℝ) := by
  rcases E.eigenvalue_eq_card_or_zero_allOnes E.maxEigenIndex with hcard | hzero
  · exact hcard
  · have hpos := E.eigenvalue_pos_maxEigenIndex (allOnesMatrix_entrywisePositive (Ω := Ω))
    linarith

/-- Every non-maximal spectral-data eigenvalue of the all-ones matrix is zero. -/
theorem eigenvalue_eq_zero_of_ne_max_allOnes [Nonempty Ω]
    (E : RealOrthogonalSpectralData (allOnesMatrix Ω))
    {i : Ω} (hi : i ≠ E.maxEigenIndex) :
    E.eigenvalue i = 0 := by
  rcases E.eigenvalue_eq_card_or_zero_allOnes i with hcard | hzero
  · have hlt :=
      E.eigenvalue_abs_lt_maxEigenIndex (allOnesMatrix_entrywisePositive (Ω := Ω)) i hi
    have htop := E.maxEigenIndex_eigenvalue_allOnes
    have hcard_pos : 0 < (Fintype.card Ω : ℝ) := by
      exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
    rw [hcard, htop, abs_of_pos hcard_pos] at hlt
    exact False.elim ((lt_irrefl _) hlt)
  · exact hzero

/-- The all-ones matrix satisfies the explicit non-maximal spectral window with
`theta = 0`. -/
theorem subdominant_abs_le_zero_allOnes [Nonempty Ω]
    (E : RealOrthogonalSpectralData (allOnesMatrix Ω)) :
    ∀ i, i ≠ E.maxEigenIndex →
      |E.eigenvalue i| ≤ 0 * E.eigenvalue E.maxEigenIndex := by
  intro i hi
  rw [E.eigenvalue_eq_zero_of_ne_max_allOnes hi]
  simp

/-- Transport the all-ones spectral window across a matrix equality. -/
theorem subdominant_abs_le_zero_of_matrix_eq_allOnes [Nonempty Ω]
    {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M)
    (hM : M = allOnesMatrix Ω) :
    ∀ i, i ≠ E.maxEigenIndex →
      |E.eigenvalue i| ≤ 0 * E.eigenvalue E.maxEigenIndex := by
  subst M
  exact E.subdominant_abs_le_zero_allOnes

end RealOrthogonalSpectralData

/-! ## Infinite-temperature arithmetic -/

/-- The inverse-cardinality threshold for a nonempty transverse layer is
strictly positive. -/
theorem inv_two_pow_cardSubOne_pos_of_nonempty
    (S : Type*) [Fintype S] [Nonempty S] :
    0 < (((2 ^ Fintype.card S - 1 : ℕ) : ℝ))⁻¹ := by
  have hcard_pos : 0 < Fintype.card S := Fintype.card_pos_iff.mpr inferInstance
  have hpow : 1 < 2 ^ Fintype.card S :=
    Nat.one_lt_pow (Nat.ne_of_gt hcard_pos) one_lt_two
  have hden_nat : 0 < 2 ^ Fintype.card S - 1 := by omega
  have hden : 0 < ((2 ^ Fintype.card S - 1 : ℕ) : ℝ) := by
    exact_mod_cast hden_nat
  exact inv_pos.mpr hden

/-- The cubic transverse-box inverse-cardinality threshold is strictly
positive. -/
theorem inv_cubicLayerSite_cardSubOne_pos (d R : ℕ) :
    0 < (((2 ^ ((2 * R + 1) ^ d) - 1 : ℕ) : ℝ))⁻¹ := by
  letI : Nonempty (CubicLayerSite d R) := cubicLayerSite_nonempty d R
  simpa [cubicLayerSite_card d R] using
    inv_two_pow_cardSubOne_pos_of_nonempty (CubicLayerSite d R)

/-! ## Physical layer weights at `β = 0` -/

/-- At `β = 0`, the one-layer physical Ising weight is identically one. -/
theorem layerInternalWeight_beta_zero
    {S : Type*} [Fintype S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (p : IsingParams ℝ)
    (hpβ : p.β = 0) (ω : LayerState S) :
    layerInternalWeight H p ω = 1 := by
  simp [layerInternalWeight, hpβ]

/-- At `β = 0`, the adjacent-layer physical Ising weight is identically one. -/
theorem layerTransitionWeight_beta_zero
    {S : Type*}
    (P : Finset (S × S)) (p : IsingParams ℝ)
    (hpβ : p.β = 0) (ω η : LayerState S) :
    layerTransitionWeight P p ω η = 1 := by
  simp [layerTransitionWeight, hpβ]

/-- At `β = 0`, the adjacent-layer physical Ising weight is symmetric. -/
theorem layerTransitionWeight_symm_beta_zero
    {S : Type*}
    (P : Finset (S × S)) (p : IsingParams ℝ) (hpβ : p.β = 0)
    (ω η : LayerState S) :
    layerTransitionWeight P p ω η = layerTransitionWeight P p η ω := by
  rw [layerTransitionWeight_beta_zero P p hpβ,
    layerTransitionWeight_beta_zero P p hpβ]

/-- At `β = 0`, the balanced physical layer transfer matrix is the all-ones
matrix. -/
theorem layerSymmetricTransferMatrix_beta_zero
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (P : Finset (S × S))
    (p : IsingParams ℝ) (hpβ : p.β = 0) :
    layerSymmetricTransferMatrix (layerInternalWeight H p)
        (layerTransitionWeight P p) =
      allOnesMatrix (LayerState S) := by
  ext ω η
  simp [layerSymmetricTransferMatrix, allOnesMatrix,
    layerInternalWeight_beta_zero H p hpβ,
    layerTransitionWeight_beta_zero P p hpβ]

/-! ## Infinite-temperature spectral-window certificates -/

/-- Orthogonal spin certificate for a physical finite layer at `β = 0`, using
the concrete spectral window `theta = 0`. -/
noncomputable def layerBalancedMinGapCert_orthogonal_beta_zero_spectralWindow
    {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (P : Finset (S × S))
    (p : IsingParams ℝ) (x : S) (hpβ : p.β = 0)
    (E : RealOrthogonalSpectralData
      (layerSymmetricTransferMatrix (layerInternalWeight H p)
        (layerTransitionWeight P p))) :
    LayerBalancedMinSpectralGapCertificate
      (layerInternalWeight H p) (layerTransitionWeight P p) (layerSpinAt x) := by
  refine
    layerBalancedMinGapCert_orthogonal_spectralWindow_layerCardSmall
      (layerInternalWeight H p) (layerTransitionWeight P p) x
      (fun ω => Real.exp_pos _)
      (fun ω η => Real.exp_pos _)
      ?_ ?_ E 0 le_rfl
      (inv_two_pow_cardSubOne_pos_of_nonempty S)
      ?_
  · intro ω
    rw [layerInternalWeight_beta_zero H p hpβ,
      layerInternalWeight_beta_zero H p hpβ]
  · intro ω η
    rw [layerTransitionWeight_beta_zero P p hpβ,
      layerTransitionWeight_beta_zero P p hpβ]
  · exact E.subdominant_abs_le_zero_of_matrix_eq_allOnes
      (layerSymmetricTransferMatrix_beta_zero H P p hpβ)

/-- Hermitian spin certificate for a physical finite layer at `β = 0`, using
the concrete spectral window `theta = 0`. -/
noncomputable def layerBalancedMinGapCert_hermitian_beta_zero_spectralWindow
    {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (P : Finset (S × S))
    (p : IsingParams ℝ) (x : S) (hpβ : p.β = 0) :
    LayerBalancedMinSpectralGapCertificate
      (layerInternalWeight H p) (layerTransitionWeight P p) (layerSpinAt x) := by
  refine
    layerBalancedMinGapCert_hermitian_spectralWindow_layerCardSmall
      (layerInternalWeight H p) (layerTransitionWeight P p) x
      (fun ω => Real.exp_pos _)
      (fun ω η => Real.exp_pos _)
      (layerTransitionWeight_symm_beta_zero P p hpβ)
      ?_ ?_ 0 le_rfl
      (inv_two_pow_cardSubOne_pos_of_nonempty S)
      ?_
  · intro ω
    rw [layerInternalWeight_beta_zero H p hpβ,
      layerInternalWeight_beta_zero H p hpβ]
  · intro ω η
    rw [layerTransitionWeight_beta_zero P p hpβ,
      layerTransitionWeight_beta_zero P p hpβ]
  · let E0 :=
      layerSymmetricTransferOrthogonalSpectralData
        (layerInternalWeight H p) (layerTransitionWeight P p)
        (layerTransitionWeight_symm_beta_zero P p hpβ)
    exact E0.subdominant_abs_le_zero_of_matrix_eq_allOnes
      (layerSymmetricTransferMatrix_beta_zero H P p hpβ)

/-! ## Cubic infinite-temperature spectral-window certificates -/

/-- Orthogonal spin certificate for a cubic transverse box at `β = 0`, using
the concrete spectral window `theta = 0`. -/
noncomputable def cubicLayerBalancedMinGapCertificate_orthogonal_beta_zero_spectralWindow
    (d R : ℕ) (p : IsingParams ℝ) (x : CubicLayerSite d R)
    (hpβ : p.β = 0)
    (E : RealOrthogonalSpectralData
      (layerSymmetricTransferMatrix
        (layerInternalWeight (cubicLayerGraph d R) p)
        (layerTransitionWeight (cubicLayerTransitionPairs d R) p))) :
    LayerBalancedMinSpectralGapCertificate
      (layerInternalWeight (cubicLayerGraph d R) p)
      (layerTransitionWeight (cubicLayerTransitionPairs d R) p)
      (layerSpinAt x) := by
  letI : Nonempty (CubicLayerSite d R) := cubicLayerSite_nonempty d R
  exact
    layerBalancedMinGapCert_orthogonal_beta_zero_spectralWindow
      (cubicLayerGraph d R) (cubicLayerTransitionPairs d R) p x hpβ E

/-- Hermitian spin certificate for a cubic transverse box at `β = 0`, using the
concrete spectral window `theta = 0`. -/
noncomputable def cubicLayerBalancedMinGapCertificate_hermitian_beta_zero_spectralWindow
    (d R : ℕ) (p : IsingParams ℝ) (x : CubicLayerSite d R)
    (hpβ : p.β = 0) :
    LayerBalancedMinSpectralGapCertificate
      (layerInternalWeight (cubicLayerGraph d R) p)
      (layerTransitionWeight (cubicLayerTransitionPairs d R) p)
      (layerSpinAt x) := by
  letI : Nonempty (CubicLayerSite d R) := cubicLayerSite_nonempty d R
  exact
    layerBalancedMinGapCert_hermitian_beta_zero_spectralWindow
      (cubicLayerGraph d R) (cubicLayerTransitionPairs d R) p x hpβ

end TransferMatrix

end IsingModel

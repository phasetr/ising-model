import IsingModel.TransferMatrix.LayerSpectral.BalancedMatrix

/-!
# Finite Hermitian spectral bridge (GJ §17.1)

The finite Hermitian spectral-theorem bridge: real orthogonal spectral data
(`RealOrthogonalSpectralData`) obtained from mathlib's Hermitian spectral
theorem, the marked matrix, boundary coordinates and marked spectral
prefactors.  Part of the `LayerSpectral` finite spectral scaffold.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.1, pp. 304--306.
-/

namespace IsingModel

namespace TransferMatrix

open Matrix

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-! ## Finite Hermitian spectral bridge -/

/-- The finite-cardinality partition prefactor obtained from a crude dominant
spectral-term lower bound. -/
def finiteSpectralPartitionPrefactor (Ω : Type*) [Fintype Ω] (theta : ℝ) : ℝ :=
  1 - (((Fintype.card Ω - 1 : ℕ) : ℝ) * theta)

/-- Positivity criterion for the finite-cardinality partition prefactor. -/
theorem finiteSpectralPartitionPrefactor_pos (Ω : Type*) [Fintype Ω] {theta : ℝ}
    (hsmall : (((Fintype.card Ω - 1 : ℕ) : ℝ) * theta) < 1) :
    0 < finiteSpectralPartitionPrefactor Ω theta := by
  rw [finiteSpectralPartitionPrefactor, sub_pos]
  exact hsmall

/-- If the finite state space has exactly one element, the finite-cardinality
partition-prefactor smallness condition is automatic. -/
theorem finiteSpectralPartitionPrefactor_small_of_card_eq_one
    (Ω : Type*) [Fintype Ω] {theta : ℝ} (hcard : Fintype.card Ω = 1) :
    (((Fintype.card Ω - 1 : ℕ) : ℝ) * theta) < 1 := by
  rw [hcard]
  norm_num

/-- If the finite state space has exactly two elements, the finite-cardinality
partition-prefactor smallness condition is exactly the strict ratio bound
`theta < 1`. -/
theorem finiteSpectralPartitionPrefactor_small_of_card_eq_two
    (Ω : Type*) [Fintype Ω] {theta : ℝ} (hcard : Fintype.card Ω = 2)
    (htheta : theta < 1) :
    (((Fintype.card Ω - 1 : ℕ) : ℝ) * theta) < 1 := by
  rw [hcard]
  norm_num at htheta ⊢
  exact htheta

/-- For a one-site transverse layer, `LayerState S` has two states, so the
finite-cardinality partition-prefactor smallness condition follows from the
strict ratio bound `theta < 1`. -/
theorem finiteSpectralPartitionPrefactor_small_of_layerState_card_eq_one
    (S : Type*) [Fintype S] [DecidableEq S] {theta : ℝ}
    (hcard : Fintype.card S = 1) (htheta : theta < 1) :
    (((Fintype.card (LayerState S) - 1 : ℕ) : ℝ) * theta) < 1 :=
  finiteSpectralPartitionPrefactor_small_of_card_eq_two (LayerState S)
    (layerState_card_eq_two_of_card_eq_one S hcard) htheta

/-- A quantitative inverse-cardinality bound on `theta` implies the
finite-cardinality partition-prefactor smallness condition. -/
theorem finiteSpectralPartitionPrefactor_small_of_lt_inv_cardSubOne
    (Ω : Type*) [Fintype Ω] {theta : ℝ} (hcard : 1 < Fintype.card Ω)
    (htheta : theta < (((Fintype.card Ω - 1 : ℕ) : ℝ))⁻¹) :
    (((Fintype.card Ω - 1 : ℕ) : ℝ) * theta) < 1 := by
  have hpos_nat : 0 < Fintype.card Ω - 1 := Nat.sub_pos_of_lt hcard
  have hpos : 0 < ((Fintype.card Ω - 1 : ℕ) : ℝ) := by exact_mod_cast hpos_nat
  have hmul := mul_lt_mul_of_pos_left htheta hpos
  simpa [mul_inv_cancel₀ hpos.ne'] using hmul

/-- Trace of a power of a finite real Hermitian matrix as the sum of
powers of its Hermitian spectral-theorem eigenvalues. -/
theorem trace_pow_eq_sum_hermitian_eigenvalues_pow
    {M : Matrix Ω Ω ℝ} (hM : M.IsHermitian) (N : ℕ) :
    (M ^ N).trace = ∑ i, hM.eigenvalues i ^ N := by
  conv_lhs => rw [hM.spectral_theorem, Unitary.conjStarAlgAut_apply]
  rw [trace_matrix_conj_pow (Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues))
    (hM.eigenvectorUnitary : Matrix Ω Ω ℝ)
    (star (hM.eigenvectorUnitary : Matrix Ω Ω ℝ))]
  · simp [Matrix.diagonal_pow, Matrix.trace]
  · exact Unitary.coe_mul_star_self hM.eigenvectorUnitary
  · exact Unitary.coe_star_mul_self hM.eigenvectorUnitary

/-- Explicit finite real orthogonal diagonalization data for a matrix.

This is intentionally data, not a Perron--Frobenius theorem: later arguments may
obtain such data from mathlib's Hermitian spectral theorem or from a more
specialised finite transfer-matrix analysis. -/
structure RealOrthogonalSpectralData (M : Matrix Ω Ω ℝ) where
  /-- Eigenvalues in the chosen orthogonal basis. -/
  eigenvalue : Ω → ℝ
  /-- Orthogonal change-of-basis matrix whose columns are eigenvectors. -/
  changeOfBasis : Matrix Ω Ω ℝ
  /-- Left inverse relation for the orthogonal change of basis. -/
  orthogonal_left : changeOfBasisᵀ * changeOfBasis = 1
  /-- Right inverse relation for the orthogonal change of basis. -/
  orthogonal_right : changeOfBasis * changeOfBasisᵀ = 1
  /-- Diagonalization of the matrix in the chosen orthogonal basis. -/
  diagonalizes : M = changeOfBasis * Matrix.diagonal eigenvalue * changeOfBasisᵀ

namespace RealOrthogonalSpectralData

/-- Construct explicit real orthogonal spectral data from mathlib's Hermitian
spectral theorem.  This remains a finite spectral-theorem bridge, not a
Perron--Frobenius dominance statement. -/
noncomputable def ofHermitian {M : Matrix Ω Ω ℝ} (hM : M.IsHermitian) :
    RealOrthogonalSpectralData M where
  eigenvalue := hM.eigenvalues
  changeOfBasis := (hM.eigenvectorUnitary : Matrix Ω Ω ℝ)
  orthogonal_left := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial
      (A := (hM.eigenvectorUnitary : Matrix Ω Ω ℝ))]
    exact Unitary.coe_star_mul_self hM.eigenvectorUnitary
  orthogonal_right := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial
      (A := (hM.eigenvectorUnitary : Matrix Ω Ω ℝ))]
    exact Unitary.coe_mul_star_self hM.eigenvectorUnitary
  diagonalizes := by
    simpa [Unitary.conjStarAlgAut_apply] using hM.spectral_theorem

/-- The marking matrix transported to the orthogonal spectral basis. -/
noncomputable def markedMatrix {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (f : Ω → ℝ) : Matrix Ω Ω ℝ :=
  E.changeOfBasisᵀ * Matrix.diagonal f * E.changeOfBasis

/-- Entrywise expansion of the marked matrix `Qᵀ diag(f) Q`. -/
theorem markedMatrix_apply {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (f : Ω → ℝ) (i j : Ω) :
    E.markedMatrix f i j =
      ∑ x, E.changeOfBasis x i * f x * E.changeOfBasis x j := by
  rw [markedMatrix, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro x _
  rw [Matrix.mul_diagonal]
  simp [mul_assoc]

/-- Boundary-vector coordinates in the orthogonal spectral basis. -/
noncomputable def boundaryCoordinates {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (v : Ω → ℝ) : Ω → ℝ :=
  fun i => ∑ x, v x * E.changeOfBasis x i

/-- The finite boundary-vector marked product
`vLᵀ M^left diag(f) M^sep diag(f) M^right vR`. -/
noncomputable def boundaryMarkedProduct
    (M : Matrix Ω Ω ℝ) (vL f vR : Ω → ℝ)
    (left sep right : ℕ) : ℝ :=
  ∑ a, ∑ b,
    vL a * (M ^ left * Matrix.diagonal f * M ^ sep *
      Matrix.diagonal f * M ^ right) a b * vR b

/-- The boundary-vector marked product as a dot product. -/
theorem boundaryMarkedProduct_eq_dotProduct
    (M : Matrix Ω Ω ℝ) (vL f vR : Ω → ℝ)
    (left sep right : ℕ) :
    boundaryMarkedProduct M vL f vR left sep right =
      vL ⬝ᵥ ((M ^ left * Matrix.diagonal f * M ^ sep *
        Matrix.diagonal f * M ^ right) *ᵥ vR) := by
  unfold boundaryMarkedProduct
  simp only [dotProduct, mulVec]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The finite absolute coefficient prefactor in the spectral marked-trace
bound. -/
noncomputable def markedSpectralPrefactor {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (f : Ω → ℝ) : ℝ :=
  ∑ i, ∑ j, |E.markedMatrix f i j * E.markedMatrix f j i|

/-- The finite absolute coefficient prefactor for an open boundary-vector marked
spectral product. -/
noncomputable def boundaryMarkedSpectralPrefactor {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (f vL vR : Ω → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ l,
    |E.boundaryCoordinates vL i * E.markedMatrix f i j *
      E.markedMatrix f j l * E.boundaryCoordinates vR l|

/-- The marked spectral prefactor is nonnegative. -/
theorem markedSpectralPrefactor_nonneg {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (f : Ω → ℝ) :
    0 ≤ E.markedSpectralPrefactor f := by
  exact Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => abs_nonneg _

/-- The open boundary-vector marked spectral prefactor is nonnegative. -/
theorem boundaryMarkedSpectralPrefactor_nonneg {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (f vL vR : Ω → ℝ) :
    0 ≤ E.boundaryMarkedSpectralPrefactor f vL vR := by
  exact Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ =>
      Finset.sum_nonneg fun l _ => abs_nonneg _

/-- Marking by the constant-one function gives the identity in spectral
coordinates. -/
@[simp]
theorem markedMatrix_one {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) :
    E.markedMatrix (fun _ => (1 : ℝ)) = 1 := by
  unfold markedMatrix
  simp [E.orthogonal_left]

/-- The marked matrix `Qᵀ diag(f) Q` is symmetric for real orthogonal spectral
coordinates. -/
theorem markedMatrix_transpose {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (f : Ω → ℝ) :
    (E.markedMatrix f)ᵀ = E.markedMatrix f := by
  have hentry :
      ∀ i j, E.markedMatrix f i j =
        ∑ x, E.changeOfBasis x i * f x * E.changeOfBasis x j := by
    intro i j
    rw [markedMatrix, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro x _
    rw [Matrix.mul_diagonal]
    simp [mul_assoc]
  ext i j
  rw [Matrix.transpose_apply, hentry j i, hentry i j]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- Symmetry of the marked matrix entries in real orthogonal spectral
coordinates. -/
theorem markedMatrix_comm {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (f : Ω → ℝ) (i j : Ω) :
    E.markedMatrix f i j = E.markedMatrix f j i := by
  have h := congr_fun (congr_fun (E.markedMatrix_transpose f) i) j
  simpa using h.symm

/-- An odd observable has zero dominant marked diagonal against an even spectral
column. -/
theorem markedMatrix_diagonal_zero_of_equiv_odd_even {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (f : Ω → ℝ) (top : Ω) (τ : Ω ≃ Ω)
    (hf_odd : ∀ x, f (τ x) = -f x)
    (hvec_even : ∀ x, E.changeOfBasis (τ x) top = E.changeOfBasis x top) :
    E.markedMatrix f top top = 0 := by
  rw [E.markedMatrix_apply f top top]
  let term : Ω → ℝ :=
    fun x => E.changeOfBasis x top * f x * E.changeOfBasis x top
  change (∑ x : Ω, term x) = 0
  have hflip : ∀ x : Ω, term (τ x) = -term x := by
    intro x
    simp [term, hf_odd, hvec_even]
  have hsum_flip : (∑ x : Ω, term (τ x)) = ∑ x : Ω, term x :=
    Equiv.sum_comp τ term
  have hself_neg : (∑ x : Ω, term x) = -∑ x : Ω, term x := by
    calc
      (∑ x : Ω, term x) = ∑ x : Ω, term (τ x) := hsum_flip.symm
      _ = ∑ x : Ω, -term x := by simp_rw [hflip]
      _ = -∑ x : Ω, term x := by rw [Finset.sum_neg_distrib]
  linarith

/-- The fixed-site layer spin observable has zero dominant marked diagonal
against a flip-even spectral column. -/
theorem markedMatrix_layerSpinAt_diagonal_zero_of_flip_even
    {S : Type*} [Fintype S] [DecidableEq S]
    {M : Matrix (LayerState S) (LayerState S) ℝ}
    (E : RealOrthogonalSpectralData M) (x : S) (top : LayerState S)
    (hvec_even : ∀ ω : LayerState S,
      E.changeOfBasis (layerStateFlipEquiv S ω) top = E.changeOfBasis ω top) :
    E.markedMatrix (layerSpinAt x) top top = 0 :=
  E.markedMatrix_diagonal_zero_of_equiv_odd_even
    (layerSpinAt x) top (layerStateFlipEquiv S)
    (fun ω => layerSpinAt_flip x ω) hvec_even


end RealOrthogonalSpectralData

end TransferMatrix

end IsingModel

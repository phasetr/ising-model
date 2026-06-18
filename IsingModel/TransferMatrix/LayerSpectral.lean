import IsingModel.TransferMatrix.LayerGibbs
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.Tactic.NoncommRing

/-!
# Finite layer spectral scaffold (GJ §17.1)

This file prepares the finite cyclic layer transfer matrix for later
Perron--Frobenius and symmetric spectral arguments.  For a positive one-layer
weight `u`, the generally non-symmetric transfer matrix
`T a b = u b * k a b` is diagonally similar to the balanced matrix

`S a b = sqrt (u a) * k a b * sqrt (u b)`.

When the transition kernel `k` is symmetric, `S` is a symmetric real matrix.
The file records the diagonal similarity and the induced invariance of the
partition trace and the two-insertion marked trace.  It deliberately does not
prove a Perron--Frobenius theorem, a spectral gap, thermodynamic limits, or
exponential decay.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.1, pp. 304--306.
-/

namespace IsingModel

namespace TransferMatrix

open Matrix

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-! ## Positivity vocabulary -/

/-- Entrywise nonnegativity for a finite real matrix. -/
def MatrixEntrywiseNonnegative (M : Matrix Ω Ω ℝ) : Prop :=
  ∀ i j, 0 ≤ M i j

/-- Entrywise strict positivity for a finite real matrix. -/
def MatrixEntrywisePositive (M : Matrix Ω Ω ℝ) : Prop :=
  ∀ i j, 0 < M i j

/-- Nonnegativity for a finite real vector. -/
def VectorNonnegative (v : Ω → ℝ) : Prop :=
  ∀ i, 0 ≤ v i

/-- Strict positivity for a finite real vector. -/
def VectorPositive (v : Ω → ℝ) : Prop :=
  ∀ i, 0 < v i

omit [Fintype Ω] [DecidableEq Ω] in
/-- An entrywise positive matrix is entrywise nonnegative. -/
theorem matrixEntrywisePositive_nonnegative {M : Matrix Ω Ω ℝ}
    (hM : MatrixEntrywisePositive M) : MatrixEntrywiseNonnegative M :=
  fun i j => (hM i j).le

omit [Fintype Ω] [DecidableEq Ω] in
/-- The ordinary layer transfer matrix is entrywise positive when the layer and
transition weights are positive. -/
theorem layerTransferMatrix_entrywisePositive
    (u : Ω → ℝ) (k : Ω → Ω → ℝ)
    (hu : ∀ a, 0 < u a) (hk : ∀ a b, 0 < k a b) :
    MatrixEntrywisePositive (layerTransferMatrix u k) :=
  fun a b => mul_pos (hu b) (hk a b)

omit [DecidableEq Ω] in
/-- The product of two entrywise positive finite matrices is entrywise positive
when the index type is nonempty. -/
theorem matrixEntrywisePositive_mul [Nonempty Ω] {M N : Matrix Ω Ω ℝ}
    (hM : MatrixEntrywisePositive M) (hN : MatrixEntrywisePositive N) :
    MatrixEntrywisePositive (M * N) := by
  intro i j
  rw [Matrix.mul_apply]
  exact Finset.sum_pos (fun k _ => mul_pos (hM i k) (hN k j)) Finset.univ_nonempty

/-- Positive powers of an entrywise positive matrix remain entrywise positive. -/
theorem matrixEntrywisePositive_pow_of_pos [Nonempty Ω] {M : Matrix Ω Ω ℝ}
    (hM : MatrixEntrywisePositive M) {n : ℕ} (hn : 0 < n) :
    MatrixEntrywisePositive (M ^ n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hn)
  cases m with
  | zero =>
      simpa using hM
  | succ m =>
      have hprev : MatrixEntrywisePositive (M ^ (m + 1)) :=
        matrixEntrywisePositive_pow_of_pos hM (Nat.succ_pos m)
      rw [pow_succ]
      exact matrixEntrywisePositive_mul hprev hM

/-- An entrywise positive finite matrix is primitive in mathlib's graph-theoretic
matrix vocabulary.  This is only a positivity/primitive bridge, not a
Perron--Frobenius eigenvalue theorem. -/
theorem matrixEntrywisePositive_isPrimitive {M : Matrix Ω Ω ℝ}
    (hM : MatrixEntrywisePositive M) :
    M.IsPrimitive where
  nonneg := matrixEntrywisePositive_nonnegative hM
  exists_pos_pow := by
    refine ⟨1, Nat.zero_lt_one, ?_⟩
    intro i j
    simpa using hM i j

omit [Fintype Ω] [DecidableEq Ω] in
/-- An entrywise positive matrix is irreducible in mathlib's graph-theoretic
matrix vocabulary. -/
theorem matrixEntrywisePositive_isIrreducible {M : Matrix Ω Ω ℝ}
    (hM : MatrixEntrywisePositive M) :
    M.IsIrreducible := by
  refine ⟨matrixEntrywisePositive_nonnegative hM, ?_⟩
  intro i j
  letI : Quiver Ω := Matrix.toQuiver M
  exact ⟨Quiver.Hom.toPath (PLift.up (hM i j)), by simp⟩

/-- A positive power of an entrywise positive matrix has positive trace when the
index type is nonempty. -/
theorem trace_pow_pos_of_entrywisePositive [Nonempty Ω] {M : Matrix Ω Ω ℝ}
    (hM : MatrixEntrywisePositive M) {n : ℕ} (hn : 0 < n) :
    0 < (M ^ n).trace := by
  rw [Matrix.trace]
  exact Finset.sum_pos
    (fun i _ => matrixEntrywisePositive_pow_of_pos hM hn i i) Finset.univ_nonempty

/-- A strictly positive right eigenpair for a finite real matrix. -/
def StrictPositiveRightEigenpair (M : Matrix Ω Ω ℝ) (lam : ℝ) (v : Ω → ℝ) : Prop :=
  VectorPositive v ∧ M.mulVec v = lam • v

omit [DecidableEq Ω] in
/-- Applying an entrywise positive matrix to a strictly positive vector gives a
strictly positive vector. -/
theorem matrixEntrywisePositive_mulVec_pos [Nonempty Ω] {M : Matrix Ω Ω ℝ}
    {v : Ω → ℝ} (hM : MatrixEntrywisePositive M) (hv : VectorPositive v) :
    VectorPositive (M.mulVec v) := by
  intro i
  rw [Matrix.mulVec, dotProduct]
  exact Finset.sum_pos (fun j _ => mul_pos (hM i j) (hv j)) Finset.univ_nonempty

omit [DecidableEq Ω] in
/-- The eigenvalue in a strictly positive right eigenpair of an entrywise
positive matrix is positive. -/
theorem eigenvalue_pos_of_strictPositiveRightEigenpair [Nonempty Ω]
    {M : Matrix Ω Ω ℝ} (hM : MatrixEntrywisePositive M)
    {lam : ℝ} {v : Ω → ℝ} (hv : StrictPositiveRightEigenpair M lam v) :
    0 < lam := by
  let i : Ω := Classical.arbitrary Ω
  have hMv : 0 < M.mulVec v i := matrixEntrywisePositive_mulVec_pos hM hv.1 i
  have heq := congr_fun hv.2 i
  simp only [Pi.smul_apply, smul_eq_mul] at heq
  rw [heq] at hMv
  nlinarith [hv.1 i]

/-! ## Matrix conjugation helpers -/

/-- Powers of a matrix conjugate by mutually inverse matrices. -/
theorem matrix_conj_pow {R : Type*} [Semiring R] (A P Q : Matrix Ω Ω R)
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (n : ℕ) :
    (P * A * Q) ^ n = P * A ^ n * Q := by
  induction n with
  | zero =>
      simp [hPQ]
  | succ n ih =>
      rw [pow_succ, ih]
      calc
        (P * A ^ n * Q) * (P * A * Q) = P * A ^ n * (Q * P) * A * Q := by
          noncomm_ring
        _ = P * A ^ n * 1 * A * Q := by rw [hQP]
        _ = P * (A ^ n * A) * Q := by
          noncomm_ring

/-- Trace is invariant under conjugation by mutually inverse matrices. -/
theorem trace_matrix_conj_pow {R : Type*} [CommSemiring R] (A P Q : Matrix Ω Ω R)
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (n : ℕ) :
    ((P * A * Q) ^ n).trace = (A ^ n).trace := by
  rw [matrix_conj_pow A P Q hPQ hQP]
  calc
    (P * A ^ n * Q).trace = (Q * (P * A ^ n)).trace := by
      rw [trace_mul_comm]
    _ = ((Q * P) * A ^ n).trace := by
      rw [mul_assoc]
    _ = (A ^ n).trace := by
      rw [hQP, one_mul]

/-- Trace is invariant under conjugation by mutually inverse matrices. -/
theorem trace_matrix_conj {R : Type*} [CommSemiring R] (A P Q : Matrix Ω Ω R)
    (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    (P * A * Q).trace = A.trace := by
  simpa using trace_matrix_conj_pow A P Q hPQ hQP 1

/-- Diagonal matrices over a commutative semiring commute. -/
theorem diagonal_mul_comm {R : Type*} [CommSemiring R] (d e : Ω → R) :
    Matrix.diagonal d * Matrix.diagonal e = Matrix.diagonal e * Matrix.diagonal d := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.mul_diagonal, mul_comm]
  · have hji : j ≠ i := fun h => hij h.symm
    simp [Matrix.mul_diagonal, hij]

/-- A two-mark trace is invariant under a conjugation that commutes with the
diagonal marking matrix. -/
theorem trace_diagonal_conj_pow_diagonal_conj_pow {R : Type*} [CommSemiring R]
    (A P Q : Matrix Ω Ω R) (f : Ω → R)
    (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hFP : Matrix.diagonal f * P = P * Matrix.diagonal f)
    (hQF : Q * Matrix.diagonal f = Matrix.diagonal f * Q)
    (a b : ℕ) :
    (Matrix.diagonal f * (P * A * Q) ^ a
        * Matrix.diagonal f * (P * A * Q) ^ b).trace
      = (Matrix.diagonal f * A ^ a * Matrix.diagonal f * A ^ b).trace := by
  rw [matrix_conj_pow A P Q hPQ hQP a, matrix_conj_pow A P Q hPQ hQP b]
  have hmat :
      Matrix.diagonal f * (P * A ^ a * Q) * Matrix.diagonal f * (P * A ^ b * Q)
        = P * (Matrix.diagonal f * A ^ a * Matrix.diagonal f * A ^ b) * Q := by
    calc
      Matrix.diagonal f * (P * A ^ a * Q) * Matrix.diagonal f * (P * A ^ b * Q)
          = (Matrix.diagonal f * P) * A ^ a * (Q * Matrix.diagonal f) * P * A ^ b * Q := by
            noncomm_ring
      _ = (P * Matrix.diagonal f) * A ^ a * (Matrix.diagonal f * Q) * P * A ^ b * Q := by
            rw [hFP, hQF]
      _ = P * (Matrix.diagonal f * A ^ a * Matrix.diagonal f * A ^ b) * Q := by
            noncomm_ring [hQP]
  rw [hmat]
  exact trace_matrix_conj (Matrix.diagonal f * A ^ a * Matrix.diagonal f * A ^ b)
    P Q hPQ hQP

/-! ## Balanced layer transfer matrix -/

/-- The diagonal scaling matrix `D = diag(sqrt u)` used to balance a positive
finite layer transfer matrix. -/
noncomputable def layerTransferSqrtDiagonal (u : Ω → ℝ) : Matrix Ω Ω ℝ :=
  Matrix.diagonal fun a => Real.sqrt (u a)

/-- The inverse diagonal scaling matrix `D⁻¹ = diag((sqrt u)⁻¹)`. -/
noncomputable def layerTransferSqrtDiagonalInv (u : Ω → ℝ) : Matrix Ω Ω ℝ :=
  Matrix.diagonal fun a => (Real.sqrt (u a))⁻¹

/-- The balanced finite layer transfer matrix
`S a b = sqrt (u a) * k a b * sqrt (u b)`.  If `k` is symmetric, this is a
symmetric real matrix diagonally similar to `layerTransferMatrix u k`. -/
noncomputable def layerSymmetricTransferMatrix
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) : Matrix Ω Ω ℝ :=
  fun a b => Real.sqrt (u a) * k a b * Real.sqrt (u b)

/-- The trace-side partition function computed with the balanced layer transfer
matrix. -/
noncomputable def layerSymmetricTransferPartitionTrace
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (n : ℕ) : ℝ :=
  (layerSymmetricTransferMatrix u k ^ n).trace

/-- The two-insertion trace computed with the balanced layer transfer matrix. -/
noncomputable def layerSymmetricTransferCorrelationTrace
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ) (a b : ℕ) : ℝ :=
  (Matrix.diagonal f * layerSymmetricTransferMatrix u k ^ a
      * Matrix.diagonal f * layerSymmetricTransferMatrix u k ^ b).trace

/-- The square-root diagonal scaling and its inverse multiply to the identity. -/
theorem layerTransferSqrtDiagonalInv_mul_sqrtDiagonal
    (u : Ω → ℝ) (hu : ∀ a, 0 < u a) :
    layerTransferSqrtDiagonalInv u * layerTransferSqrtDiagonal u = 1 := by
  ext a b
  by_cases hab : a = b
  · subst b
    simp [layerTransferSqrtDiagonalInv, layerTransferSqrtDiagonal,
      inv_mul_cancel₀ (Real.sqrt_pos_of_pos (hu a)).ne']
  · simp [layerTransferSqrtDiagonalInv, layerTransferSqrtDiagonal,
      hab]

/-- The square-root diagonal scaling and its inverse multiply to the identity in
the opposite order. -/
theorem layerTransferSqrtDiagonal_mul_sqrtDiagonalInv
    (u : Ω → ℝ) (hu : ∀ a, 0 < u a) :
    layerTransferSqrtDiagonal u * layerTransferSqrtDiagonalInv u = 1 := by
  ext a b
  by_cases hab : a = b
  · subst b
    simp [layerTransferSqrtDiagonalInv, layerTransferSqrtDiagonal,
      mul_inv_cancel₀ (Real.sqrt_pos_of_pos (hu a)).ne']
  · simp [layerTransferSqrtDiagonalInv, layerTransferSqrtDiagonal,
      hab]

omit [Fintype Ω] [DecidableEq Ω] in
/-- The balanced transfer matrix is positive entrywise when the layer and
transition weights are positive. -/
theorem layerSymmetricTransferMatrix_pos
    (u : Ω → ℝ) (k : Ω → Ω → ℝ)
    (hu : ∀ a, 0 < u a) (hk : ∀ a b, 0 < k a b) (a b : Ω) :
    0 < layerSymmetricTransferMatrix u k a b := by
  exact mul_pos (mul_pos (Real.sqrt_pos.mpr (hu a)) (hk a b))
    (Real.sqrt_pos.mpr (hu b))

omit [Fintype Ω] [DecidableEq Ω] in
/-- The balanced layer transfer matrix is entrywise positive when the layer and
transition weights are positive. -/
theorem layerSymmetricTransferMatrix_entrywisePositive
    (u : Ω → ℝ) (k : Ω → Ω → ℝ)
    (hu : ∀ a, 0 < u a) (hk : ∀ a b, 0 < k a b) :
    MatrixEntrywisePositive (layerSymmetricTransferMatrix u k) :=
  layerSymmetricTransferMatrix_pos u k hu hk

/-- The balanced layer transfer matrix is primitive when the layer and transition
weights are positive.  This records the finite positive-matrix bridge but does
not assert a Perron--Frobenius eigenpair. -/
theorem layerSymmetricTransferMatrix_isPrimitive
    (u : Ω → ℝ) (k : Ω → Ω → ℝ)
    (hu : ∀ a, 0 < u a) (hk : ∀ a b, 0 < k a b) :
    (layerSymmetricTransferMatrix u k).IsPrimitive :=
  matrixEntrywisePositive_isPrimitive
    (layerSymmetricTransferMatrix_entrywisePositive u k hu hk)

omit [Fintype Ω] [DecidableEq Ω] in
/-- The balanced layer transfer matrix is irreducible when the layer and
transition weights are positive. -/
theorem layerSymmetricTransferMatrix_isIrreducible
    (u : Ω → ℝ) (k : Ω → Ω → ℝ)
    (hu : ∀ a, 0 < u a) (hk : ∀ a b, 0 < k a b) :
    (layerSymmetricTransferMatrix u k).IsIrreducible :=
  matrixEntrywisePositive_isIrreducible
    (layerSymmetricTransferMatrix_entrywisePositive u k hu hk)

omit [Fintype Ω] [DecidableEq Ω] in
/-- The ordinary layer transfer matrix is positive entrywise when the layer and
transition weights are positive. -/
theorem layerTransferMatrix_pos
    (u : Ω → ℝ) (k : Ω → Ω → ℝ)
    (hu : ∀ a, 0 < u a) (hk : ∀ a b, 0 < k a b) (a b : Ω) :
    0 < layerTransferMatrix u k a b := by
  exact mul_pos (hu b) (hk a b)

omit [Fintype Ω] [DecidableEq Ω] in
/-- The balanced layer transfer matrix is symmetric when the transition weight is
symmetric. -/
theorem layerSymmetricTransferMatrix_transpose
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (hk : ∀ a b, k a b = k b a) :
    (layerSymmetricTransferMatrix u k)ᵀ = layerSymmetricTransferMatrix u k := by
  ext a b
  simp [layerSymmetricTransferMatrix, hk b a]
  ring

omit [Fintype Ω] [DecidableEq Ω] in
/-- The balanced layer transfer matrix is Hermitian when the transition weight is
symmetric.  This is the entry point to mathlib's finite Hermitian spectral
theorem. -/
theorem layerSymmetricTransferMatrix_isHermitian
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (hk : ∀ a b, k a b = k b a) :
    (layerSymmetricTransferMatrix u k).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext a b
  simp [Matrix.conjTranspose, layerSymmetricTransferMatrix, hk b a]
  ring

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

/-- The finite absolute coefficient prefactor in the spectral marked-trace
bound. -/
noncomputable def markedSpectralPrefactor {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (f : Ω → ℝ) : ℝ :=
  ∑ i, ∑ j, |E.markedMatrix f i j * E.markedMatrix f j i|

/-- The marked spectral prefactor is nonnegative. -/
theorem markedSpectralPrefactor_nonneg {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (f : Ω → ℝ) :
    0 ≤ E.markedSpectralPrefactor f := by
  exact Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => abs_nonneg _

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

/-- Powers of a matrix with explicit orthogonal diagonalization. -/
theorem pow_eq {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (N : ℕ) :
    M ^ N = E.changeOfBasis * Matrix.diagonal (fun i => E.eigenvalue i ^ N)
      * E.changeOfBasisᵀ := by
  conv_lhs => rw [E.diagonalizes]
  simpa [Matrix.diagonal_pow] using
    matrix_conj_pow (Matrix.diagonal E.eigenvalue) E.changeOfBasis
    E.changeOfBasisᵀ E.orthogonal_right E.orthogonal_left N

/-- Trace of a power from explicit orthogonal diagonalization data. -/
theorem trace_pow_eq_sum {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (N : ℕ) :
    (M ^ N).trace = ∑ i, E.eigenvalue i ^ N := by
  rw [E.pow_eq N]
  rw [trace_matrix_conj (Matrix.diagonal fun i => E.eigenvalue i ^ N)
    E.changeOfBasis E.changeOfBasisᵀ E.orthogonal_right E.orthogonal_left]
  simp [Matrix.trace]

/-- Trace of two diagonal-power insertions in a fixed spectral basis. -/
theorem trace_marked_diagonal_pow_eq_sum
    (G : Matrix Ω Ω ℝ) (lam : Ω → ℝ) (a b : ℕ) :
    (G * Matrix.diagonal (fun i => lam i ^ a)
        * G * Matrix.diagonal (fun i => lam i ^ b)).trace
      = ∑ i, ∑ j, G i j * G j i * lam j ^ a * lam i ^ b := by
  rw [Matrix.trace]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.diag_apply]
  rw [Matrix.mul_diagonal]
  rw [Matrix.mul_apply]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.mul_diagonal]
  ring

/-- The balanced marked trace written in explicit orthogonal spectral data. -/
theorem marked_trace_eq_sum {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (f : Ω → ℝ) (a b : ℕ) :
    (Matrix.diagonal f * M ^ a * Matrix.diagonal f * M ^ b).trace
      = ∑ i, ∑ j,
          E.markedMatrix f i j * E.markedMatrix f j i
            * E.eigenvalue j ^ a * E.eigenvalue i ^ b := by
  rw [E.pow_eq a, E.pow_eq b]
  rw [show
      Matrix.diagonal f
          * (E.changeOfBasis * Matrix.diagonal (fun i => E.eigenvalue i ^ a)
              * E.changeOfBasisᵀ)
          * Matrix.diagonal f
          * (E.changeOfBasis * Matrix.diagonal (fun i => E.eigenvalue i ^ b)
              * E.changeOfBasisᵀ)
        =
          (Matrix.diagonal f * E.changeOfBasis
            * Matrix.diagonal (fun i => E.eigenvalue i ^ a)
            * E.changeOfBasisᵀ * Matrix.diagonal f * E.changeOfBasis
            * Matrix.diagonal (fun i => E.eigenvalue i ^ b))
            * E.changeOfBasisᵀ by
        noncomm_ring]
  rw [Matrix.trace_mul_comm]
  simp [markedMatrix, Matrix.mul_assoc]
  simpa [markedMatrix, Matrix.mul_assoc] using
    trace_marked_diagonal_pow_eq_sum (E.markedMatrix f) E.eigenvalue a b

/-- A nonnegative dominant spectral term gives a lower bound on the partition
spectral sum. -/
theorem partition_sum_lower_of_eigenvalue_nonnegative {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (top : Ω) (scale : ℝ)
    (dominant_eigenvalue : E.eigenvalue top = scale)
    (eigenvalue_nonnegative : ∀ i, 0 ≤ E.eigenvalue i)
    {N : ℕ} (_hN : 0 < N) :
    scale ^ N ≤ ∑ i, E.eigenvalue i ^ N := by
  have hterms : ∀ i ∈ (Finset.univ : Finset Ω), 0 ≤ E.eigenvalue i ^ N := by
    intro i _
    exact pow_nonneg (eigenvalue_nonnegative i) N
  have htop :=
    Finset.single_le_sum hterms (Finset.mem_univ top)
  simpa [dominant_eigenvalue] using htop

/-- A dominant index and a subdominant absolute bound imply the global
absolute eigenvalue bound. -/
theorem eigenvalue_abs_le_scale_of_dominant_bounds {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (top : Ω) (scale theta : ℝ)
    (scale_pos : 0 < scale)
    (theta_le_one : theta ≤ 1)
    (dominant_eigenvalue : E.eigenvalue top = scale)
    (subdominant_abs_le : ∀ i, i ≠ top → |E.eigenvalue i| ≤ theta * scale) :
    ∀ i, |E.eigenvalue i| ≤ scale := by
  intro i
  by_cases hitop : i = top
  · subst i
    simp [dominant_eigenvalue, abs_of_pos scale_pos]
  · calc
      |E.eigenvalue i| ≤ theta * scale := subdominant_abs_le i hitop
      _ ≤ scale := by
        exact (mul_le_iff_le_one_left scale_pos).2 theta_le_one

/-- A dominant eigenvalue and a uniform subdominant absolute bound give a finite
lower bound for the partition spectral sum. -/
theorem partition_sum_lower_of_dominant_bounds {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (top : Ω) (scale theta : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (dominant_eigenvalue : E.eigenvalue top = scale)
    (subdominant_abs_le : ∀ i, i ≠ top → |E.eigenvalue i| ≤ theta * scale)
    {N : ℕ} (_hN : 0 < N) :
    scale ^ N - (((Fintype.card Ω - 1 : ℕ) : ℝ) * (theta * scale) ^ N)
      ≤ ∑ i, E.eigenvalue i ^ N := by
  let rest : Finset Ω := Finset.univ.erase top
  have htheta_scale_nonneg : 0 ≤ theta * scale :=
    mul_nonneg theta_nonneg scale_pos.le
  have hrest_term :
      ∀ i ∈ rest, -((theta * scale) ^ N) ≤ E.eigenvalue i ^ N := by
    intro i hi
    have hitop : i ≠ top := (Finset.mem_erase.mp hi).1
    have hpow_abs : |E.eigenvalue i ^ N| ≤ (theta * scale) ^ N := by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (subdominant_abs_le i hitop) N
    exact neg_le_of_abs_le hpow_abs
  have hrest_sum :
      ∑ i ∈ rest, -((theta * scale) ^ N)
        ≤ ∑ i ∈ rest, E.eigenvalue i ^ N :=
    Finset.sum_le_sum hrest_term
  have hrest_sum' :
      -(((Fintype.card Ω - 1 : ℕ) : ℝ) * (theta * scale) ^ N)
        ≤ ∑ i ∈ rest, E.eigenvalue i ^ N := by
    simpa [rest, Finset.sum_const, nsmul_eq_mul,
      Finset.card_erase_of_mem (Finset.mem_univ top)] using hrest_sum
  have hadd := add_le_add_left hrest_sum' (scale ^ N)
  calc
    scale ^ N - (((Fintype.card Ω - 1 : ℕ) : ℝ) * (theta * scale) ^ N)
        = scale ^ N
          + -(((Fintype.card Ω - 1 : ℕ) : ℝ) * (theta * scale) ^ N) := by ring
    _ ≤ scale ^ N + ∑ i ∈ rest, E.eigenvalue i ^ N := by
      simpa [add_comm, add_left_comm, add_assoc] using hadd
    _ = (∑ i ∈ rest, E.eigenvalue i ^ N) + scale ^ N := by ring
    _ = ∑ i, E.eigenvalue i ^ N := by
      rw [← Finset.sum_erase_add (Finset.univ) (fun i => E.eigenvalue i ^ N)
        (Finset.mem_univ top)]
      simp [rest, dominant_eigenvalue]

/-- The finite-cardinality dominant-bound partition estimate in certificate
prefactor form. -/
theorem partition_lower_of_dominant_bounds {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (top : Ω) (scale theta : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_le_one : theta ≤ 1)
    (dominant_eigenvalue : E.eigenvalue top = scale)
    (subdominant_abs_le : ∀ i, i ≠ top → |E.eigenvalue i| ≤ theta * scale)
    {N : ℕ} (hN : 0 < N) :
    finiteSpectralPartitionPrefactor Ω theta * scale ^ N
      ≤ ∑ i, E.eigenvalue i ^ N := by
  have hN_one : 1 ≤ N := hN
  have htheta_pow_le : theta ^ N ≤ theta := by
    simpa using pow_le_pow_of_le_one theta_nonneg theta_le_one hN_one
  have hscale_pow_nonneg : 0 ≤ scale ^ N := pow_nonneg scale_pos.le N
  have hcard_mul :
      (((Fintype.card Ω - 1 : ℕ) : ℝ) * (theta * scale) ^ N)
        ≤ (((Fintype.card Ω - 1 : ℕ) : ℝ) * theta) * scale ^ N := by
    rw [mul_pow]
    calc
      (((Fintype.card Ω - 1 : ℕ) : ℝ) * (theta ^ N * scale ^ N))
          ≤ ((Fintype.card Ω - 1 : ℕ) : ℝ) * (theta * scale ^ N) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right htheta_pow_le hscale_pow_nonneg)
              (Nat.cast_nonneg _)
      _ = (((Fintype.card Ω - 1 : ℕ) : ℝ) * theta) * scale ^ N := by ring
  have hprefactor_le :
      finiteSpectralPartitionPrefactor Ω theta * scale ^ N
        ≤ scale ^ N - (((Fintype.card Ω - 1 : ℕ) : ℝ) * (theta * scale) ^ N) := by
    calc
      finiteSpectralPartitionPrefactor Ω theta * scale ^ N
          = scale ^ N
            - (((Fintype.card Ω - 1 : ℕ) : ℝ) * theta) * scale ^ N := by
              rw [finiteSpectralPartitionPrefactor]
              ring
      _ ≤ scale ^ N - (((Fintype.card Ω - 1 : ℕ) : ℝ) * (theta * scale) ^ N) :=
            sub_le_sub_left hcard_mul (scale ^ N)
  exact hprefactor_le.trans
    (partition_sum_lower_of_dominant_bounds E top scale theta scale_pos
      theta_nonneg dominant_eigenvalue subdominant_abs_le hN)

/-- Spectral dominance and cancellation of the dominant marked column give the
one-sided marked-trace bound in the separation exponent. -/
theorem marked_sum_abs_le_spectralPrefactor {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (f : Ω → ℝ) (top : Ω)
    (scale theta : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (eigenvalue_abs_le_scale : ∀ i, |E.eigenvalue i| ≤ scale)
    (subdominant_abs_le : ∀ i, i ≠ top → |E.eigenvalue i| ≤ theta * scale)
    (dominant_markedColumn_zero :
      ∀ i, E.markedMatrix f i top * E.markedMatrix f top i = 0)
    {a b : ℕ} (_ha : 0 < a) :
    |∑ i, ∑ j,
        E.markedMatrix f i j * E.markedMatrix f j i
          * E.eigenvalue j ^ a * E.eigenvalue i ^ b|
      ≤ E.markedSpectralPrefactor f * scale ^ (a + b) * theta ^ a := by
  let coeff : Ω → Ω → ℝ :=
    fun i j => E.markedMatrix f i j * E.markedMatrix f j i
  let term : Ω → Ω → ℝ :=
    fun i j => coeff i j * E.eigenvalue j ^ a * E.eigenvalue i ^ b
  have hscale_nonneg : 0 ≤ scale := scale_pos.le
  have htheta_scale_nonneg : 0 ≤ theta * scale :=
    mul_nonneg theta_nonneg hscale_nonneg
  have hsum :
      |∑ i, ∑ j, term i j| ≤ ∑ i, ∑ j, |term i j| := by
    calc
      |∑ i, ∑ j, term i j| ≤ ∑ i, |∑ j, term i j| :=
        Finset.abs_sum_le_sum_abs (fun i => ∑ j, term i j) Finset.univ
      _ ≤ ∑ i, ∑ j, |term i j| := by
        exact Finset.sum_le_sum fun i _ =>
          Finset.abs_sum_le_sum_abs (fun j => term i j) Finset.univ
  have hterm : ∀ i j, |term i j| ≤
      |coeff i j| * (scale ^ (a + b) * theta ^ a) := by
    intro i j
    by_cases hj : j = top
    · subst j
      have hcoeff : coeff i top = 0 := dominant_markedColumn_zero i
      simp [term, coeff, hcoeff]
    · have hjpow : |E.eigenvalue j| ^ a ≤ (theta * scale) ^ a :=
        pow_le_pow_left₀ (abs_nonneg _) (subdominant_abs_le j hj) a
      have hipow : |E.eigenvalue i| ^ b ≤ scale ^ b :=
        pow_le_pow_left₀ (abs_nonneg _) (eigenvalue_abs_le_scale i) b
      have hpow_mul :
          |E.eigenvalue j| ^ a * |E.eigenvalue i| ^ b
            ≤ (theta * scale) ^ a * scale ^ b :=
        mul_le_mul hjpow hipow (pow_nonneg (abs_nonneg _) b)
          (pow_nonneg htheta_scale_nonneg a)
      have hpow_eq :
          (theta * scale) ^ a * scale ^ b = scale ^ (a + b) * theta ^ a := by
        rw [mul_pow, pow_add]
        ring
      calc
        |term i j|
            = |coeff i j| * (|E.eigenvalue j| ^ a * |E.eigenvalue i| ^ b) := by
              simp [term, abs_mul, abs_pow, mul_assoc]
        _ ≤ |coeff i j| * ((theta * scale) ^ a * scale ^ b) :=
              mul_le_mul_of_nonneg_left hpow_mul (abs_nonneg _)
        _ = |coeff i j| * (scale ^ (a + b) * theta ^ a) := by
              rw [hpow_eq]
  calc
    |∑ i, ∑ j,
        E.markedMatrix f i j * E.markedMatrix f j i
          * E.eigenvalue j ^ a * E.eigenvalue i ^ b|
        = |∑ i, ∑ j, term i j| := rfl
    _ ≤ ∑ i, ∑ j, |term i j| := hsum
    _ ≤ ∑ i, ∑ j, |coeff i j| * (scale ^ (a + b) * theta ^ a) := by
      exact Finset.sum_le_sum fun i _ =>
        Finset.sum_le_sum fun j _ => hterm i j
    _ = E.markedSpectralPrefactor f * scale ^ (a + b) * theta ^ a := by
      simp [markedSpectralPrefactor, coeff, Finset.sum_mul, mul_assoc]

/-- Spectral dominance and cancellation of only the dominant-dominant marked
entry give a two-sided cyclic marked-trace bound.  This is the natural finite
cycle estimate: after the non-decaying `(top, top)` channel is removed, each
remaining spectral term has a subdominant eigenvalue on at least one arc. -/
theorem marked_sum_abs_le_spectralPrefactor_min {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (f : Ω → ℝ) (top : Ω)
    (scale theta : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_le_one : theta ≤ 1)
    (eigenvalue_abs_le_scale : ∀ i, |E.eigenvalue i| ≤ scale)
    (subdominant_abs_le : ∀ i, i ≠ top → |E.eigenvalue i| ≤ theta * scale)
    (dominant_markedDiagonal_zero : E.markedMatrix f top top = 0)
    {a b : ℕ} :
    |∑ i, ∑ j,
        E.markedMatrix f i j * E.markedMatrix f j i
          * E.eigenvalue j ^ a * E.eigenvalue i ^ b|
      ≤ E.markedSpectralPrefactor f * scale ^ (a + b) * theta ^ min a b := by
  let coeff : Ω → Ω → ℝ :=
    fun i j => E.markedMatrix f i j * E.markedMatrix f j i
  let term : Ω → Ω → ℝ :=
    fun i j => coeff i j * E.eigenvalue j ^ a * E.eigenvalue i ^ b
  have hscale_nonneg : 0 ≤ scale := scale_pos.le
  have htheta_scale_nonneg : 0 ≤ theta * scale :=
    mul_nonneg theta_nonneg hscale_nonneg
  have htheta_min_nonneg : 0 ≤ theta ^ min a b :=
    pow_nonneg theta_nonneg _
  have hsum :
      |∑ i, ∑ j, term i j| ≤ ∑ i, ∑ j, |term i j| := by
    calc
      |∑ i, ∑ j, term i j| ≤ ∑ i, |∑ j, term i j| :=
        Finset.abs_sum_le_sum_abs (fun i => ∑ j, term i j) Finset.univ
      _ ≤ ∑ i, ∑ j, |term i j| := by
        exact Finset.sum_le_sum fun i _ =>
          Finset.abs_sum_le_sum_abs (fun j => term i j) Finset.univ
  have hterm : ∀ i j, |term i j| ≤
      |coeff i j| * (scale ^ (a + b) * theta ^ min a b) := by
    intro i j
    by_cases hj : j = top
    · subst j
      by_cases hi : i = top
      · subst i
        have hcoeff : coeff top top = 0 := by
          simp [coeff, dominant_markedDiagonal_zero]
        simp [term, hcoeff]
      · have hjpow : |E.eigenvalue top| ^ a ≤ scale ^ a :=
          pow_le_pow_left₀ (abs_nonneg _) (eigenvalue_abs_le_scale top) a
        have hipow : |E.eigenvalue i| ^ b ≤ (theta * scale) ^ b :=
          pow_le_pow_left₀ (abs_nonneg _) (subdominant_abs_le i hi) b
        have hpow_mul :
            |E.eigenvalue top| ^ a * |E.eigenvalue i| ^ b
              ≤ scale ^ a * (theta * scale) ^ b :=
          mul_le_mul hjpow hipow (pow_nonneg (abs_nonneg _) b)
            (pow_nonneg hscale_nonneg a)
        have htheta_pow_le_min : theta ^ b ≤ theta ^ min a b :=
          pow_le_pow_of_le_one theta_nonneg theta_le_one (Nat.min_le_right a b)
        have hpow_eq :
            scale ^ a * (theta * scale) ^ b = scale ^ (a + b) * theta ^ b := by
          rw [mul_pow, pow_add]
          ring
        have hpow_target :
            scale ^ a * (theta * scale) ^ b
              ≤ scale ^ (a + b) * theta ^ min a b := by
          rw [hpow_eq]
          exact mul_le_mul_of_nonneg_left htheta_pow_le_min
            (pow_nonneg hscale_nonneg (a + b))
        calc
          |term i top|
              = |coeff i top| * (|E.eigenvalue top| ^ a * |E.eigenvalue i| ^ b) := by
                simp [term, abs_mul, abs_pow, mul_assoc]
          _ ≤ |coeff i top| * (scale ^ a * (theta * scale) ^ b) :=
                mul_le_mul_of_nonneg_left hpow_mul (abs_nonneg _)
          _ ≤ |coeff i top| * (scale ^ (a + b) * theta ^ min a b) :=
                mul_le_mul_of_nonneg_left hpow_target (abs_nonneg _)
    · have hjpow : |E.eigenvalue j| ^ a ≤ (theta * scale) ^ a :=
        pow_le_pow_left₀ (abs_nonneg _) (subdominant_abs_le j hj) a
      have hipow : |E.eigenvalue i| ^ b ≤ scale ^ b :=
        pow_le_pow_left₀ (abs_nonneg _) (eigenvalue_abs_le_scale i) b
      have hpow_mul :
          |E.eigenvalue j| ^ a * |E.eigenvalue i| ^ b
            ≤ (theta * scale) ^ a * scale ^ b :=
        mul_le_mul hjpow hipow (pow_nonneg (abs_nonneg _) b)
          (pow_nonneg htheta_scale_nonneg a)
      have htheta_pow_le_min : theta ^ a ≤ theta ^ min a b :=
        pow_le_pow_of_le_one theta_nonneg theta_le_one (Nat.min_le_left a b)
      have hpow_eq :
          (theta * scale) ^ a * scale ^ b = scale ^ (a + b) * theta ^ a := by
        rw [mul_pow, pow_add]
        ring
      have hpow_target :
          (theta * scale) ^ a * scale ^ b
            ≤ scale ^ (a + b) * theta ^ min a b := by
        rw [hpow_eq]
        exact mul_le_mul_of_nonneg_left htheta_pow_le_min
          (pow_nonneg hscale_nonneg (a + b))
      calc
        |term i j|
            = |coeff i j| * (|E.eigenvalue j| ^ a * |E.eigenvalue i| ^ b) := by
              simp [term, abs_mul, abs_pow, mul_assoc]
        _ ≤ |coeff i j| * ((theta * scale) ^ a * scale ^ b) :=
              mul_le_mul_of_nonneg_left hpow_mul (abs_nonneg _)
        _ ≤ |coeff i j| * (scale ^ (a + b) * theta ^ min a b) :=
              mul_le_mul_of_nonneg_left hpow_target (abs_nonneg _)
  calc
    |∑ i, ∑ j,
        E.markedMatrix f i j * E.markedMatrix f j i
          * E.eigenvalue j ^ a * E.eigenvalue i ^ b|
        = |∑ i, ∑ j, term i j| := rfl
    _ ≤ ∑ i, ∑ j, |term i j| := hsum
    _ ≤ ∑ i, ∑ j, |coeff i j| * (scale ^ (a + b) * theta ^ min a b) := by
      exact Finset.sum_le_sum fun i _ =>
        Finset.sum_le_sum fun j _ => hterm i j
    _ = E.markedSpectralPrefactor f * scale ^ (a + b) * theta ^ min a b := by
      simp [markedSpectralPrefactor, coeff, Finset.sum_mul, mul_assoc]

end RealOrthogonalSpectralData

/-- The finite Hermitian spectral-theorem eigenvalues of the balanced layer
transfer matrix.  They are indexed by the layer-state type. -/
noncomputable def layerSymmetricTransferEigenvalues
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (hk : ∀ a b, k a b = k b a) :
    Ω → ℝ :=
  (layerSymmetricTransferMatrix_isHermitian u k hk).eigenvalues

/-- The finite Hermitian spectral-theorem orthonormal eigenbasis of the balanced
layer transfer matrix. -/
noncomputable def layerSymmetricTransferEigenvectorBasis
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (hk : ∀ a b, k a b = k b a) :
    OrthonormalBasis Ω ℝ (EuclideanSpace ℝ Ω) :=
  (layerSymmetricTransferMatrix_isHermitian u k hk).eigenvectorBasis

/-- The balanced layer spectral basis diagonalizes the balanced transfer matrix. -/
theorem layerSymmetricTransferMatrix_mulVec_eigenvectorBasis
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (hk : ∀ a b, k a b = k b a) (j : Ω) :
    layerSymmetricTransferMatrix u k
        *ᵥ ⇑(layerSymmetricTransferEigenvectorBasis u k hk j)
      = (layerSymmetricTransferEigenvalues u k hk j)
        • ⇑(layerSymmetricTransferEigenvectorBasis u k hk j) := by
  exact (layerSymmetricTransferMatrix_isHermitian u k hk).mulVec_eigenvectorBasis j

/-- The balanced finite layer partition trace is the sum of powers of the
finite Hermitian spectral-theorem eigenvalues of the balanced transfer matrix. -/
theorem layerSymmetricTransferPartitionTrace_eq_sum_eigenvalues_pow
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (hk : ∀ a b, k a b = k b a) (N : ℕ) :
    layerSymmetricTransferPartitionTrace u k N
      = ∑ i, layerSymmetricTransferEigenvalues u k hk i ^ N := by
  rw [layerSymmetricTransferPartitionTrace, layerSymmetricTransferEigenvalues]
  exact trace_pow_eq_sum_hermitian_eigenvalues_pow
    (layerSymmetricTransferMatrix_isHermitian u k hk) N

/-- Explicit real orthogonal spectral data for the balanced layer transfer
matrix, obtained from the finite Hermitian spectral theorem. -/
noncomputable def layerSymmetricTransferOrthogonalSpectralData
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (hk : ∀ a b, k a b = k b a) :
    RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k) :=
  RealOrthogonalSpectralData.ofHermitian
    (layerSymmetricTransferMatrix_isHermitian u k hk)

/-- Diagonal similarity between the ordinary layer transfer matrix and the
balanced layer transfer matrix:
`T = D⁻¹ S D`. -/
theorem layerTransferMatrix_eq_sqrtDiagonalInv_mul_symm_mul_sqrtDiagonal
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (hu : ∀ a, 0 < u a) :
    layerTransferMatrix u k
      = layerTransferSqrtDiagonalInv u
        * layerSymmetricTransferMatrix u k * layerTransferSqrtDiagonal u := by
  ext a b
  simp [layerTransferMatrix, layerTransferSqrtDiagonalInv, layerTransferSqrtDiagonal,
    layerSymmetricTransferMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal]
  field_simp [(Real.sqrt_pos_of_pos (hu a)).ne']
  rw [Real.sq_sqrt (le_of_lt (hu b))]
  ring

/-- The finite layer partition trace is unchanged by replacing the transfer
matrix with its balanced diagonally similar form. -/
theorem layerTransferPartitionTrace_eq_layerSymmetricTransferPartitionTrace
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (hu : ∀ a, 0 < u a) (n : ℕ) :
    layerTransferPartitionTrace u k n
      = layerSymmetricTransferPartitionTrace u k n := by
  rw [layerTransferPartitionTrace, layerSymmetricTransferPartitionTrace,
    layerTransferMatrix_eq_sqrtDiagonalInv_mul_symm_mul_sqrtDiagonal u k hu]
  exact trace_matrix_conj_pow (layerSymmetricTransferMatrix u k)
    (layerTransferSqrtDiagonalInv u) (layerTransferSqrtDiagonal u)
    (layerTransferSqrtDiagonalInv_mul_sqrtDiagonal u hu)
    (layerTransferSqrtDiagonal_mul_sqrtDiagonalInv u hu) n

/-- The finite layer two-insertion trace is unchanged by replacing the transfer
matrix with its balanced diagonally similar form. -/
theorem layerTransferCorrelation_matrixElement_eq_layerSymmetricTransferCorrelationTrace
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (hu : ∀ a, 0 < u a) (a b : ℕ) :
    layerTransferCorrelation_matrixElement u k f a b
      = layerSymmetricTransferCorrelationTrace u k f a b := by
  rw [layerTransferCorrelation_matrixElement, layerSymmetricTransferCorrelationTrace,
    layerTransferMatrix_eq_sqrtDiagonalInv_mul_symm_mul_sqrtDiagonal u k hu]
  exact trace_diagonal_conj_pow_diagonal_conj_pow
    (layerSymmetricTransferMatrix u k)
    (layerTransferSqrtDiagonalInv u) (layerTransferSqrtDiagonal u) f
    (layerTransferSqrtDiagonalInv_mul_sqrtDiagonal u hu)
    (layerTransferSqrtDiagonal_mul_sqrtDiagonalInv u hu)
    (diagonal_mul_comm f fun x => (Real.sqrt (u x))⁻¹)
    (diagonal_mul_comm (fun x => Real.sqrt (u x)) f) a b

/-! ## Spectral-gap certificates -/

/-- A finite spectral-gap certificate for a layer transfer matrix.

This is not a Perron--Frobenius theorem.  It packages the data that a later
spectral proof may provide: a positive scale `lambda`, a subdominant ratio
`theta < 1`, a lower bound on the partition trace, and an upper bound on the
marked two-insertion trace. -/
structure LayerSpectralGapCertificate
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ) where
  /-- The positive dominant transfer scale. -/
  scale : ℝ
  /-- The nonnegative subdominant ratio. -/
  theta : ℝ
  /-- The numerator prefactor. -/
  prefactor : ℝ
  /-- The denominator prefactor in the partition lower bound. -/
  partitionPrefactor : ℝ
  /-- Positivity of the dominant transfer scale. -/
  scale_pos : 0 < scale
  /-- Nonnegativity of the subdominant ratio. -/
  theta_nonneg : 0 ≤ theta
  /-- Strict spectral-gap ratio bound. -/
  theta_lt_one : theta < 1
  /-- Nonnegativity of the numerator prefactor. -/
  prefactor_nonneg : 0 ≤ prefactor
  /-- Positivity of the partition prefactor. -/
  partitionPrefactor_pos : 0 < partitionPrefactor
  /-- Lower bound on the cyclic partition trace. -/
  partition_lower : ∀ {N : ℕ}, 0 < N →
    partitionPrefactor * scale ^ N ≤ layerTransferPartitionTrace u k N
  /-- Exponential upper bound on the marked two-insertion trace. -/
  marked_abs_le : ∀ {a b : ℕ}, 0 < a → 0 < b →
    |layerTransferCorrelation_matrixElement u k f a b|
      ≤ prefactor * scale ^ (a + b) * theta ^ a

/-- The denominator in a spectral-gap certificate is positive. -/
theorem layerTransferPartitionTrace_pos_of_spectralGapCertificate
    {u : Ω → ℝ} {k : Ω → Ω → ℝ} {f : Ω → ℝ}
    (h : LayerSpectralGapCertificate u k f) {N : ℕ} (hN : 0 < N) :
    0 < layerTransferPartitionTrace u k N := by
  exact lt_of_lt_of_le (mul_pos h.partitionPrefactor_pos (pow_pos h.scale_pos N))
    (h.partition_lower hN)

/-- A finite spectral-gap certificate gives exponential decay of the normalised
cyclic layer two-point trace ratio in the marked separation `a`. -/
theorem layerTwoPoint_abs_le_of_spectralGapCertificate
    {u : Ω → ℝ} {k : Ω → Ω → ℝ} {f : Ω → ℝ}
    (h : LayerSpectralGapCertificate u k f)
    {a b : ℕ} [NeZero a] (hb : 0 < b) :
    |layerTwoPoint u k f (a := a) (b := b) hb|
      ≤ (h.prefactor / h.partitionPrefactor) * h.theta ^ a := by
  have ha : 0 < a := Nat.pos_of_ne_zero (NeZero.ne a)
  have hN : 0 < a + b := Nat.add_pos_left ha b
  have hscaleN : 0 < h.scale ^ (a + b) := pow_pos h.scale_pos (a + b)
  have hθa : 0 ≤ h.theta ^ a := pow_nonneg h.theta_nonneg a
  have hlower_pos : 0 < h.partitionPrefactor * h.scale ^ (a + b) :=
    mul_pos h.partitionPrefactor_pos hscaleN
  have hden_lower := h.partition_lower hN
  have hden_pos : 0 < layerTransferPartitionTrace u k (a + b) :=
    lt_of_lt_of_le hlower_pos hden_lower
  have hmarked := h.marked_abs_le ha hb
  rw [layerTwoPoint_eq_trace_ratio, abs_div, abs_of_pos hden_pos]
  calc
    |layerTransferCorrelation_matrixElement u k f a b| /
        layerTransferPartitionTrace u k (a + b)
        = |layerTransferCorrelation_matrixElement u k f a b|
          * (layerTransferPartitionTrace u k (a + b))⁻¹ := by
            rw [div_eq_mul_inv]
    _ ≤ (h.prefactor * h.scale ^ (a + b) * h.theta ^ a)
          * (h.partitionPrefactor * h.scale ^ (a + b))⁻¹ := by
            exact mul_le_mul hmarked ((inv_le_inv₀ hden_pos hlower_pos).mpr hden_lower)
              (inv_nonneg.mpr hden_pos.le)
              (mul_nonneg (mul_nonneg h.prefactor_nonneg hscaleN.le) hθa)
    _ = (h.prefactor / h.partitionPrefactor) * h.theta ^ a := by
            field_simp [(ne_of_gt h.partitionPrefactor_pos), (ne_of_gt hscaleN)]

/-- Spin-observable wrapper for the spectral-gap certificate bound. -/
theorem layerSpinTwoPoint_abs_le_of_spectralGapCertificate
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    (x : S)
    (h : LayerSpectralGapCertificate u k (layerSpinAt x))
    {a b : ℕ} [NeZero a] (hb : 0 < b) :
    |layerSpinTwoPoint u k x (a := a) (b := b) hb|
      ≤ (h.prefactor / h.partitionPrefactor) * h.theta ^ a := by
  exact layerTwoPoint_abs_le_of_spectralGapCertificate h hb

/-! ## Balanced spectral-gap certificates -/

/-- A finite spectral-gap certificate stated on the balanced layer transfer
matrix.

This is the form expected from later symmetric spectral input for
`layerSymmetricTransferMatrix u k`.  The certificate is finite and algebraic:
it records bounds on the balanced partition trace and balanced marked trace,
but does not assert a Perron--Frobenius theorem or construct the bounds. -/
structure LayerBalancedSpectralGapCertificate
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ) where
  /-- The positive dominant transfer scale. -/
  scale : ℝ
  /-- The nonnegative subdominant ratio. -/
  theta : ℝ
  /-- The numerator prefactor. -/
  prefactor : ℝ
  /-- The denominator prefactor in the partition lower bound. -/
  partitionPrefactor : ℝ
  /-- Positivity of the dominant transfer scale. -/
  scale_pos : 0 < scale
  /-- Nonnegativity of the subdominant ratio. -/
  theta_nonneg : 0 ≤ theta
  /-- Strict spectral-gap ratio bound. -/
  theta_lt_one : theta < 1
  /-- Nonnegativity of the numerator prefactor. -/
  prefactor_nonneg : 0 ≤ prefactor
  /-- Positivity of the partition prefactor. -/
  partitionPrefactor_pos : 0 < partitionPrefactor
  /-- Lower bound on the balanced cyclic partition trace. -/
  partition_lower : ∀ {N : ℕ}, 0 < N →
    partitionPrefactor * scale ^ N ≤ layerSymmetricTransferPartitionTrace u k N
  /-- Exponential upper bound on the balanced marked two-insertion trace. -/
  marked_abs_le : ∀ {a b : ℕ}, 0 < a → 0 < b →
    |layerSymmetricTransferCorrelationTrace u k f a b|
      ≤ prefactor * scale ^ (a + b) * theta ^ a

/-- Transport a balanced trace certificate to the ordinary transfer-matrix
certificate using the diagonal similarity `T = D⁻¹ S D`. -/
def LayerBalancedSpectralGapCertificate.toLayerSpectralGapCertificate
    {u : Ω → ℝ} {k : Ω → Ω → ℝ} {f : Ω → ℝ}
    (h : LayerBalancedSpectralGapCertificate u k f)
    (hu : ∀ a, 0 < u a) :
    LayerSpectralGapCertificate u k f := by
  refine
    { scale := h.scale
      theta := h.theta
      prefactor := h.prefactor
      partitionPrefactor := h.partitionPrefactor
      scale_pos := h.scale_pos
      theta_nonneg := h.theta_nonneg
      theta_lt_one := h.theta_lt_one
      prefactor_nonneg := h.prefactor_nonneg
      partitionPrefactor_pos := h.partitionPrefactor_pos
      partition_lower := ?_
      marked_abs_le := ?_ }
  · intro N hN
    rw [layerTransferPartitionTrace_eq_layerSymmetricTransferPartitionTrace u k hu]
    exact h.partition_lower hN
  · intro a b ha hb
    rw [layerTransferCorrelation_matrixElement_eq_layerSymmetricTransferCorrelationTrace
      u k f hu]
    exact h.marked_abs_le ha hb

/-- A balanced finite spectral-gap certificate with the two-arc cyclic
marked-trace estimate `theta ^ min a b`.

This is weaker than a one-sided separation estimate but requires only the
dominant-dominant marked channel to vanish.  It is the natural finite cyclic
bound before taking a thermodynamic limit or imposing an arc-ordering. -/
structure LayerBalancedMinSpectralGapCertificate
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ) where
  /-- The positive dominant transfer scale. -/
  scale : ℝ
  /-- The nonnegative subdominant ratio. -/
  theta : ℝ
  /-- The numerator prefactor. -/
  prefactor : ℝ
  /-- The denominator prefactor in the partition lower bound. -/
  partitionPrefactor : ℝ
  /-- Positivity of the dominant transfer scale. -/
  scale_pos : 0 < scale
  /-- Nonnegativity of the subdominant ratio. -/
  theta_nonneg : 0 ≤ theta
  /-- Strict spectral-gap ratio bound. -/
  theta_lt_one : theta < 1
  /-- Nonnegativity of the numerator prefactor. -/
  prefactor_nonneg : 0 ≤ prefactor
  /-- Positivity of the partition prefactor. -/
  partitionPrefactor_pos : 0 < partitionPrefactor
  /-- Lower bound on the balanced cyclic partition trace. -/
  partition_lower : ∀ {N : ℕ}, 0 < N →
    partitionPrefactor * scale ^ N ≤ layerSymmetricTransferPartitionTrace u k N
  /-- Two-arc upper bound on the balanced marked two-insertion trace. -/
  marked_abs_le_min : ∀ {a b : ℕ}, 0 < a → 0 < b →
    |layerSymmetricTransferCorrelationTrace u k f a b|
      ≤ prefactor * scale ^ (a + b) * theta ^ min a b

/-- Constructor for an ordinary spectral-gap certificate from explicit
transfer-trace bounds. -/
def layerSpectralGapCertificate_of_traceBounds
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (scale theta prefactor partitionPrefactor : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (prefactor_nonneg : 0 ≤ prefactor)
    (partitionPrefactor_pos : 0 < partitionPrefactor)
    (partition_lower : ∀ {N : ℕ}, 0 < N →
      partitionPrefactor * scale ^ N ≤ layerTransferPartitionTrace u k N)
    (marked_abs_le : ∀ {a b : ℕ}, 0 < a → 0 < b →
      |layerTransferCorrelation_matrixElement u k f a b|
        ≤ prefactor * scale ^ (a + b) * theta ^ a) :
    LayerSpectralGapCertificate u k f where
  scale := scale
  theta := theta
  prefactor := prefactor
  partitionPrefactor := partitionPrefactor
  scale_pos := scale_pos
  theta_nonneg := theta_nonneg
  theta_lt_one := theta_lt_one
  prefactor_nonneg := prefactor_nonneg
  partitionPrefactor_pos := partitionPrefactor_pos
  partition_lower := partition_lower
  marked_abs_le := marked_abs_le

/-- Constructor for a balanced spectral-gap certificate from explicit balanced
trace bounds. -/
def layerBalancedSpectralGapCertificate_of_traceBounds
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (scale theta prefactor partitionPrefactor : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (prefactor_nonneg : 0 ≤ prefactor)
    (partitionPrefactor_pos : 0 < partitionPrefactor)
    (partition_lower : ∀ {N : ℕ}, 0 < N →
      partitionPrefactor * scale ^ N ≤ layerSymmetricTransferPartitionTrace u k N)
    (marked_abs_le : ∀ {a b : ℕ}, 0 < a → 0 < b →
      |layerSymmetricTransferCorrelationTrace u k f a b|
        ≤ prefactor * scale ^ (a + b) * theta ^ a) :
    LayerBalancedSpectralGapCertificate u k f where
  scale := scale
  theta := theta
  prefactor := prefactor
  partitionPrefactor := partitionPrefactor
  scale_pos := scale_pos
  theta_nonneg := theta_nonneg
  theta_lt_one := theta_lt_one
  prefactor_nonneg := prefactor_nonneg
  partitionPrefactor_pos := partitionPrefactor_pos
  partition_lower := partition_lower
  marked_abs_le := marked_abs_le

/-- Constructor for a balanced min-separation spectral-gap certificate from
explicit balanced trace bounds. -/
def layerBalancedMinSpectralGapCertificate_of_traceBounds
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (scale theta prefactor partitionPrefactor : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (prefactor_nonneg : 0 ≤ prefactor)
    (partitionPrefactor_pos : 0 < partitionPrefactor)
    (partition_lower : ∀ {N : ℕ}, 0 < N →
      partitionPrefactor * scale ^ N ≤ layerSymmetricTransferPartitionTrace u k N)
    (marked_abs_le_min : ∀ {a b : ℕ}, 0 < a → 0 < b →
      |layerSymmetricTransferCorrelationTrace u k f a b|
        ≤ prefactor * scale ^ (a + b) * theta ^ min a b) :
    LayerBalancedMinSpectralGapCertificate u k f where
  scale := scale
  theta := theta
  prefactor := prefactor
  partitionPrefactor := partitionPrefactor
  scale_pos := scale_pos
  theta_nonneg := theta_nonneg
  theta_lt_one := theta_lt_one
  prefactor_nonneg := prefactor_nonneg
  partitionPrefactor_pos := partitionPrefactor_pos
  partition_lower := partition_lower
  marked_abs_le_min := marked_abs_le_min

/-- Constructor for a balanced spectral-gap certificate from explicit
orthogonal spectral data and explicit spectral-basis bounds.

The hypotheses are deliberately stated as finite spectral-basis inequalities:
this does not assert Perron--Frobenius existence, identify a spectral radius, or
derive the one-sided cyclic marked-trace decay automatically. -/
def layerBalancedSpectralGapCertificate_of_orthogonalSpectralData
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (scale theta prefactor partitionPrefactor : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (prefactor_nonneg : 0 ≤ prefactor)
    (partitionPrefactor_pos : 0 < partitionPrefactor)
    (partition_lower_spectral : ∀ {N : ℕ}, 0 < N →
      partitionPrefactor * scale ^ N ≤ ∑ i, E.eigenvalue i ^ N)
    (marked_abs_le_spectral : ∀ {a b : ℕ}, 0 < a → 0 < b →
      |∑ i, ∑ j,
          E.markedMatrix f i j * E.markedMatrix f j i
            * E.eigenvalue j ^ a * E.eigenvalue i ^ b|
        ≤ prefactor * scale ^ (a + b) * theta ^ a) :
    LayerBalancedSpectralGapCertificate u k f := by
  refine
    layerBalancedSpectralGapCertificate_of_traceBounds u k f scale theta
      prefactor partitionPrefactor scale_pos theta_nonneg theta_lt_one
      prefactor_nonneg partitionPrefactor_pos ?_ ?_
  · intro N hN
    rw [layerSymmetricTransferPartitionTrace,
      RealOrthogonalSpectralData.trace_pow_eq_sum E N]
    exact partition_lower_spectral hN
  · intro a b ha hb
    rw [layerSymmetricTransferCorrelationTrace,
      RealOrthogonalSpectralData.marked_trace_eq_sum E f a b]
    exact marked_abs_le_spectral ha hb

/-- Constructor for a balanced spectral-gap certificate from explicit
orthogonal spectral data, a chosen dominant spectral index, finite spectral
dominance, and one-sided marked-column cancellation.

This proves the partition and marked-trace bounds from component spectral
hypotheses.  It does not assert the existence of a Perron--Frobenius eigenvector,
identify the spectral radius, or derive the cancellation hypothesis from the
observable. -/
noncomputable def layerBalancedSpectralGapCertificate_of_orthogonalSpectralDominance
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (top : Ω) (scale theta : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (dominant_eigenvalue : E.eigenvalue top = scale)
    (eigenvalue_nonnegative : ∀ i, 0 ≤ E.eigenvalue i)
    (eigenvalue_abs_le_scale : ∀ i, |E.eigenvalue i| ≤ scale)
    (subdominant_abs_le : ∀ i, i ≠ top → |E.eigenvalue i| ≤ theta * scale)
    (dominant_markedColumn_zero :
      ∀ i, E.markedMatrix f i top * E.markedMatrix f top i = 0) :
    LayerBalancedSpectralGapCertificate u k f :=
  layerBalancedSpectralGapCertificate_of_orthogonalSpectralData u k f E
    scale theta (E.markedSpectralPrefactor f) 1
    scale_pos theta_nonneg theta_lt_one
    (E.markedSpectralPrefactor_nonneg f) one_pos
    (fun hN => by
      simpa using
        RealOrthogonalSpectralData.partition_sum_lower_of_eigenvalue_nonnegative
          E top scale dominant_eigenvalue eigenvalue_nonnegative hN)
    (fun ha _hb =>
      RealOrthogonalSpectralData.marked_sum_abs_le_spectralPrefactor
        E f top scale theta scale_pos theta_nonneg eigenvalue_abs_le_scale
        subdominant_abs_le dominant_markedColumn_zero ha)

/-- Constructor for a balanced spectral-gap certificate from explicit
orthogonal spectral data, a chosen dominant spectral index, a subdominant
absolute spectral bound, and one-sided marked-column cancellation.

The partition prefactor is the finite-cardinality bound
`1 - (Fintype.card Ω - 1) * theta`, so this constructor also assumes that this
quantity is positive.  This remains a conditional finite spectral-basis bound:
it does not prove Perron--Frobenius existence, spectral-radius maximality, or
the cancellation hypothesis. -/
noncomputable def layerBalancedSpectralGapCertificate_of_orthogonalDominantBounds
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (top : Ω) (scale theta : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (partitionPrefactor_small :
      (((Fintype.card Ω - 1 : ℕ) : ℝ) * theta) < 1)
    (dominant_eigenvalue : E.eigenvalue top = scale)
    (subdominant_abs_le : ∀ i, i ≠ top → |E.eigenvalue i| ≤ theta * scale)
    (dominant_markedColumn_zero :
      ∀ i, E.markedMatrix f i top * E.markedMatrix f top i = 0) :
    LayerBalancedSpectralGapCertificate u k f :=
  layerBalancedSpectralGapCertificate_of_orthogonalSpectralData u k f E
    scale theta (E.markedSpectralPrefactor f)
    (finiteSpectralPartitionPrefactor Ω theta)
    scale_pos theta_nonneg theta_lt_one
    (E.markedSpectralPrefactor_nonneg f)
    (finiteSpectralPartitionPrefactor_pos Ω partitionPrefactor_small)
    (fun hN =>
      RealOrthogonalSpectralData.partition_lower_of_dominant_bounds
        E top scale theta scale_pos theta_nonneg theta_lt_one.le
        dominant_eigenvalue subdominant_abs_le hN)
    (fun ha _hb =>
      RealOrthogonalSpectralData.marked_sum_abs_le_spectralPrefactor
        E f top scale theta scale_pos theta_nonneg
        (RealOrthogonalSpectralData.eigenvalue_abs_le_scale_of_dominant_bounds
          E top scale theta scale_pos theta_lt_one.le dominant_eigenvalue
          subdominant_abs_le)
        subdominant_abs_le dominant_markedColumn_zero ha)

/-- Constructor for a balanced min-separation spectral-gap certificate from
explicit orthogonal spectral data and explicit spectral-basis bounds. -/
def layerBalancedMinSpectralGapCertificate_of_orthogonalSpectralData
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (scale theta prefactor partitionPrefactor : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (prefactor_nonneg : 0 ≤ prefactor)
    (partitionPrefactor_pos : 0 < partitionPrefactor)
    (partition_lower_spectral : ∀ {N : ℕ}, 0 < N →
      partitionPrefactor * scale ^ N ≤ ∑ i, E.eigenvalue i ^ N)
    (marked_abs_le_min_spectral : ∀ {a b : ℕ}, 0 < a → 0 < b →
      |∑ i, ∑ j,
          E.markedMatrix f i j * E.markedMatrix f j i
            * E.eigenvalue j ^ a * E.eigenvalue i ^ b|
        ≤ prefactor * scale ^ (a + b) * theta ^ min a b) :
    LayerBalancedMinSpectralGapCertificate u k f := by
  refine
    layerBalancedMinSpectralGapCertificate_of_traceBounds u k f scale theta
      prefactor partitionPrefactor scale_pos theta_nonneg theta_lt_one
      prefactor_nonneg partitionPrefactor_pos ?_ ?_
  · intro N hN
    rw [layerSymmetricTransferPartitionTrace,
      RealOrthogonalSpectralData.trace_pow_eq_sum E N]
    exact partition_lower_spectral hN
  · intro a b ha hb
    rw [layerSymmetricTransferCorrelationTrace,
      RealOrthogonalSpectralData.marked_trace_eq_sum E f a b]
    exact marked_abs_le_min_spectral ha hb

/-- Constructor for a balanced min-separation spectral-gap certificate from
explicit orthogonal spectral data, a chosen dominant spectral index, a
subdominant absolute spectral bound, and dominant-dominant marked-channel
cancellation. -/
noncomputable def layerBalancedMinSpectralGapCertificate_of_orthogonalDominantBounds
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (top : Ω) (scale theta : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (partitionPrefactor_small :
      (((Fintype.card Ω - 1 : ℕ) : ℝ) * theta) < 1)
    (dominant_eigenvalue : E.eigenvalue top = scale)
    (subdominant_abs_le : ∀ i, i ≠ top → |E.eigenvalue i| ≤ theta * scale)
    (dominant_markedDiagonal_zero : E.markedMatrix f top top = 0) :
    LayerBalancedMinSpectralGapCertificate u k f :=
  layerBalancedMinSpectralGapCertificate_of_orthogonalSpectralData u k f E
    scale theta (E.markedSpectralPrefactor f)
    (finiteSpectralPartitionPrefactor Ω theta)
    scale_pos theta_nonneg theta_lt_one
    (E.markedSpectralPrefactor_nonneg f)
    (finiteSpectralPartitionPrefactor_pos Ω partitionPrefactor_small)
    (fun hN =>
      RealOrthogonalSpectralData.partition_lower_of_dominant_bounds
        E top scale theta scale_pos theta_nonneg theta_lt_one.le
        dominant_eigenvalue subdominant_abs_le hN)
    (fun _ha _hb =>
      RealOrthogonalSpectralData.marked_sum_abs_le_spectralPrefactor_min
        E f top scale theta scale_pos theta_nonneg theta_lt_one.le
        (RealOrthogonalSpectralData.eigenvalue_abs_le_scale_of_dominant_bounds
          E top scale theta scale_pos theta_lt_one.le dominant_eigenvalue
          subdominant_abs_le)
        subdominant_abs_le dominant_markedDiagonal_zero)

/-- Constructor for a balanced min-separation spectral-gap certificate using
the Hermitian spectral theorem data attached to the balanced transfer matrix. -/
noncomputable def layerBalancedMinSpectralGapCertificate_of_layerHermitianDominantBounds
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (hk : ∀ a b, k a b = k b a)
    (top : Ω) (scale theta : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (partitionPrefactor_small :
      (((Fintype.card Ω - 1 : ℕ) : ℝ) * theta) < 1)
    (dominant_eigenvalue :
      (layerSymmetricTransferOrthogonalSpectralData u k hk).eigenvalue top = scale)
    (subdominant_abs_le : ∀ i, i ≠ top →
      |(layerSymmetricTransferOrthogonalSpectralData u k hk).eigenvalue i|
        ≤ theta * scale)
    (dominant_markedDiagonal_zero :
      (layerSymmetricTransferOrthogonalSpectralData u k hk).markedMatrix f top top = 0) :
    LayerBalancedMinSpectralGapCertificate u k f :=
  layerBalancedMinSpectralGapCertificate_of_orthogonalDominantBounds u k f
    (layerSymmetricTransferOrthogonalSpectralData u k hk) top scale theta
    scale_pos theta_nonneg theta_lt_one partitionPrefactor_small
    dominant_eigenvalue subdominant_abs_le dominant_markedDiagonal_zero

/-- Constructor for an ordinary spectral-gap certificate from explicit balanced
trace bounds, transported across the diagonal similarity. -/
def layerSpectralGapCertificate_of_balancedTraceBounds
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (hu : ∀ a, 0 < u a)
    (scale theta prefactor partitionPrefactor : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (prefactor_nonneg : 0 ≤ prefactor)
    (partitionPrefactor_pos : 0 < partitionPrefactor)
    (partition_lower : ∀ {N : ℕ}, 0 < N →
      partitionPrefactor * scale ^ N ≤ layerSymmetricTransferPartitionTrace u k N)
    (marked_abs_le : ∀ {a b : ℕ}, 0 < a → 0 < b →
      |layerSymmetricTransferCorrelationTrace u k f a b|
        ≤ prefactor * scale ^ (a + b) * theta ^ a) :
    LayerSpectralGapCertificate u k f :=
  (layerBalancedSpectralGapCertificate_of_traceBounds u k f scale theta prefactor
    partitionPrefactor scale_pos theta_nonneg theta_lt_one prefactor_nonneg
    partitionPrefactor_pos partition_lower marked_abs_le).toLayerSpectralGapCertificate hu

/-- A balanced finite spectral-gap certificate gives exponential decay of the
normalised cyclic layer two-point trace ratio. -/
theorem layerTwoPoint_abs_le_of_balancedSpectralGapCertificate
    {u : Ω → ℝ} {k : Ω → Ω → ℝ} {f : Ω → ℝ}
    (hu : ∀ a, 0 < u a)
    (h : LayerBalancedSpectralGapCertificate u k f)
    {a b : ℕ} [NeZero a] (hb : 0 < b) :
    |layerTwoPoint u k f (a := a) (b := b) hb|
      ≤ (h.prefactor / h.partitionPrefactor) * h.theta ^ a :=
  by
    simpa using
      (layerTwoPoint_abs_le_of_spectralGapCertificate
        (h.toLayerSpectralGapCertificate hu) hb)

/-- Spin-observable wrapper for the balanced spectral-gap certificate bound. -/
theorem layerSpinTwoPoint_abs_le_of_balancedSpectralGapCertificate
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    (x : S)
    (hu : ∀ a, 0 < u a)
    (h : LayerBalancedSpectralGapCertificate u k (layerSpinAt x))
    {a b : ℕ} [NeZero a] (hb : 0 < b) :
    |layerSpinTwoPoint u k x (a := a) (b := b) hb|
      ≤ (h.prefactor / h.partitionPrefactor) * h.theta ^ a :=
  by
    simpa using
      (layerSpinTwoPoint_abs_le_of_spectralGapCertificate u k x
        (h.toLayerSpectralGapCertificate hu) hb)

/-- A balanced min-separation spectral-gap certificate gives the two-arc cyclic
decay bound for the normalised layer two-point trace ratio. -/
theorem layerTwoPoint_abs_le_min_of_balancedMinSpectralGapCertificate
    {u : Ω → ℝ} {k : Ω → Ω → ℝ} {f : Ω → ℝ}
    (hu : ∀ a, 0 < u a)
    (h : LayerBalancedMinSpectralGapCertificate u k f)
    {a b : ℕ} [NeZero a] (hb : 0 < b) :
    |layerTwoPoint u k f (a := a) (b := b) hb|
      ≤ (h.prefactor / h.partitionPrefactor) * h.theta ^ min a b := by
  have ha : 0 < a := Nat.pos_of_ne_zero (NeZero.ne a)
  have hN : 0 < a + b := Nat.add_pos_left ha b
  have hscaleN : 0 < h.scale ^ (a + b) := pow_pos h.scale_pos (a + b)
  have hθmin : 0 ≤ h.theta ^ min a b := pow_nonneg h.theta_nonneg _
  have hlower_pos : 0 < h.partitionPrefactor * h.scale ^ (a + b) :=
    mul_pos h.partitionPrefactor_pos hscaleN
  have hden_lower : h.partitionPrefactor * h.scale ^ (a + b)
      ≤ layerTransferPartitionTrace u k (a + b) := by
    rw [layerTransferPartitionTrace_eq_layerSymmetricTransferPartitionTrace u k hu]
    exact h.partition_lower hN
  have hden_pos : 0 < layerTransferPartitionTrace u k (a + b) :=
    lt_of_lt_of_le hlower_pos hden_lower
  have hmarked : |layerTransferCorrelation_matrixElement u k f a b|
      ≤ h.prefactor * h.scale ^ (a + b) * h.theta ^ min a b := by
    rw [layerTransferCorrelation_matrixElement_eq_layerSymmetricTransferCorrelationTrace
      u k f hu]
    exact h.marked_abs_le_min ha hb
  rw [layerTwoPoint_eq_trace_ratio, abs_div, abs_of_pos hden_pos]
  calc
    |layerTransferCorrelation_matrixElement u k f a b| /
        layerTransferPartitionTrace u k (a + b)
        = |layerTransferCorrelation_matrixElement u k f a b|
          * (layerTransferPartitionTrace u k (a + b))⁻¹ := by
            rw [div_eq_mul_inv]
    _ ≤ (h.prefactor * h.scale ^ (a + b) * h.theta ^ min a b)
          * (h.partitionPrefactor * h.scale ^ (a + b))⁻¹ := by
            exact mul_le_mul hmarked ((inv_le_inv₀ hden_pos hlower_pos).mpr hden_lower)
              (inv_nonneg.mpr hden_pos.le)
              (mul_nonneg (mul_nonneg h.prefactor_nonneg hscaleN.le) hθmin)
    _ = (h.prefactor / h.partitionPrefactor) * h.theta ^ min a b := by
            field_simp [(ne_of_gt h.partitionPrefactor_pos), (ne_of_gt hscaleN)]

/-- If the marked separation is no longer than the complementary arc, the
two-arc min-separation bound becomes the usual one-sided separation bound. -/
theorem layerTwoPoint_abs_le_left_of_balancedMinSpectralGapCertificate
    {u : Ω → ℝ} {k : Ω → Ω → ℝ} {f : Ω → ℝ}
    (hu : ∀ a, 0 < u a)
    (h : LayerBalancedMinSpectralGapCertificate u k f)
    {a b : ℕ} [NeZero a] (hb : 0 < b) (hab : a ≤ b) :
    |layerTwoPoint u k f (a := a) (b := b) hb|
      ≤ (h.prefactor / h.partitionPrefactor) * h.theta ^ a := by
  simpa [Nat.min_eq_left hab] using
    (layerTwoPoint_abs_le_min_of_balancedMinSpectralGapCertificate
      (u := u) (k := k) (f := f) hu h (a := a) (b := b) hb)

/-- Spin-observable wrapper for the balanced min-separation certificate bound. -/
theorem layerSpinTwoPoint_abs_le_min_of_balancedMinSpectralGapCertificate
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    (x : S)
    (hu : ∀ a, 0 < u a)
    (h : LayerBalancedMinSpectralGapCertificate u k (layerSpinAt x))
    {a b : ℕ} [NeZero a] (hb : 0 < b) :
    |layerSpinTwoPoint u k x (a := a) (b := b) hb|
      ≤ (h.prefactor / h.partitionPrefactor) * h.theta ^ min a b :=
  by
    simpa using
      (layerTwoPoint_abs_le_min_of_balancedMinSpectralGapCertificate
        (u := u) (k := k) (f := layerSpinAt x) hu h (a := a) (b := b) hb)

end TransferMatrix

end IsingModel

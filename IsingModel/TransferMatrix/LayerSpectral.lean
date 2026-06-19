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

omit [Fintype Ω] [DecidableEq Ω] in
/-- The balanced transfer matrix is invariant under simultaneous relabelling by
an equivalence that preserves the layer and transition weights. -/
theorem layerSymmetricTransferMatrix_equiv_equiv
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (τ : Ω ≃ Ω)
    (huτ : ∀ a, u (τ a) = u a)
    (hkτ : ∀ a b, k (τ a) (τ b) = k a b) (a b : Ω) :
    layerSymmetricTransferMatrix u k (τ a) (τ b)
      = layerSymmetricTransferMatrix u k a b := by
  simp [layerSymmetricTransferMatrix, huτ, hkτ]

/-- The balanced layer transfer matrix is invariant under simultaneous global
spin flip when the layer and transition weights are. -/
theorem layerSymmetricTransferMatrix_flip_flip
    {S : Type*} (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (ω η : LayerState S) :
    layerSymmetricTransferMatrix u k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η)
      = layerSymmetricTransferMatrix u k ω η :=
  layerSymmetricTransferMatrix_equiv_equiv u k (layerStateFlipEquiv S)
    hu_flip hk_flip ω η

omit [DecidableEq Ω] in
/-- The balanced transfer matrix commutes with the vector-level action induced
by a weight-preserving equivalence. -/
theorem layerSymmetricTransferMatrix_mulVec_comp_equiv
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (τ : Ω ≃ Ω)
    (huτ : ∀ a, u (τ a) = u a)
    (hkτ : ∀ a b, k (τ a) (τ b) = k a b)
    (v : Ω → ℝ) :
    (layerSymmetricTransferMatrix u k).mulVec (v ∘ τ)
      = (layerSymmetricTransferMatrix u k).mulVec v ∘ τ := by
  ext a
  change (∑ b : Ω, layerSymmetricTransferMatrix u k a b * (v ∘ τ) b)
      = ∑ b : Ω, layerSymmetricTransferMatrix u k (τ a) b * v b
  dsimp [Function.comp]
  have hsum :
      (∑ b : Ω, layerSymmetricTransferMatrix u k (τ a) (τ b) * v (τ b))
        = ∑ b : Ω, layerSymmetricTransferMatrix u k (τ a) b * v b := by
    exact Equiv.sum_comp τ
      (fun b => layerSymmetricTransferMatrix u k (τ a) b * v b)
  calc
    (∑ b : Ω, layerSymmetricTransferMatrix u k a b * v (τ b))
        = ∑ b : Ω, layerSymmetricTransferMatrix u k (τ a) (τ b) * v (τ b) := by
          apply Finset.sum_congr rfl
          intro b _
          rw [layerSymmetricTransferMatrix_equiv_equiv u k τ huτ hkτ a b]
    _ = ∑ b : Ω, layerSymmetricTransferMatrix u k (τ a) b * v b := hsum

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

/-! ## Flip-parity selection rules -/

/-- A spectral-data column is even under an involutive relabelling. -/
def ColumnFlipEven {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (τ : Ω ≃ Ω) (i : Ω) : Prop :=
  ∀ x, E.changeOfBasis (τ x) i = E.changeOfBasis x i

/-- A spectral-data column is odd under an involutive relabelling. -/
def ColumnFlipOdd {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (τ : Ω ≃ Ω) (i : Ω) : Prop :=
  ∀ x, E.changeOfBasis (τ x) i = -E.changeOfBasis x i

/-- A spectral basis is adapted to a two-sector flip parity when every column
is either even or odd under the relabelling. -/
def ColumnFlipParity {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (τ : Ω ≃ Ω) : Prop :=
  ∀ i, E.ColumnFlipEven τ i ∨ E.ColumnFlipOdd τ i

/-- An even boundary vector has zero coordinate against an odd spectral-data
column. -/
theorem boundaryCoordinates_zero_of_equiv_even_odd {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (v : Ω → ℝ) (i : Ω) (τ : Ω ≃ Ω)
    (hv_even : ∀ x, v (τ x) = v x)
    (hcol_odd : E.ColumnFlipOdd τ i) :
    E.boundaryCoordinates v i = 0 := by
  rw [boundaryCoordinates]
  let term : Ω → ℝ := fun x => v x * E.changeOfBasis x i
  change (∑ x : Ω, term x) = 0
  have hflip : ∀ x : Ω, term (τ x) = -term x := by
    intro x
    simp [term, hv_even x, hcol_odd x]
  have hsum_flip : (∑ x : Ω, term (τ x)) = ∑ x : Ω, term x :=
    Equiv.sum_comp τ term
  have hself_neg : (∑ x : Ω, term x) = -∑ x : Ω, term x := by
    calc
      (∑ x : Ω, term x) = ∑ x : Ω, term (τ x) := hsum_flip.symm
      _ = ∑ x : Ω, -term x := by simp_rw [hflip]
      _ = -∑ x : Ω, term x := by rw [Finset.sum_neg_distrib]
  linarith

/-- An odd observable has zero marked-matrix entry between two even
spectral-data columns. -/
theorem markedMatrix_zero_of_equiv_odd_even_even {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (f : Ω → ℝ) (i j : Ω) (τ : Ω ≃ Ω)
    (hf_odd : ∀ x, f (τ x) = -f x)
    (hi_even : E.ColumnFlipEven τ i) (hj_even : E.ColumnFlipEven τ j) :
    E.markedMatrix f i j = 0 := by
  rw [E.markedMatrix_apply f i j]
  let term : Ω → ℝ :=
    fun x => E.changeOfBasis x i * f x * E.changeOfBasis x j
  change (∑ x : Ω, term x) = 0
  have hflip : ∀ x : Ω, term (τ x) = -term x := by
    intro x
    simp [term, hf_odd x, hi_even x, hj_even x]
  have hsum_flip : (∑ x : Ω, term (τ x)) = ∑ x : Ω, term x :=
    Equiv.sum_comp τ term
  have hself_neg : (∑ x : Ω, term x) = -∑ x : Ω, term x := by
    calc
      (∑ x : Ω, term x) = ∑ x : Ω, term (τ x) := hsum_flip.symm
      _ = ∑ x : Ω, -term x := by simp_rw [hflip]
      _ = -∑ x : Ω, term x := by rw [Finset.sum_neg_distrib]
  linarith

/-- An odd observable has zero marked-matrix entry between two odd
spectral-data columns. -/
theorem markedMatrix_zero_of_equiv_odd_odd_odd {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (f : Ω → ℝ) (i j : Ω) (τ : Ω ≃ Ω)
    (hf_odd : ∀ x, f (τ x) = -f x)
    (hi_odd : E.ColumnFlipOdd τ i) (hj_odd : E.ColumnFlipOdd τ j) :
    E.markedMatrix f i j = 0 := by
  rw [E.markedMatrix_apply f i j]
  let term : Ω → ℝ :=
    fun x => E.changeOfBasis x i * f x * E.changeOfBasis x j
  change (∑ x : Ω, term x) = 0
  have hflip : ∀ x : Ω, term (τ x) = -term x := by
    intro x
    simp [term, hf_odd x, hi_odd x, hj_odd x]
  have hsum_flip : (∑ x : Ω, term (τ x)) = ∑ x : Ω, term x :=
    Equiv.sum_comp τ term
  have hself_neg : (∑ x : Ω, term x) = -∑ x : Ω, term x := by
    calc
      (∑ x : Ω, term x) = ∑ x : Ω, term (τ x) := hsum_flip.symm
      _ = ∑ x : Ω, -term x := by simp_rw [hflip]
      _ = -∑ x : Ω, term x := by rw [Finset.sum_neg_distrib]
  linarith

/-- If the left boundary vector is even, the observable is odd, the top column
is even, and every spectral-data column has a flip parity, then the open
central marked channel vanishes coefficientwise. -/
theorem boundaryMarkedCentral_zero_of_equiv_evenBoundary_columnParity
    {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (f vL vR : Ω → ℝ)
    (top : Ω) (τ : Ω ≃ Ω)
    (hf_odd : ∀ x, f (τ x) = -f x)
    (hvL_even : ∀ x, vL (τ x) = vL x)
    (htop_even : E.ColumnFlipEven τ top)
    (hparity : E.ColumnFlipParity τ) :
    ∀ i l,
      E.boundaryCoordinates vL i * E.markedMatrix f i top *
        E.markedMatrix f top l * E.boundaryCoordinates vR l = 0 := by
  intro i l
  have hleft :
      E.boundaryCoordinates vL i * E.markedMatrix f i top = 0 := by
    rcases hparity i with hi_even | hi_odd
    · have hmarked :
          E.markedMatrix f i top = 0 :=
        E.markedMatrix_zero_of_equiv_odd_even_even f i top τ
          hf_odd hi_even htop_even
      simp [hmarked]
    · have hboundary :
          E.boundaryCoordinates vL i = 0 :=
        E.boundaryCoordinates_zero_of_equiv_even_odd vL i τ hvL_even hi_odd
      simp [hboundary]
  calc
    E.boundaryCoordinates vL i * E.markedMatrix f i top *
        E.markedMatrix f top l * E.boundaryCoordinates vR l
        = (E.boundaryCoordinates vL i * E.markedMatrix f i top) *
            (E.markedMatrix f top l * E.boundaryCoordinates vR l) := by
          ring
    _ = 0 := by simp [hleft]

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

/-- Boundary-vector product of two marked insertions in a fixed diagonal
spectral basis. -/
theorem boundary_marked_diagonal_pow_eq_sum
    (G : Matrix Ω Ω ℝ) (lam vL vR : Ω → ℝ)
    (left sep right : ℕ) :
    (∑ a, ∑ b,
      vL a * (Matrix.diagonal (fun i => lam i ^ left) * G *
        Matrix.diagonal (fun i => lam i ^ sep) * G *
        Matrix.diagonal (fun i => lam i ^ right)) a b * vR b)
      = ∑ i, ∑ j, ∑ l,
          vL i * lam i ^ left * G i j * lam j ^ sep *
          G j l * lam l ^ right * vR l := by
  apply Finset.sum_congr rfl
  intro i _
  calc
    ∑ b,
        vL i * (Matrix.diagonal (fun i => lam i ^ left) * G *
          Matrix.diagonal (fun i => lam i ^ sep) * G *
          Matrix.diagonal (fun i => lam i ^ right)) i b * vR b
        = ∑ l, ∑ j,
            vL i * lam i ^ left * G i j * lam j ^ sep *
            G j l * lam l ^ right * vR l := by
          apply Finset.sum_congr rfl
          intro l _
          rw [Matrix.mul_diagonal]
          rw [Matrix.mul_apply]
          rw [Finset.sum_mul]
          rw [Finset.mul_sum]
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _
          rw [Matrix.mul_diagonal]
          rw [Matrix.diagonal_mul]
          ring
    _ = ∑ j, ∑ l,
            vL i * lam i ^ left * G i j * lam j ^ sep *
            G j l * lam l ^ right * vR l := by
          rw [Finset.sum_comm]

/-- A finite boundary-vector marked product written in explicit orthogonal
spectral coordinates. -/
theorem boundaryMarkedProduct_eq_spectralSum {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (vL f vR : Ω → ℝ)
    (left sep right : ℕ) :
    boundaryMarkedProduct M vL f vR left sep right =
      ∑ i, ∑ j, ∑ l,
        E.boundaryCoordinates vL i * E.eigenvalue i ^ left *
        E.markedMatrix f i j * E.eigenvalue j ^ sep *
        E.markedMatrix f j l * E.eigenvalue l ^ right *
        E.boundaryCoordinates vR l := by
  let Dleft : Matrix Ω Ω ℝ := Matrix.diagonal fun i => E.eigenvalue i ^ left
  let Dsep : Matrix Ω Ω ℝ := Matrix.diagonal fun i => E.eigenvalue i ^ sep
  let Dright : Matrix Ω Ω ℝ := Matrix.diagonal fun i => E.eigenvalue i ^ right
  let G : Matrix Ω Ω ℝ := E.markedMatrix f
  let B : Matrix Ω Ω ℝ := Dleft * G * Dsep * G * Dright
  have hmat :
      M ^ left * Matrix.diagonal f * M ^ sep * Matrix.diagonal f * M ^ right =
        E.changeOfBasis * B * E.changeOfBasisᵀ := by
    dsimp [B, Dleft, Dsep, Dright, G]
    rw [E.pow_eq left, E.pow_eq sep, E.pow_eq right]
    unfold markedMatrix
    noncomm_ring [E.orthogonal_left]
  rw [boundaryMarkedProduct_eq_dotProduct]
  rw [hmat]
  rw [dotProduct_mulVec]
  rw [← vecMul_vecMul vL (E.changeOfBasis * B) E.changeOfBasisᵀ]
  rw [← vecMul_vecMul vL E.changeOfBasis B]
  rw [← dotProduct_mulVec]
  have hleft :
      vL ᵥ* E.changeOfBasis = E.boundaryCoordinates vL := by
    ext i
    simp [vecMul, dotProduct, boundaryCoordinates]
  have hright :
      E.changeOfBasisᵀ *ᵥ vR = E.boundaryCoordinates vR := by
    ext i
    simp only [mulVec, dotProduct, Matrix.transpose_apply, boundaryCoordinates]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hleft, hright]
  dsimp [B, Dleft, Dsep, Dright, G]
  rw [← boundary_marked_diagonal_pow_eq_sum (E.markedMatrix f) E.eigenvalue
    (E.boundaryCoordinates vL) (E.boundaryCoordinates vR) left sep right]
  simp only [dotProduct, vecMul]
  calc
    ∑ x,
        (∑ x_1,
          E.boundaryCoordinates vL x_1 *
            ((Matrix.diagonal (fun i => E.eigenvalue i ^ left) * E.markedMatrix f *
              Matrix.diagonal (fun i => E.eigenvalue i ^ sep) * E.markedMatrix f *
              Matrix.diagonal (fun i => E.eigenvalue i ^ right)) x_1 x)) *
          E.boundaryCoordinates vR x
        = ∑ x, ∑ x_1,
            E.boundaryCoordinates vL x_1 *
              ((Matrix.diagonal (fun i => E.eigenvalue i ^ left) * E.markedMatrix f *
                Matrix.diagonal (fun i => E.eigenvalue i ^ sep) * E.markedMatrix f *
                Matrix.diagonal (fun i => E.eigenvalue i ^ right)) x_1 x) *
              E.boundaryCoordinates vR x := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.sum_mul]
    _ = ∑ x_1, ∑ x,
            E.boundaryCoordinates vL x_1 *
              ((Matrix.diagonal (fun i => E.eigenvalue i ^ left) * E.markedMatrix f *
                Matrix.diagonal (fun i => E.eigenvalue i ^ sep) * E.markedMatrix f *
                Matrix.diagonal (fun i => E.eigenvalue i ^ right)) x_1 x) *
              E.boundaryCoordinates vR x := by
          rw [Finset.sum_comm]

/-- A finite boundary-vector power product `vLᵀ M^n vR`. -/
noncomputable def boundaryPowerProduct
    (M : Matrix Ω Ω ℝ) (vL vR : Ω → ℝ) (n : ℕ) : ℝ :=
  boundaryMarkedProduct M vL (fun _ => (1 : ℝ)) vR n 0 0

/-- The boundary-vector power product in explicit orthogonal spectral
coordinates. -/
theorem boundaryPowerProduct_eq_spectralSum {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (vL vR : Ω → ℝ) (n : ℕ) :
    boundaryPowerProduct M vL vR n =
      ∑ i, E.boundaryCoordinates vL i * E.eigenvalue i ^ n *
        E.boundaryCoordinates vR i := by
  rw [boundaryPowerProduct, E.boundaryMarkedProduct_eq_spectralSum]
  simp [Matrix.one_apply, mul_assoc]

/-- The finite open-boundary spectral denominator prefactor attached to a
boundary vector and a chosen dominant channel. -/
noncomputable def boundarySpectralPartitionPrefactor {M : Matrix Ω Ω ℝ}
  (E : RealOrthogonalSpectralData M) (v : Ω → ℝ) (top : Ω) (theta : ℝ) : ℝ :=
  (E.boundaryCoordinates v top) ^ 2 -
    (∑ i ∈ Finset.univ.erase top, (E.boundaryCoordinates v i) ^ 2) * theta

/-- Boundary-vector spectral dominance gives a lower bound for a finite
boundary-power denominator. -/
theorem boundary_partition_lower_of_dominant_bounds {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (v : Ω → ℝ)
    (top : Ω) (scale theta : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_le_one : theta ≤ 1)
    (dominant_eigenvalue : E.eigenvalue top = scale)
    (subdominant_abs_le : ∀ i, i ≠ top → |E.eigenvalue i| ≤ theta * scale)
    (n : ℕ) :
    E.boundarySpectralPartitionPrefactor v top theta * scale ^ n ≤
      ∑ i, (E.boundaryCoordinates v i) ^ 2 * E.eigenvalue i ^ n := by
  let b : Ω → ℝ := E.boundaryCoordinates v
  let rest : Finset Ω := Finset.univ.erase top
  have hscale_nonneg : 0 ≤ scale := scale_pos.le
  have htheta_scale_nonneg : 0 ≤ theta * scale :=
    mul_nonneg theta_nonneg hscale_nonneg
  have hrest_coeff_nonneg :
      0 ≤ ∑ i ∈ rest, b i ^ 2 := by
    exact Finset.sum_nonneg fun i _ => sq_nonneg (b i)
  by_cases hn : n = 0
  · subst n
    have hpref_le_top :
        E.boundarySpectralPartitionPrefactor v top theta ≤ b top ^ 2 := by
      dsimp [boundarySpectralPartitionPrefactor, b, rest]
      exact sub_le_self _ (mul_nonneg hrest_coeff_nonneg theta_nonneg)
    have htop_le_sum :
        b top ^ 2 ≤ ∑ i, b i ^ 2 := by
      exact Finset.single_le_sum
        (fun i _ => sq_nonneg (b i)) (Finset.mem_univ top)
    calc
      E.boundarySpectralPartitionPrefactor v top theta * scale ^ 0
          = E.boundarySpectralPartitionPrefactor v top theta := by simp
      _ ≤ b top ^ 2 := hpref_le_top
      _ ≤ ∑ i, b i ^ 2 := htop_le_sum
      _ = ∑ i, b i ^ 2 * E.eigenvalue i ^ 0 := by simp
  · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    have htheta_pow_le : theta ^ n ≤ theta := by
      simpa using pow_le_pow_of_le_one theta_nonneg theta_le_one hn_pos
    have hscale_pow_nonneg : 0 ≤ scale ^ n := pow_nonneg hscale_nonneg n
    have hrest_term :
        ∀ i ∈ rest,
          -(b i ^ 2 * (theta * scale) ^ n) ≤ b i ^ 2 * E.eigenvalue i ^ n := by
      intro i hi
      have hitop : i ≠ top := (Finset.mem_erase.mp hi).1
      have hpow_abs : |E.eigenvalue i ^ n| ≤ (theta * scale) ^ n := by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (subdominant_abs_le i hitop) n
      have hneg := neg_le_of_abs_le hpow_abs
      simpa [mul_assoc] using
        mul_le_mul_of_nonneg_left hneg (sq_nonneg (b i))
    have hrest_sum :
        ∑ i ∈ rest, -(b i ^ 2 * (theta * scale) ^ n)
          ≤ ∑ i ∈ rest, b i ^ 2 * E.eigenvalue i ^ n :=
      Finset.sum_le_sum hrest_term
    have hrest_sum' :
        -((∑ i ∈ rest, b i ^ 2) * (theta * scale) ^ n)
          ≤ ∑ i ∈ rest, b i ^ 2 * E.eigenvalue i ^ n := by
      simpa [Finset.sum_neg_distrib, Finset.sum_mul, mul_assoc] using hrest_sum
    have hrest_pow_le :
        (∑ i ∈ rest, b i ^ 2) * (theta * scale) ^ n
          ≤ (∑ i ∈ rest, b i ^ 2) * theta * scale ^ n := by
      rw [mul_pow]
      calc
        (∑ i ∈ rest, b i ^ 2) * (theta ^ n * scale ^ n)
            ≤ (∑ i ∈ rest, b i ^ 2) * (theta * scale ^ n) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right htheta_pow_le hscale_pow_nonneg)
                hrest_coeff_nonneg
        _ = (∑ i ∈ rest, b i ^ 2) * theta * scale ^ n := by ring
    have htop_rest_lower :
        b top ^ 2 * scale ^ n -
            (∑ i ∈ rest, b i ^ 2) * (theta * scale) ^ n
          ≤ b top ^ 2 * scale ^ n +
              ∑ i ∈ rest, b i ^ 2 * E.eigenvalue i ^ n := by
      linarith
    have hpref_le :
        E.boundarySpectralPartitionPrefactor v top theta * scale ^ n
          ≤ b top ^ 2 * scale ^ n -
              (∑ i ∈ rest, b i ^ 2) * (theta * scale) ^ n := by
      dsimp [boundarySpectralPartitionPrefactor, b, rest]
      nlinarith
    calc
      E.boundarySpectralPartitionPrefactor v top theta * scale ^ n
          ≤ b top ^ 2 * scale ^ n -
              (∑ i ∈ rest, b i ^ 2) * (theta * scale) ^ n := hpref_le
      _ ≤ b top ^ 2 * scale ^ n +
              ∑ i ∈ rest, b i ^ 2 * E.eigenvalue i ^ n := htop_rest_lower
      _ = (∑ i ∈ rest, b i ^ 2 * E.eigenvalue i ^ n) +
              b top ^ 2 * scale ^ n := by ring
      _ = ∑ i, b i ^ 2 * E.eigenvalue i ^ n := by
        rw [← Finset.sum_erase_add (Finset.univ)
          (fun i => b i ^ 2 * E.eigenvalue i ^ n) (Finset.mem_univ top)]
        simp [rest, dominant_eigenvalue]

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

/-- A top-supported pair of boundary vectors and a zero dominant marked diagonal
give the central-channel cancellation needed for open boundary-vector marked
products. -/
theorem boundaryMarkedCentral_zero_of_topBoundary {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (f vL vR : Ω → ℝ) (top : Ω)
    (hL : ∀ i, i ≠ top → E.boundaryCoordinates vL i = 0)
    (hR : ∀ i, i ≠ top → E.boundaryCoordinates vR i = 0)
    (hG : E.markedMatrix f top top = 0) :
    ∀ i l,
      E.boundaryCoordinates vL i * E.markedMatrix f i top *
        E.markedMatrix f top l * E.boundaryCoordinates vR l = 0 := by
  intro i l
  by_cases hi : i = top
  · subst i
    by_cases hl : l = top
    · subst l
      simp [hG]
    · simp [hR l hl]
  · simp [hL i hi]

/-- Spectral dominance and central-channel cancellation give an open
boundary-vector marked numerator bound in the separation exponent. -/
theorem boundaryMarkedSpectralSum_abs_le_spectralPrefactor {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (f vL vR : Ω → ℝ)
    (top : Ω) (scale theta : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (eigenvalue_abs_le_scale : ∀ i, |E.eigenvalue i| ≤ scale)
    (subdominant_abs_le : ∀ i, i ≠ top → |E.eigenvalue i| ≤ theta * scale)
    (central_dominant_channel_zero : ∀ i l,
      E.boundaryCoordinates vL i * E.markedMatrix f i top *
        E.markedMatrix f top l * E.boundaryCoordinates vR l = 0)
    (left sep right : ℕ) :
    |∑ i, ∑ j, ∑ l,
        E.boundaryCoordinates vL i * E.eigenvalue i ^ left *
        E.markedMatrix f i j * E.eigenvalue j ^ sep *
        E.markedMatrix f j l * E.eigenvalue l ^ right *
        E.boundaryCoordinates vR l|
      ≤ E.boundaryMarkedSpectralPrefactor f vL vR *
          scale ^ (left + sep + right) * theta ^ sep := by
  let coeff : Ω → Ω → Ω → ℝ :=
    fun i j l =>
      E.boundaryCoordinates vL i * E.markedMatrix f i j *
        E.markedMatrix f j l * E.boundaryCoordinates vR l
  let term : Ω → Ω → Ω → ℝ :=
    fun i j l =>
      coeff i j l * E.eigenvalue i ^ left * E.eigenvalue j ^ sep *
        E.eigenvalue l ^ right
  have hscale_nonneg : 0 ≤ scale := scale_pos.le
  have htheta_scale_nonneg : 0 ≤ theta * scale :=
    mul_nonneg theta_nonneg hscale_nonneg
  have hsum :
      |∑ i, ∑ j, ∑ l, term i j l| ≤ ∑ i, ∑ j, ∑ l, |term i j l| := by
    calc
      |∑ i, ∑ j, ∑ l, term i j l|
          ≤ ∑ i, |∑ j, ∑ l, term i j l| :=
            Finset.abs_sum_le_sum_abs (fun i => ∑ j, ∑ l, term i j l) Finset.univ
      _ ≤ ∑ i, ∑ j, |∑ l, term i j l| := by
            exact Finset.sum_le_sum fun i _ =>
              Finset.abs_sum_le_sum_abs (fun j => ∑ l, term i j l) Finset.univ
      _ ≤ ∑ i, ∑ j, ∑ l, |term i j l| := by
            exact Finset.sum_le_sum fun i _ =>
              Finset.sum_le_sum fun j _ =>
                Finset.abs_sum_le_sum_abs (fun l => term i j l) Finset.univ
  have hterm : ∀ i j l, |term i j l| ≤
      |coeff i j l| * (scale ^ (left + sep + right) * theta ^ sep) := by
    intro i j l
    by_cases hj : j = top
    · subst j
      have hcoeff : coeff i top l = 0 := central_dominant_channel_zero i l
      simp [term, hcoeff]
    · have hipow : |E.eigenvalue i| ^ left ≤ scale ^ left :=
        pow_le_pow_left₀ (abs_nonneg _) (eigenvalue_abs_le_scale i) left
      have hjpow : |E.eigenvalue j| ^ sep ≤ (theta * scale) ^ sep :=
        pow_le_pow_left₀ (abs_nonneg _) (subdominant_abs_le j hj) sep
      have hlpow : |E.eigenvalue l| ^ right ≤ scale ^ right :=
        pow_le_pow_left₀ (abs_nonneg _) (eigenvalue_abs_le_scale l) right
      have hpow_mul :
          |E.eigenvalue i| ^ left * |E.eigenvalue j| ^ sep *
              |E.eigenvalue l| ^ right
            ≤ scale ^ left * (theta * scale) ^ sep * scale ^ right := by
        exact mul_le_mul
          (mul_le_mul hipow hjpow (pow_nonneg (abs_nonneg _) sep)
            (pow_nonneg hscale_nonneg left))
          hlpow (pow_nonneg (abs_nonneg _) right)
          (mul_nonneg (pow_nonneg hscale_nonneg left)
            (pow_nonneg htheta_scale_nonneg sep))
      have hpow_eq :
          scale ^ left * (theta * scale) ^ sep * scale ^ right =
            scale ^ (left + sep + right) * theta ^ sep := by
        rw [mul_pow, pow_add, pow_add]
        ring
      calc
        |term i j l|
            = |coeff i j l| *
                (|E.eigenvalue i| ^ left * |E.eigenvalue j| ^ sep *
                  |E.eigenvalue l| ^ right) := by
              simp [term, abs_mul, abs_pow, mul_assoc]
        _ ≤ |coeff i j l| *
              (scale ^ left * (theta * scale) ^ sep * scale ^ right) :=
                mul_le_mul_of_nonneg_left hpow_mul (abs_nonneg _)
        _ = |coeff i j l| * (scale ^ (left + sep + right) * theta ^ sep) := by
              rw [hpow_eq]
  calc
    |∑ i, ∑ j, ∑ l,
        E.boundaryCoordinates vL i * E.eigenvalue i ^ left *
        E.markedMatrix f i j * E.eigenvalue j ^ sep *
        E.markedMatrix f j l * E.eigenvalue l ^ right *
        E.boundaryCoordinates vR l|
        = |∑ i, ∑ j, ∑ l, term i j l| := by
            congr 1
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            apply Finset.sum_congr rfl
            intro l _
            simp [term, coeff]
            ring
    _ ≤ ∑ i, ∑ j, ∑ l, |term i j l| := hsum
    _ ≤ ∑ i, ∑ j, ∑ l,
          |coeff i j l| * (scale ^ (left + sep + right) * theta ^ sep) := by
            exact Finset.sum_le_sum fun i _ =>
              Finset.sum_le_sum fun j _ =>
                Finset.sum_le_sum fun l _ => hterm i j l
    _ = E.boundaryMarkedSpectralPrefactor f vL vR *
          scale ^ (left + sep + right) * theta ^ sep := by
            simp [boundaryMarkedSpectralPrefactor, coeff, Finset.sum_mul, mul_assoc]

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

/-- Spin-observable constructor for a balanced min-separation spectral-gap
certificate from explicit orthogonal spectral data.  It replaces the
dominant-diagonal marked-channel cancellation hypothesis by flip-evenness of
the chosen dominant spectral column. -/
noncomputable def
    layerBalancedMinSpectralGapCertificate_of_orthogonalDominantBounds_flipEvenSpin
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (top : LayerState S) (scale theta : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (partitionPrefactor_small :
      (((Fintype.card (LayerState S) - 1 : ℕ) : ℝ) * theta) < 1)
    (dominant_eigenvalue : E.eigenvalue top = scale)
    (subdominant_abs_le : ∀ i, i ≠ top → |E.eigenvalue i| ≤ theta * scale)
    (dominant_vector_flip_even : ∀ ω : LayerState S,
      E.changeOfBasis (layerStateFlipEquiv S ω) top = E.changeOfBasis ω top) :
    LayerBalancedMinSpectralGapCertificate u k (layerSpinAt x) :=
  layerBalancedMinSpectralGapCertificate_of_orthogonalDominantBounds
    u k (layerSpinAt x) E top scale theta scale_pos theta_nonneg theta_lt_one
    partitionPrefactor_small dominant_eigenvalue subdominant_abs_le
    (E.markedMatrix_layerSpinAt_diagonal_zero_of_flip_even x top
      dominant_vector_flip_even)

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

/-- Spin-observable constructor for a balanced min-separation spectral-gap
certificate using the Hermitian spectral theorem data attached to the balanced
transfer matrix.  The marked-channel cancellation is supplied by flip-evenness
of the chosen dominant spectral column. -/
noncomputable def
    layerBalancedMinSpectralGapCertificate_of_layerHermitianDominantBounds_flipEvenSpin
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hk : ∀ a b, k a b = k b a)
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
    (dominant_vector_flip_even : ∀ ω : LayerState S,
      (layerSymmetricTransferOrthogonalSpectralData u k hk).changeOfBasis
          (layerStateFlipEquiv S ω) top =
        (layerSymmetricTransferOrthogonalSpectralData u k hk).changeOfBasis
          ω top) :
    LayerBalancedMinSpectralGapCertificate u k (layerSpinAt x) :=
  layerBalancedMinSpectralGapCertificate_of_orthogonalDominantBounds_flipEvenSpin
    u k x (layerSymmetricTransferOrthogonalSpectralData u k hk) top scale theta
    scale_pos theta_nonneg theta_lt_one partitionPrefactor_small
    dominant_eigenvalue subdominant_abs_le dominant_vector_flip_even

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

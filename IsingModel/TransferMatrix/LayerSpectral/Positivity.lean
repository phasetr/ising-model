import IsingModel.TransferMatrix.LayerGibbs
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.Tactic.NoncommRing

/-!
# Entrywise positivity vocabulary (GJ §17.1)

Basic entrywise nonnegativity / positivity predicates for finite real matrices
and vectors, together with primitivity/irreducibility and strict-positive
eigenpair consequences.  Part of the `LayerSpectral` finite spectral scaffold.

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


end TransferMatrix

end IsingModel

import IsingModel.TransferMatrix.LayerSpectral.Conjugation

/-!
# Balanced layer transfer matrix (GJ §17.1)

The diagonally balanced (symmetric-when-`k`-symmetric) layer transfer matrix
`S a b = sqrt (u a) * k a b * sqrt (u b)`, its diagonal similarity to the
layer transfer matrix, and the induced positivity, primitivity and Hermitian
structure.  Part of the `LayerSpectral` finite spectral scaffold.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.1, pp. 304--306.
-/

namespace IsingModel

namespace TransferMatrix

open Matrix

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

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


end TransferMatrix

end IsingModel

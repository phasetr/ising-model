import IsingModel.TransferMatrix.LayerSpectral.HermitianBridge

/-!
# Flip-parity spectral-sum expansions (GJ §17.1)

Spectral-sum expansions of matrix powers, marked traces, and boundary-vector
marked/power products in explicit orthogonal spectral coordinates.  Child module
of the `LayerSpectral.FlipParity` scaffold.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.1, pp. 304--306.
-/

namespace IsingModel

namespace TransferMatrix

open Matrix

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

namespace RealOrthogonalSpectralData

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

end RealOrthogonalSpectralData

end TransferMatrix

end IsingModel

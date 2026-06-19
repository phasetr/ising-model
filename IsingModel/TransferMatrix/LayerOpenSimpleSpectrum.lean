import IsingModel.TransferMatrix.LayerOpenParitySimple

/-!
# Simple spectrum implies columnwise simple eigenspaces

This file records a finite linear-algebra bridge for the open-boundary
transfer-matrix route.  If explicit real orthogonal spectral data has an
injective eigenvalue function (a simple spectrum), then each selected spectral
column spans its eigenspace, i.e. the `ColumnSimpleEigenspaces` condition holds.
Consequently the existing flip-parity consumers can take the more elementary,
checkable simple-spectrum hypothesis instead of a direct
`ColumnSimpleEigenspaces` hypothesis.

The results are finite and conditional.  They do not prove a physical
norm-window inequality, that Hermitian spectral-theorem data varies
continuously, that an interacting cubic-layer family has a simple spectrum, an
interacting spectral window, a thermodynamic limit, or final hyperplane
exponential decay.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

open Matrix

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

namespace RealOrthogonalSpectralData

/-! ## Simple spectrum -/

/-- Explicit real orthogonal spectral data has a *simple spectrum* when its
eigenvalue function is injective, i.e. all eigenvalues are distinct. -/
def SimpleSpectrum {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M) : Prop :=
  Function.Injective E.eigenvalue

/-- A simple spectrum implies columnwise simple eigenspaces.  Expanding an
eigenvector in the orthogonal spectral basis, the eigenvector equation forces
every spectral coordinate whose eigenvalue differs from the selected column's
eigenvalue to vanish.  Injectivity of the eigenvalue function then leaves only
the selected column, so it spans its eigenspace. -/
theorem columnSimpleEigenspaces_of_simpleSpectrum {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (hsimple : E.SimpleSpectrum) :
    E.ColumnSimpleEigenspaces := by
  classical
  intro i w hw
  set c : Ω → ℝ := E.changeOfBasisᵀ.mulVec w with hc_def
  -- Diagonalize the action of `M` on `w` through the spectral coordinates `c`.
  have hMw : M.mulVec w
      = E.changeOfBasis.mulVec ((Matrix.diagonal E.eigenvalue).mulVec c) := by
    have h1 : M.mulVec w
        = (E.changeOfBasis * Matrix.diagonal E.eigenvalue
            * E.changeOfBasisᵀ).mulVec w :=
      congrArg (fun A => A.mulVec w) E.diagonalizes
    rw [h1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hc_def]
  -- The spectral coordinates `c` satisfy the diagonal eigenvalue equation.
  have hDiag : (Matrix.diagonal E.eigenvalue).mulVec c = E.eigenvalue i • c := by
    have h2 : E.changeOfBasisᵀ.mulVec
          (E.changeOfBasis.mulVec ((Matrix.diagonal E.eigenvalue).mulVec c))
        = E.changeOfBasisᵀ.mulVec (E.eigenvalue i • w) := by
      rw [← hMw, hw]
    rwa [Matrix.mulVec_mulVec, E.orthogonal_left, Matrix.one_mulVec,
      Matrix.mulVec_smul, ← hc_def] at h2
  -- Off-diagonal spectral coordinates vanish by injectivity of the eigenvalues.
  have hzero : ∀ j, j ≠ i → c j = 0 := by
    intro j hj
    have hcoord := congr_fun hDiag j
    rw [Matrix.mulVec_diagonal] at hcoord
    simp only [Pi.smul_apply, smul_eq_mul] at hcoord
    have hne : E.eigenvalue j ≠ E.eigenvalue i := fun h => hj (hsimple h)
    have hfac : (E.eigenvalue j - E.eigenvalue i) * c j = 0 := by
      rw [sub_mul, hcoord, sub_self]
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd (sub_eq_zero.mp h) hne
    · exact h
  -- Reconstruct `w` as the selected column scaled by its spectral coordinate.
  refine ⟨c i, ?_⟩
  have hrecon : w = E.changeOfBasis.mulVec c := by
    rw [hc_def, Matrix.mulVec_mulVec, E.orthogonal_right, Matrix.one_mulVec]
  funext x
  rw [hrecon, Pi.smul_apply, smul_eq_mul]
  rw [show (E.changeOfBasis.mulVec c) x = ∑ j, E.changeOfBasis x j * c j from rfl]
  rw [Finset.sum_eq_single i]
  · rw [mul_comm]
  · intro j _ hj
    rw [hzero j hj, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- A simple spectrum together with a commuting involution gives a
flip-parity-adapted spectral basis. -/
theorem columnFlipParity_of_commuting_involution_simpleSpectrum {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (τ : Ω ≃ Ω)
    (hτ : ∀ x, τ (τ x) = x)
    (hcomm : ∀ w : Ω → ℝ, M.mulVec (w ∘ τ) = M.mulVec w ∘ τ)
    (hsimple : E.SimpleSpectrum) :
    E.ColumnFlipParity τ :=
  E.columnFlipParity_of_commuting_involution_columnSimple τ hτ hcomm
    (E.columnSimpleEigenspaces_of_simpleSpectrum hsimple)

end RealOrthogonalSpectralData

/-! ## Layer specialization -/

/-- For a balanced layer transfer matrix, zero-field flip invariance plus a
simple spectrum gives a flip-parity-adapted spectral basis. -/
theorem layerSymmetricTransfer_columnFlipParity_of_simpleSpectrum
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (hsimple : E.SimpleSpectrum) :
    E.ColumnFlipParity (layerStateFlipEquiv S) :=
  layerSymmetricTransfer_columnFlipParity_of_columnSimple u k hu_flip hk_flip E
    (E.columnSimpleEigenspaces_of_simpleSpectrum hsimple)

end TransferMatrix

end IsingModel

import IsingModel.TransferMatrix.LayerTopDeflationRowIdentity

/-!
# Perron eigenvector flatness from a uniform entry-ratio bound (GJ §17.1, P5)

The remaining core of the transverse-volume-uniform spectral gap is a **flatness** bound on the
Perron column `w`: that `w_i / w_j` is bounded uniformly. This file proves the abstract mechanism:
for a positive eigenvector `v` (`M v = λ v`, `v > 0`, `λ > 0`), a uniform row entry-ratio bound
`M_ik ≤ ρ·M_jk` forces `v_i ≤ ρ·v_j`. Indeed `λ v_i = ∑_k M_ik v_k ≤ ρ ∑_k M_jk v_k = ρ λ v_j`.

* `eigenvector_ratio_le_of_entry_ratio` — the abstract flatness mechanism.
* `RealOrthogonalSpectralData.signedColumn_mulVec_eq` — the signed Perron column is an eigenvector.
* `signedColumn_ratio_le_of_entry_ratio` — Perron-column flatness from the entry ratio.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §17.1.
-/

namespace IsingModel

namespace TransferMatrix

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- **Eigenvector flatness from a uniform entry-ratio bound**: for a strictly positive eigenvector
`v` of `M` with positive eigenvalue `λ`, a uniform row entry-ratio bound `M_ik ≤ ρ·M_jk` forces
`v_i ≤ ρ·v_j`. This is the abstract mechanism behind a volume-uniform Perron flatness bound:
`λ v_i = ∑_k M_ik v_k ≤ ρ ∑_k M_jk v_k = ρ λ v_j`. -/
theorem eigenvector_ratio_le_of_entry_ratio {M : Matrix Ω Ω ℝ} {v : Ω → ℝ} {lam rho : ℝ}
    (hlam : 0 < lam) (hv_pos : ∀ x, 0 < v x) (hv_eig : M.mulVec v = lam • v)
    (hratio : ∀ i j k, M i k ≤ rho * M j k) (i j : Ω) :
    v i ≤ rho * v j := by
  have hi : (M.mulVec v) i = lam * v i := by rw [hv_eig]; simp [Pi.smul_apply]
  have hj : (M.mulVec v) j = lam * v j := by rw [hv_eig]; simp [Pi.smul_apply]
  have hsum : (M.mulVec v) i ≤ rho * (M.mulVec v) j := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_le_sum (fun k _ => ?_)
    nlinarith [hratio i j k, (hv_pos k).le]
  rw [hi, hj] at hsum
  have h2 : lam * v i ≤ lam * (rho * v j) := by
    have hcomm : rho * (lam * v j) = lam * (rho * v j) := by ring
    linarith [hsum, hcomm]
  exact le_of_mul_le_mul_left h2 hlam

/-- **Perron-column flatness from a uniform entry-ratio bound**: for an entrywise positive matrix,
the signed-positive maximal spectral column `v = sign·(changeOfBasis · maxEigenIndex)` satisfies
`v_i ≤ ρ·v_j` whenever `M_ik ≤ ρ·M_jk` for all `i, j, k`. The signed column is a positive eigenvector
(`mulVec_signedColumn`) with positive eigenvalue (`eigenvalue_pos_maxEigenIndex`), so the abstract
flatness mechanism applies. -/
theorem RealOrthogonalSpectralData.signedColumn_ratio_le_of_entry_ratio [Nonempty Ω]
    {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M) (hM : MatrixEntrywisePositive M)
    {rho : ℝ} (hratio : ∀ i j k, M i k ≤ rho * M j k) (i j : Ω) :
    (E.signedPositiveColumn_maxEigenIndex hM).sign * E.changeOfBasis i E.maxEigenIndex
      ≤ rho * ((E.signedPositiveColumn_maxEigenIndex hM).sign
        * E.changeOfBasis j E.maxEigenIndex) :=
  eigenvector_ratio_le_of_entry_ratio (E.eigenvalue_pos_maxEigenIndex hM)
    (E.signedPositiveColumn_maxEigenIndex hM).positive
    (E.signedPositiveColumn_maxEigenIndex hM).mulVec_signedColumn hratio i j

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- **Perron-column flatness for the balanced layer transfer matrix**: the signed-positive maximal
spectral column of an arbitrary finite layer transfer matrix is flat with ratio `ρ`, given a uniform
entry-ratio bound `M_ik ≤ ρ·M_jk` on `M a b = √(u a)·k a b·√(u b)`. The remaining P5 step is to
exhibit such a `ρ(βJ)` at high temperature, uniform in the transverse box radius. -/
theorem finiteTransverseHermitian_signedColumn_ratio_le_of_entry_ratio [Nonempty (LayerState S)]
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ)
    (hk_symm : ∀ ω η,
      layerTransitionWeight transitionPairs p ω η =
        layerTransitionWeight transitionPairs p η ω)
    {rho : ℝ}
    (hratio : ∀ i j k, layerSymmetricTransferMatrix
        (layerInternalWeight H p) (layerTransitionWeight transitionPairs p) i k
      ≤ rho * layerSymmetricTransferMatrix
        (layerInternalWeight H p) (layerTransitionWeight transitionPairs p) j k)
    (i j : LayerState S) :
    (((finiteTransverseHermitianData H transitionPairs p hk_symm).signedPositiveColumn_maxEigenIndex
        (finiteTransverseHermitian_entrywisePositive H transitionPairs p)).sign
      * (finiteTransverseHermitianData H transitionPairs p hk_symm).changeOfBasis i
          (finiteTransverseHermitianData H transitionPairs p hk_symm).maxEigenIndex)
      ≤ rho * (((finiteTransverseHermitianData H transitionPairs p hk_symm).signedPositiveColumn_maxEigenIndex
          (finiteTransverseHermitian_entrywisePositive H transitionPairs p)).sign
        * (finiteTransverseHermitianData H transitionPairs p hk_symm).changeOfBasis j
            (finiteTransverseHermitianData H transitionPairs p hk_symm).maxEigenIndex) :=
  (finiteTransverseHermitianData H transitionPairs p hk_symm).signedColumn_ratio_le_of_entry_ratio
    (finiteTransverseHermitian_entrywisePositive H transitionPairs p) hratio i j

end TransferMatrix

end IsingModel

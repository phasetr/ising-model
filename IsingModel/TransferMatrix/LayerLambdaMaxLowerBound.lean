import IsingModel.TransferMatrix.LayerQuadraticFormDeflationGap

/-!
# Rayleigh lower bound on the maximal eigenvalue of the layer transfer matrix (GJ §17.1, P5)

The top-deflated Gershgorin spectral gap (`LayerQuadraticFormDeflationGap`) reduces a uniform
subdominant ratio `θ < 1` to `maxAbsDiag(M_def) + offMass(M_def) ≤ θ·λ_max`. The denominator
`λ_max` therefore needs a **lower** bound. This file supplies the Rayleigh lower bound
`λ_max ≥ ⟨v, M v⟩/‖v‖²` (the reverse of the existing Rayleigh upper bound) and the constant-vector
specialization `λ_max ≥ (∑_{a,b} M a b)/|Ω|` — an explicit positive lower bound for the entrywise
positive layer transfer matrix.

* `vectorSqNorm_pos_of_ne_zero` — a nonzero vector has positive squared norm.
* `RealOrthogonalSpectralData.matrixQuadraticForm_div_vectorSqNorm_le_maxEigenIndex` — Rayleigh lower
  bound on `λ_max`.
* `RealOrthogonalSpectralData.sum_entries_div_card_le_maxEigenIndex` — constant-vector specialization.
* `finiteTransverseHermitian_sum_entries_div_card_le_maxEigenIndex` — the layer specialization.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §17.1.
-/

namespace IsingModel

namespace TransferMatrix

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- **A nonzero vector has positive squared norm**: `‖v‖² = ∑ v_i² > 0` whenever some coordinate is
nonzero. The positivity needed to divide the Rayleigh quotient by `‖v‖²`. -/
theorem vectorSqNorm_pos_of_ne_zero {v : Ω → ℝ} (hv : v ≠ 0) : 0 < vectorSqNorm v := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  rw [vectorSqNorm]
  refine Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ i, ?_⟩
  exact pow_pos (abs_pos.mpr (by simpa using hi)) 2 |>.trans_eq (by rw [sq_abs])

namespace RealOrthogonalSpectralData

/-- **Rayleigh lower bound on the maximal eigenvalue**: for any nonzero `v`, the Rayleigh quotient
`⟨v, M v⟩/‖v‖²` is at most `λ_max`. This is the reverse of `matrixQuadraticForm_le_maxEigenIndex`,
giving a *lower* bound `λ_max ≥ ⟨v, M v⟩/‖v‖²` on the maximal eigenvalue from any trial vector. -/
theorem matrixQuadraticForm_div_vectorSqNorm_le_maxEigenIndex [Nonempty Ω] {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) {v : Ω → ℝ} (hv : v ≠ 0) :
    matrixQuadraticForm M v / vectorSqNorm v ≤ E.eigenvalue E.maxEigenIndex := by
  rw [div_le_iff₀ (vectorSqNorm_pos_of_ne_zero hv)]
  exact E.matrixQuadraticForm_le_maxEigenIndex v

/-- **Constant-vector lower bound on the maximal eigenvalue**: evaluating the Rayleigh lower bound at
the constant-one vector gives `λ_max ≥ (∑_{a,b} M a b)/|Ω|` — the average entry sum bounds the
maximal eigenvalue from below. For an entrywise positive matrix this is a positive lower bound. -/
theorem sum_entries_div_card_le_maxEigenIndex [Nonempty Ω] {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) :
    (∑ a, ∑ b, M a b) / (Fintype.card Ω : ℝ) ≤ E.eigenvalue E.maxEigenIndex := by
  have hv : (fun _ : Ω => (1 : ℝ)) ≠ 0 := by
    obtain ⟨i⟩ := (inferInstance : Nonempty Ω)
    exact fun h => one_ne_zero (congr_fun h i)
  have hquad : matrixQuadraticForm M (fun _ : Ω => (1 : ℝ)) = ∑ a, ∑ b, M a b := by
    simp [matrixQuadraticForm]
  have hnorm : vectorSqNorm (fun _ : Ω => (1 : ℝ)) = (Fintype.card Ω : ℝ) := by
    simp [vectorSqNorm]
  have h := E.matrixQuadraticForm_div_vectorSqNorm_le_maxEigenIndex hv
  rwa [hquad, hnorm] at h

end RealOrthogonalSpectralData

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- **Constant-vector lower bound for the balanced layer transfer matrix**: the maximal eigenvalue
of the arbitrary-finite-layer transfer matrix is bounded below by the average of its entries
`√(u a)·k a b·√(u b)`. This is the explicit lower bound on the `λ_max` denominator of the
top-deflated Gershgorin spectral gap. -/
theorem finiteTransverseHermitian_sum_entries_div_card_le_maxEigenIndex [Nonempty S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ)
    (hk_symm : ∀ ω η,
      layerTransitionWeight transitionPairs p ω η =
        layerTransitionWeight transitionPairs p η ω) :
    (∑ a, ∑ b, layerSymmetricTransferMatrix
        (layerInternalWeight H p) (layerTransitionWeight transitionPairs p) a b)
        / (Fintype.card (LayerState S) : ℝ)
      ≤ (finiteTransverseHermitianData H transitionPairs p hk_symm).eigenvalue
          (finiteTransverseHermitianData H transitionPairs p hk_symm).maxEigenIndex :=
  (finiteTransverseHermitianData H transitionPairs p hk_symm).sum_entries_div_card_le_maxEigenIndex

end TransferMatrix

end IsingModel

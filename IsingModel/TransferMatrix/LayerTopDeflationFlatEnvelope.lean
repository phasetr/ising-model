import IsingModel.TransferMatrix.LayerTopDeflationRowIdentity

/-!
# Flatness reduction of the top-deflated Gershgorin envelope (GJ §17.1)

The top-deflated Gershgorin route
(`subdominantAbsRatio_maxEigenIndex_le_of_topDeflatedGershgorin_le`)
bounds the explicit subdominant ratio by `θ` once the **full** Gershgorin envelope of the deflated
matrix — `maxAbsDiag(M_def) + maxOffMass(M_def)` — is at most `θ·λ_top`. This file removes the
diagonal half of that obligation. By the row-cancellation identity `M_def · w = 0`
(`abs_matrixTopDeflation_diag_le_weighted_offDiag`: the deflated diagonal is a Perron-weighted sum
of its own off-diagonal row), the deflated diagonal is controlled by the off-diagonal mass scaled
by the **Perron flatness ratio** `ρ = sup_{i,j} |w_j / w_i|`:
\[
  \mathrm{maxAbsDiag}(M_{\mathrm{def}}) \le ρ\cdot\mathrm{maxOffMass}(M_{\mathrm{def}}),
  \qquad
  \mathrm{envelope}(M_{\mathrm{def}}) \le (1+ρ)\cdot\mathrm{maxOffMass}(M_{\mathrm{def}}).
\]
Hence the whole deflated-Gershgorin hypothesis reduces to an **off-diagonal-mass** bound plus the
Perron flatness ratio:
\[
  \mathrm{maxOffMass}(M_{\mathrm{def}}) \le η\cdot λ_{\mathrm{top}}
  \ \Longrightarrow\
  \texttt{subdominantAbsRatio} \le (1+ρ)\,η .
\]
This isolates the finite algebraic part of the gap problem; the remaining input is the off-diagonal
mass of the deflated matrix together with the flatness ratio `ρ` (which, for the interacting layer,
is the genuinely analytic obstruction — it is not transverse-volume-uniform, cf. GJ §17.1).

* `vectorAbsRatioSup` — the flatness ratio `sup_{i,j} |w_j / w_i|`.
* `abs_div_le_vectorAbsRatioSup` — its defining property.
* `abs_matrixTopDeflation_diag_le_flatness_mul_offDiagAbsRowSum` — per-row diagonal bound.
* `matrixMaxAbsDiag_topDeflation_le_flatness_mul_maxOffDiagAbsRowSum` — the max diagonal bound.
* `topDeflatedGershgorinEnvelope_le_one_add_flatness_mul_maxOffDiagAbsRowSum` — the
  `(1+ρ)·maxOffMass` envelope bound.
* `subdominantAbsRatio_maxEigenIndex_le_of_topDeflatedOffMass_le_flatness` — the off-diagonal-mass
  capstone (all in the `RealOrthogonalSpectralData` namespace).

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §17.1, pp. 304–306.
-/

namespace IsingModel

namespace TransferMatrix

open Matrix

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- **The flatness ratio of a real vector**: `sup_{i,j} |w_j / w_i|`, the maximal entrywise ratio of
`w`. For the Perron column `w` of an entrywise-positive matrix this measures how far `w` is from
constant; it equals `1` exactly when `w` is flat. -/
noncomputable def vectorAbsRatioSup [Nonempty Ω] (w : Ω → ℝ) : ℝ :=
  (Finset.univ : Finset (Ω × Ω)).sup' Finset.univ_nonempty (fun p => |w p.1 / w p.2|)

omit [DecidableEq Ω] in
/-- The flatness ratio is nonnegative. -/
theorem vectorAbsRatioSup_nonneg [Nonempty Ω] (w : Ω → ℝ) : 0 ≤ vectorAbsRatioSup w := by
  obtain ⟨i⟩ := ‹Nonempty Ω›
  exact le_trans (abs_nonneg _)
    (Finset.le_sup' (fun p : Ω × Ω => |w p.1 / w p.2|) (Finset.mem_univ (i, i)))

omit [DecidableEq Ω] in
/-- **The defining property of the flatness ratio**: every entrywise ratio `|w_j / w_i|` is at most
`vectorAbsRatioSup w`. -/
theorem abs_div_le_vectorAbsRatioSup [Nonempty Ω] (w : Ω → ℝ) (i j : Ω) :
    |w j / w i| ≤ vectorAbsRatioSup w :=
  Finset.le_sup' (fun p : Ω × Ω => |w p.1 / w p.2|) (Finset.mem_univ (j, i))

namespace RealOrthogonalSpectralData

/-- **Flatness bound on the deflated diagonal (per row)**: by the row-cancellation identity the
deflated diagonal `|M_def_ii|` is at most the Perron flatness ratio times the off-diagonal absolute
row sum of the deflated matrix. -/
theorem abs_matrixTopDeflation_diag_le_flatness_mul_offDiagAbsRowSum [Nonempty Ω]
    {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M) (top i : Ω)
    (hi : E.changeOfBasis i top ≠ 0) :
    |E.matrixTopDeflation top i i|
      ≤ vectorAbsRatioSup (fun a => E.changeOfBasis a top)
          * matrixOffDiagAbsRowSum (E.matrixTopDeflation top) i := by
  refine (abs_matrixTopDeflation_diag_le_weighted_offDiag E top i hi).trans ?_
  rw [matrixOffDiagAbsRowSum, Finset.mul_sum]
  refine Finset.sum_le_sum (fun j _ => ?_)
  rw [mul_comm (vectorAbsRatioSup (fun a => E.changeOfBasis a top))
    |E.matrixTopDeflation top i j|]
  exact mul_le_mul_of_nonneg_left
    (abs_div_le_vectorAbsRatioSup (fun a => E.changeOfBasis a top) i j) (abs_nonneg _)

/-- **Flatness bound on the maximal deflated diagonal**: at the Perron (maximal) eigenindex the
maximal deflated diagonal `maxAbsDiag(M_def)` is at most the flatness ratio times the maximal
off-diagonal absolute row sum. -/
theorem matrixMaxAbsDiag_topDeflation_le_flatness_mul_maxOffDiagAbsRowSum [Nonempty Ω]
    {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M) (hM : MatrixEntrywisePositive M) :
    matrixMaxAbsDiag (E.matrixTopDeflation E.maxEigenIndex)
      ≤ vectorAbsRatioSup (fun a => E.changeOfBasis a E.maxEigenIndex)
          * matrixMaxOffDiagAbsRowSum (E.matrixTopDeflation E.maxEigenIndex) := by
  rw [matrixMaxAbsDiag]
  refine Finset.sup'_le _ _ (fun i _ => ?_)
  have hi := changeOfBasis_maxEigenIndex_ne_zero_of_entrywisePositive E hM i
  refine
    (abs_matrixTopDeflation_diag_le_flatness_mul_offDiagAbsRowSum E E.maxEigenIndex i hi).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (vectorAbsRatioSup_nonneg _)
  exact matrixOffDiagAbsRowSum_le_matrixMaxOffDiagAbsRowSum (E.matrixTopDeflation E.maxEigenIndex) i

/-- **Flatness reduction of the deflated Gershgorin envelope**: the full deflated Gershgorin
envelope `maxAbsDiag(M_def) + maxOffMass(M_def)` is at most `(1 + ρ)·maxOffMass(M_def)`, with `ρ`
the Perron flatness ratio. The diagonal half of the envelope is folded into the off-diagonal
mass. -/
theorem topDeflatedGershgorinEnvelope_le_one_add_flatness_mul_maxOffDiagAbsRowSum [Nonempty Ω]
    {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M) (hM : MatrixEntrywisePositive M) :
    matrixMaxAbsDiag (E.matrixTopDeflation E.maxEigenIndex)
        + matrixMaxOffDiagAbsRowSum (E.matrixTopDeflation E.maxEigenIndex)
      ≤ (1 + vectorAbsRatioSup (fun a => E.changeOfBasis a E.maxEigenIndex))
          * matrixMaxOffDiagAbsRowSum (E.matrixTopDeflation E.maxEigenIndex) := by
  have h := matrixMaxAbsDiag_topDeflation_le_flatness_mul_maxOffDiagAbsRowSum E hM
  rw [show (1 + vectorAbsRatioSup (fun a => E.changeOfBasis a E.maxEigenIndex))
        * matrixMaxOffDiagAbsRowSum (E.matrixTopDeflation E.maxEigenIndex)
      = vectorAbsRatioSup (fun a => E.changeOfBasis a E.maxEigenIndex)
          * matrixMaxOffDiagAbsRowSum (E.matrixTopDeflation E.maxEigenIndex)
        + matrixMaxOffDiagAbsRowSum (E.matrixTopDeflation E.maxEigenIndex) from by ring]
  linarith [h]

/-- **Off-diagonal-mass capstone**: if the maximal off-diagonal absolute row sum of the deflated
matrix is at most `η·λ_top`, then the explicit subdominant ratio is at most `(1 + ρ)·η`, with `ρ`
the Perron flatness ratio. The deflated diagonal has been eliminated; only the off-diagonal mass and
the flatness ratio remain as inputs. -/
theorem subdominantAbsRatio_maxEigenIndex_le_of_topDeflatedOffMass_le_flatness [Nonempty Ω]
    {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M) (hM : MatrixEntrywisePositive M)
    (hM_symm : Mᵀ = M) {eta : ℝ} (heta_nonneg : 0 ≤ eta)
    (hoff : matrixMaxOffDiagAbsRowSum (E.matrixTopDeflation E.maxEigenIndex)
        ≤ eta * E.eigenvalue E.maxEigenIndex) :
    E.subdominantAbsRatio_maxEigenIndex hM
      ≤ (1 + vectorAbsRatioSup (fun a => E.changeOfBasis a E.maxEigenIndex)) * eta := by
  have hρ_nonneg : 0 ≤ vectorAbsRatioSup (fun a => E.changeOfBasis a E.maxEigenIndex) :=
    vectorAbsRatioSup_nonneg _
  refine E.subdominantAbsRatio_maxEigenIndex_le_of_topDeflatedGershgorin_le hM hM_symm
    (mul_nonneg (add_nonneg zero_le_one hρ_nonneg) heta_nonneg) ?_
  calc matrixMaxAbsDiag (E.matrixTopDeflation E.maxEigenIndex)
        + matrixMaxOffDiagAbsRowSum (E.matrixTopDeflation E.maxEigenIndex)
      ≤ (1 + vectorAbsRatioSup (fun a => E.changeOfBasis a E.maxEigenIndex))
          * matrixMaxOffDiagAbsRowSum (E.matrixTopDeflation E.maxEigenIndex) :=
        topDeflatedGershgorinEnvelope_le_one_add_flatness_mul_maxOffDiagAbsRowSum E hM
    _ ≤ (1 + vectorAbsRatioSup (fun a => E.changeOfBasis a E.maxEigenIndex))
          * (eta * E.eigenvalue E.maxEigenIndex) :=
        mul_le_mul_of_nonneg_left hoff (add_nonneg zero_le_one hρ_nonneg)
    _ = ((1 + vectorAbsRatioSup (fun a => E.changeOfBasis a E.maxEigenIndex)) * eta)
          * E.eigenvalue E.maxEigenIndex := by ring

end RealOrthogonalSpectralData

end TransferMatrix

end IsingModel

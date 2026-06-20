import IsingModel.TransferMatrix.LayerDoeblin
import IsingModel.TransferMatrix.LayerQuadraticFormGap

/-!
# Subdominant ratio bounded by the Doob Dobrushin coefficient

This file ties the abstract spectral-gap machinery together: the explicit
subdominant absolute ratio of a real orthogonally diagonalized entrywise positive
matrix is bounded by the Dobrushin coefficient of its Doob transform, and is
therefore strictly below one.

The key step is that, for each non-maximal spectral column `v_i`, the
Doob-conjugated vector `v_i / w_top` is nonconstant: were it constant, `v_i` would
be a scalar multiple of the maximal column, contradicting the orthonormality of
the spectral basis (`changeOfBasis_columns_not_smul`).  Feeding this into the
eigenvalue bound of `LayerDobrushinContraction` gives `|λ_i / λ_top| ≤ δ(Doob)`
for every non-maximal eigenvalue, hence `subdominantAbsRatio ≤ δ(Doob)`.  With the
strict Doeblin bound `δ(Doob) < 1` of `LayerDoeblin`, the subdominant ratio is
strictly below one.

This is an alternative, abstract proof of the strict subdominant bound, expressed
through the Dobrushin coefficient `δ(Doob)` — the quantity a later high-temperature
estimate makes uniform in the transverse box size.  The bound here is not uniform.

The results are finite, unconditional estimates.  They do not give a
transverse-volume-uniform gap, prove a thermodynamic limit, or prove final
hyperplane exponential decay.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- A vector of zero oscillation is constant. -/
theorem exists_eq_const_of_vectorOscillation_eq_zero [Nonempty Ω] {v : Ω → ℝ}
    (hv : vectorOscillation v = 0) :
    ∃ c : ℝ, v = fun _ => c := by
  refine ⟨Finset.univ.inf' Finset.univ_nonempty v, ?_⟩
  funext x
  have hsup := Finset.le_sup' v (Finset.mem_univ x)
  have hinf := Finset.inf'_le v (Finset.mem_univ x)
  rw [vectorOscillation, sub_eq_zero] at hv
  linarith

namespace RealOrthogonalSpectralData

/-- For a non-maximal spectral column, the Doob-conjugated vector
`v_i / w_top` is nonconstant: otherwise `v_i` would be a scalar multiple of the
maximal column, contradicting orthonormality. -/
theorem vectorOscillation_div_signedPositiveColumn_ne_zero [Nonempty Ω]
    {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M) {top i : Ω}
    (hpos : E.SignedPositiveColumn top) (hi : i ≠ top) :
    vectorOscillation
        (fun x => E.changeOfBasis x i / (hpos.sign * E.changeOfBasis x top)) ≠ 0 := by
  intro hzero
  obtain ⟨c, hc⟩ := exists_eq_const_of_vectorOscillation_eq_zero hzero
  have hcol : (fun x => E.changeOfBasis x i)
      = c • (fun x => hpos.sign * E.changeOfBasis x top) := by
    funext x
    have hx := congr_fun hc x
    have hne : hpos.sign * E.changeOfBasis x top ≠ 0 := (hpos.positive x).ne'
    rw [div_eq_iff hne] at hx
    simpa [Pi.smul_apply, smul_eq_mul] using hx
  obtain ⟨c', hc'⟩ := hpos.smul_signedColumn_eq_smul_raw hcol
  exact E.changeOfBasis_columns_not_smul hi c' hc'

/-- **The explicit subdominant ratio is bounded by the Doob Dobrushin
coefficient.**  Each non-maximal eigenvalue satisfies `|λ_i / λ_top| ≤ δ(Doob)`,
so the maximal-index subdominant absolute ratio is at most `δ(Doob)`. -/
theorem subdominantAbsRatio_maxEigenIndex_le_dobrushin_doob [Nonempty Ω]
    {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M)
    (hM : MatrixEntrywisePositive M) (hpos : E.SignedPositiveColumn E.maxEigenIndex) :
    E.subdominantAbsRatio_maxEigenIndex hM ≤
      matrixDobrushinCoefficient
        (matrixDoobTransform M (E.eigenvalue E.maxEigenIndex)
          (fun x => hpos.sign * E.changeOfBasis x E.maxEigenIndex)) := by
  have hlam : 0 < E.eigenvalue E.maxEigenIndex := E.eigenvalue_pos_maxEigenIndex hM
  refine E.subdominantAbsRatio_maxEigenIndex_le_of_eigenvalue_abs_le hM
    (matrixDobrushinCoefficient_nonneg _) fun i hi => ?_
  have hbound := abs_eigenvalue_div_le_dobrushin_doob_of_mulVec hM hlam hpos.positive
    hpos.mulVec_signedColumn (E.mulVec_changeOfBasis_column i)
    (E.vectorOscillation_div_signedPositiveColumn_ne_zero hpos hi)
  rw [abs_div, abs_of_pos hlam, div_le_iff₀ hlam] at hbound
  exact hbound

/-- **The explicit subdominant ratio is strictly below one (via the Doob
Dobrushin coefficient).**  An alternative proof of the strict subdominant bound,
through `δ(Doob) < 1`. -/
theorem subdominantAbsRatio_maxEigenIndex_lt_one_via_doob [Nonempty Ω]
    {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M)
    (hM : MatrixEntrywisePositive M) (hpos : E.SignedPositiveColumn E.maxEigenIndex) :
    E.subdominantAbsRatio_maxEigenIndex hM < 1 :=
  lt_of_le_of_lt (E.subdominantAbsRatio_maxEigenIndex_le_dobrushin_doob hM hpos)
    (matrixDobrushinCoefficient_matrixDoobTransform_lt_one hM
      (E.eigenvalue_pos_maxEigenIndex hM) hpos.positive hpos.mulVec_signedColumn)

end RealOrthogonalSpectralData

end TransferMatrix

end IsingModel

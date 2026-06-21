import IsingModel.TransferMatrix.LayerDoeblin

/-!
# Column-oscillation reduction of the Doeblin mass / Dobrushin coefficient (GJ §17.1, P5)

The transverse-volume-uniform spectral gap reduces (via the existing Doob–Dobrushin chain) to a
uniform lower bound on the Doeblin mass `∑_j min_i P_ij` of the Doob transform `P`. A crude per-entry
floor `card·min P_ij` is useless (entries are exponentially small in the layer size). The correct,
volume-uniform handle is **row similarity**: for a row-stochastic `P`,
`DoeblinMass P = 1 − ∑_j (P_ij − min_i P_ij)` for any row `i`, so
`DoeblinMass P ≥ 1 − ∑_j (max_i P_ij − min_i P_ij)`. This file proves that reduction, honestly
turning the uniform Doeblin bound into a per-column **row-variation** (column-oscillation) sum:
`DobrushinCoefficient P ≤ ∑_j (max_i P_ij − min_i P_ij)`.

The remaining P5 core is then the layer-specific estimate that the Doob transform's columns vary
little (rows nearly identical) at high temperature, uniformly in the transverse box radius.

* `matrixColSup` — the column maximum `max_i P_ij`.
* `matrixDoeblinMass_eq_one_sub_row_excess` — the exact row identity for row-stochastic `P`.
* `matrixDoeblinMass_ge_one_sub_sum_colOsc` — the column-oscillation lower bound.
* `matrixDobrushinCoefficient_le_sum_colOsc` — the column-oscillation bound on the Dobrushin coeff.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §17.1.
-/

namespace IsingModel

namespace TransferMatrix

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- **The column maximum** `max_i P_ij` of a finite real matrix. -/
noncomputable def matrixColSup [Nonempty Ω] (P : Matrix Ω Ω ℝ) (j : Ω) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => P i j

/-- **Each entry is at most its column maximum**. -/
theorem le_matrixColSup [Nonempty Ω] (P : Matrix Ω Ω ℝ) (i j : Ω) :
    P i j ≤ matrixColSup P j :=
  Finset.le_sup' (fun i => P i j) (Finset.mem_univ i)

/-- **Exact row identity for the Doeblin mass**: for a row-stochastic matrix, the Doeblin mass equals
`1` minus the excess of any single row over the column minima, since the row sums to `1`. -/
theorem matrixDoeblinMass_eq_one_sub_row_excess [Nonempty Ω] {P : Matrix Ω Ω ℝ}
    (hP : MatrixRowStochastic P) (i : Ω) :
    matrixDoeblinMass P = 1 - ∑ j, (P i j - matrixColMin P j) := by
  rw [matrixDoeblinMass, eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun j _ => by ring : ∀ j ∈ Finset.univ,
    matrixColMin P j + (P i j - matrixColMin P j) = P i j)]
  exact hP.2 i

/-- **Column-oscillation lower bound on the Doeblin mass**: for a row-stochastic matrix, the Doeblin
mass is at least `1` minus the total column oscillation `∑_j (max_i P_ij − min_i P_ij)`. The smaller
the column variation (the more nearly identical the rows), the closer the Doeblin mass is to `1`. -/
theorem matrixDoeblinMass_ge_one_sub_sum_colOsc [Nonempty Ω] {P : Matrix Ω Ω ℝ}
    (hP : MatrixRowStochastic P) :
    1 - ∑ j, (matrixColSup P j - matrixColMin P j) ≤ matrixDoeblinMass P := by
  obtain ⟨i⟩ := (inferInstance : Nonempty Ω)
  rw [matrixDoeblinMass_eq_one_sub_row_excess hP i]
  have hle : ∑ j, (P i j - matrixColMin P j) ≤ ∑ j, (matrixColSup P j - matrixColMin P j) :=
    Finset.sum_le_sum fun j _ => by linarith [le_matrixColSup P i j]
  linarith

/-- **Column-oscillation bound on the Dobrushin coefficient**: for a row-stochastic matrix, the
Dobrushin coefficient is at most the total column oscillation `∑_j (max_i P_ij − min_i P_ij)`. This
reduces a transverse-volume-uniform Dobrushin (hence subdominant-ratio) bound to a per-column
row-variation estimate on the Doob transform. -/
theorem matrixDobrushinCoefficient_le_sum_colOsc [Nonempty Ω] {P : Matrix Ω Ω ℝ}
    (hP : MatrixRowStochastic P) :
    matrixDobrushinCoefficient P ≤ ∑ j, (matrixColSup P j - matrixColMin P j) := by
  have h1 := matrixDobrushinCoefficient_le_one_sub_doeblinMass hP
  have h2 := matrixDoeblinMass_ge_one_sub_sum_colOsc hP
  linarith

end TransferMatrix

end IsingModel

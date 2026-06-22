import IsingModel.Dobrushin.InfluenceMatrixDecay

/-!
# The Dobrushin total influence (Neumann-series resolvent row sums) (GJ §17.1)

At high temperature the Dobrushin coefficient `α = Δ(G)·tanh(βJ)` is `< 1`, so the influence-matrix
powers' row sums `∑_y (C^n)_{xy} ≤ α^n` (`isingInfluenceMatrix_pow_rowSum_le`, #4199) form a
summable geometric majorant. Hence the **total influence** `∑_n ∑_y (C^n)_{xy}` — the row sum of the
Neumann series `∑_n C^n` (formally the resolvent of `I − C`; the matrix identity `(I − C)^{-1} =
∑_n C^n` is not formalized here) — converges and is bounded by `(1 − α)^{-1}`. This row sum is
exactly the coefficient appearing in the Dobrushin comparison theorem
`|⟨f⟩_η − ⟨f⟩_{η'}| ≤ ∑_{x,y} ((I−C)^{-1})_{xy}·osc_x(f)·[η,η' differ at y]` (that comparison
theorem is not formalized here).

* `matrix_summable_pow_rowSum` / `matrix_tsum_pow_rowSum_le` — abstract: for a nonnegative matrix
  with row sums `≤ α` (`0 ≤ α < 1`), the power row sums are summable with `∑_n ≤ (1−α)^{-1}`.
* `isingTotalInfluence` — the total influence `∑_n ∑_y (C^n)_{xy}` at a site `x`.
* `isingInfluenceMatrix_summable_pow_rowSum` / `isingTotalInfluence_le` — the high-temperature
  summability and the `(1 − Δ(G)·tanh(βJ))^{-1}` bound.
* `one_le_isingTotalInfluence` — the resolvent row sum is `≥ 1` (the identity `n = 0` term).

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §17.1, pp. 304–306.
-/

namespace IsingModel

namespace Dobrushin

open Real

/-- **Summability of the matrix-power row sums** (abstract): for a nonnegative matrix `M` with all
row sums `≤ α` and `0 ≤ α < 1`, the row sums of the powers `∑_y (M^n)_{xy}` are summable (dominated
by the geometric series `α^n`). -/
theorem matrix_summable_pow_rowSum {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℝ}
    {α : ℝ} (hM : ∀ x y, 0 ≤ M x y) (hα0 : 0 ≤ α) (hα1 : α < 1) (hrow : ∀ x, ∑ y, M x y ≤ α)
    (x : ι) : Summable (fun n => ∑ y, (M ^ n) x y) :=
  Summable.of_nonneg_of_le
    (fun n => Finset.sum_nonneg fun y _ => Matrix.pow_apply_nonneg hM n x y)
    (fun n => matrix_pow_rowSum_le hM hα0 hrow n x)
    (summable_geometric_of_lt_one hα0 hα1)

/-- **The total matrix-power row sum is at most `(1 − α)^{-1}`** (abstract): summing the geometric
majorant `α^n` gives the Neumann-series bound on the resolvent row sum. -/
theorem matrix_tsum_pow_rowSum_le {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℝ}
    {α : ℝ} (hM : ∀ x y, 0 ≤ M x y) (hα0 : 0 ≤ α) (hα1 : α < 1) (hrow : ∀ x, ∑ y, M x y ≤ α)
    (x : ι) : ∑' n, ∑ y, (M ^ n) x y ≤ (1 - α)⁻¹ := by
  calc ∑' n, ∑ y, (M ^ n) x y
      ≤ ∑' n, α ^ n :=
        Summable.tsum_mono (matrix_summable_pow_rowSum hM hα0 hα1 hrow x)
          (summable_geometric_of_lt_one hα0 hα1)
          (fun n => matrix_pow_rowSum_le hM hα0 hrow n x)
    _ = (1 - α)⁻¹ := tsum_geometric_of_lt_one hα0 hα1

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (G : SimpleGraph ι) [Fintype G.edgeSet] [DecidableRel G.Adj]

/-- **The total Dobrushin influence at a site** `x`: the row sum of the Neumann series `∑_n C^n`,
i.e. `∑_n ∑_y (C^n)_{xy}` (formally the resolvent row sum of `I − C`). The coefficient of the
Dobrushin comparison theorem. -/
noncomputable def isingTotalInfluence (β J : ℝ) (x : ι) : ℝ :=
  ∑' n, ∑ y, ((isingInfluenceMatrix G β J) ^ n) x y

omit [Fintype G.edgeSet] in
/-- **High-temperature summability of the influence-matrix power row sums**: for `0 ≤ βJ` and
`βJ·Δ(G) < 1`, the row sums `∑_y (C^n)_{xy}` are summable. -/
theorem isingInfluenceMatrix_summable_pow_rowSum {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hΔ : β * J * G.maxDegree < 1) (x : ι) :
    Summable (fun n => ∑ y, ((isingInfluenceMatrix G β J) ^ n) x y) :=
  matrix_summable_pow_rowSum (isingInfluenceMatrix_nonneg G hβJ)
    (isingDobrushinCoeff_nonneg G hβJ) (isingDobrushinCoeff_lt_one_of_high_temp G hβJ hΔ)
    (isingInfluenceMatrix_rowSum_le G hβJ) x

omit [Fintype G.edgeSet] in
/-- **The total Dobrushin influence is bounded by `(1 − α)^{-1}`** (GJ §17.1): for `0 ≤ βJ` and
`βJ·Δ(G) < 1`, the resolvent row sum is at most `(1 − Δ(G)·tanh(βJ))^{-1}`. This is the
high-temperature bound on the Dobrushin comparison-theorem coefficient. -/
theorem isingTotalInfluence_le {β J : ℝ} (hβJ : 0 ≤ β * J) (hΔ : β * J * G.maxDegree < 1) (x : ι) :
    isingTotalInfluence G β J x ≤ (1 - isingDobrushinCoeff G β J)⁻¹ :=
  matrix_tsum_pow_rowSum_le (isingInfluenceMatrix_nonneg G hβJ)
    (isingDobrushinCoeff_nonneg G hβJ) (isingDobrushinCoeff_lt_one_of_high_temp G hβJ hΔ)
    (isingInfluenceMatrix_rowSum_le G hβJ) x

omit [Fintype G.edgeSet] in
/-- **The total Dobrushin influence is at least `1`** (GJ §17.1): for `0 ≤ βJ` and `βJ·Δ(G) < 1`,
the resolvent row sum is `≥ 1` — the identity contribution `∑_y (C^0)_{xy} = ∑_y [x = y] = 1` (all
other
terms are nonnegative). -/
theorem one_le_isingTotalInfluence {β J : ℝ} (hβJ : 0 ≤ β * J) (hΔ : β * J * G.maxDegree < 1)
    (x : ι) : 1 ≤ isingTotalInfluence G β J x := by
  have hsummable := isingInfluenceMatrix_summable_pow_rowSum G hβJ hΔ x
  have hzero : ∑ y, ((isingInfluenceMatrix G β J) ^ 0) x y = 1 := by
    simp [pow_zero, Matrix.one_apply]
  calc (1 : ℝ) = ∑ y, ((isingInfluenceMatrix G β J) ^ 0) x y := hzero.symm
    _ ≤ isingTotalInfluence G β J x :=
        Summable.le_tsum hsummable 0 fun n _ =>
          Finset.sum_nonneg fun y _ => Matrix.pow_apply_nonneg (isingInfluenceMatrix_nonneg G hβJ)
            n x y

end Dobrushin

end IsingModel

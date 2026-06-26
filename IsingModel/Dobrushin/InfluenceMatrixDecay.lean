import IsingModel.Dobrushin.DobrushinHighTemp
import IsingModel.RealTanhAux

/-!
# Exponential decay of the Dobrushin influence-matrix powers (GJ §17.1)

The single-site Dobrushin influence matrix `C` (`isingInfluenceMatrix`, with `C_{xy} =
tanh(βJ)·[y∼x]`) has nonnegative entries and every row sum is at most the **Dobrushin coefficient**
`α = Δ(G)·tanh(βJ)` (`isingDobrushinCoeff`). Consequently the `n`-th matrix power has row sums at
most `α^n` — the influence of the boundary on a site decays geometrically with the number of steps.
At high temperature `α < 1`, so the row sums of `C^n` tend to `0`: the analytic seed of the
Dobrushin comparison/uniqueness theorem (which itself is not formalized here).

* `matrix_pow_rowSum_le` — abstract: a nonnegative matrix with row sums `≤ α` (`0 ≤ α`) has
  `∑_y (M^n)_{xy} ≤ α^n`.
* `isingInfluenceMatrix` — the influence matrix `C_{xy} = isingInfluence G β J x y`.
* `isingDobrushinCoeff` — the Dobrushin coefficient `Δ(G)·tanh(βJ)`.
* `isingInfluenceMatrix_pow_rowSum_le` — `∑_y (C^n)_{xy} ≤ (Δ(G)·tanh(βJ))^n` (for `0 ≤ βJ`).
* `isingDobrushinCoeff_lt_one_of_high_temp` — `α < 1` under `βJ·Δ(G) < 1`.
* `isingInfluenceMatrix_pow_rowSum_tendsto_zero` — the row sums of `C^n` tend to `0` at high
  temperature.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §17.1, pp. 304–306.
-/

namespace IsingModel

namespace Dobrushin

open Real

/-- **Geometric decay of matrix-power row sums** (abstract): if `M` has nonnegative entries and
every row sum is at most `α` (`0 ≤ α`), then every row sum of `M^n` is at most `α^n`. Proof by
induction: `∑_z (M^{n+1})_{xz} = ∑_y M_{xy}·(∑_z (M^n)_{yz}) ≤ (∑_y M_{xy})·α^n ≤ α·α^n`. -/
theorem matrix_pow_rowSum_le {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℝ} {α : ℝ}
    (hM : ∀ x y, 0 ≤ M x y) (hα : 0 ≤ α) (hrow : ∀ x, ∑ y, M x y ≤ α) :
    ∀ (n : ℕ) (x : ι), ∑ y, (M ^ n) x y ≤ α ^ n := by
  intro n
  induction n with
  | zero =>
    intro x
    simp [pow_zero, Matrix.one_apply]
  | succ n ih =>
    intro x
    calc ∑ z, (M ^ (n + 1)) x z
        = ∑ z, ∑ y, M x y * (M ^ n) y z := by
          simp_rw [pow_succ', Matrix.mul_apply]
      _ = ∑ y, M x y * ∑ z, (M ^ n) y z := by
          rw [Finset.sum_comm]; simp_rw [Finset.mul_sum]
      _ ≤ ∑ y, M x y * α ^ n :=
          Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (ih y) (hM x y)
      _ = (∑ y, M x y) * α ^ n := by rw [Finset.sum_mul]
      _ ≤ α * α ^ n := mul_le_mul_of_nonneg_right (hrow x) (pow_nonneg hα n)
      _ = α ^ (n + 1) := (pow_succ' α n).symm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (G : SimpleGraph ι) [Fintype G.edgeSet] [DecidableRel G.Adj]

/-- **The single-site Dobrushin influence matrix** `C_{xy} = tanh(βJ)·[y∼x]` as a `Matrix`. -/
noncomputable def isingInfluenceMatrix (β J : ℝ) : Matrix ι ι ℝ :=
  fun x y => isingInfluence G β J x y

/-- **The Dobrushin coefficient** `α = Δ(G)·tanh(βJ)`: the maximum-degree bound on every influence
row sum. The Dobrushin condition `α < 1` is the high-temperature uniqueness hypothesis. -/
noncomputable def isingDobrushinCoeff (β J : ℝ) : ℝ :=
  G.maxDegree * Real.tanh (β * J)

omit [Fintype G.edgeSet] in
/-- **The influence matrix entries are nonnegative** (for `0 ≤ βJ`). -/
theorem isingInfluenceMatrix_nonneg {β J : ℝ} (hβJ : 0 ≤ β * J) (x y : ι) :
    0 ≤ isingInfluenceMatrix G β J x y := by
  rw [isingInfluenceMatrix, isingInfluence]
  split
  · exact real_tanh_nonneg hβJ
  · exact le_refl 0

omit [Fintype G.edgeSet] in
/-- **Every influence row sum is at most the Dobrushin coefficient** (for `0 ≤ βJ`):
`∑_y C_{xy} = deg(x)·tanh(βJ) ≤ Δ(G)·tanh(βJ)`. -/
theorem isingInfluenceMatrix_rowSum_le {β J : ℝ} (hβJ : 0 ≤ β * J) (x : ι) :
    ∑ y, isingInfluenceMatrix G β J x y ≤ isingDobrushinCoeff G β J := by
  have hrow : ∑ y, isingInfluenceMatrix G β J x y = G.degree x * Real.tanh (β * J) :=
    isingInfluence_rowSum G β J x
  rw [hrow, isingDobrushinCoeff]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast G.degree_le_maxDegree x)
    (real_tanh_nonneg hβJ)

omit [Fintype G.edgeSet] in
/-- **Geometric decay of the influence-matrix powers** (GJ §17.1): for `0 ≤ βJ`, the row sums of the
`n`-th power of the influence matrix are at most `α^n` with `α = Δ(G)·tanh(βJ)` the Dobrushin
coefficient. The boundary influence on a site decays geometrically with the number of steps `n`. -/
theorem isingInfluenceMatrix_pow_rowSum_le {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) (x : ι) :
    ∑ y, ((isingInfluenceMatrix G β J) ^ n) x y ≤ (isingDobrushinCoeff G β J) ^ n :=
  matrix_pow_rowSum_le (isingInfluenceMatrix_nonneg G hβJ)
    (mul_nonneg (Nat.cast_nonneg _) (real_tanh_nonneg hβJ))
    (isingInfluenceMatrix_rowSum_le G hβJ) n x

omit [Fintype G.edgeSet] [DecidableEq ι] in
/-- **The Dobrushin coefficient is nonnegative** (for `0 ≤ βJ`). -/
theorem isingDobrushinCoeff_nonneg {β J : ℝ} (hβJ : 0 ≤ β * J) :
    0 ≤ isingDobrushinCoeff G β J :=
  mul_nonneg (Nat.cast_nonneg _) (real_tanh_nonneg hβJ)

omit [Fintype G.edgeSet] [DecidableEq ι] in
/-- **The Dobrushin coefficient is below `1` at high temperature** (GJ §17.1): if `0 ≤ βJ` and
`βJ·Δ(G) < 1`, then `α = Δ(G)·tanh(βJ) ≤ Δ(G)·βJ < 1` (using `tanh(βJ) ≤ βJ`). -/
theorem isingDobrushinCoeff_lt_one_of_high_temp {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hΔ : β * J * G.maxDegree < 1) : isingDobrushinCoeff G β J < 1 := by
  rw [isingDobrushinCoeff]
  calc (G.maxDegree : ℝ) * Real.tanh (β * J)
      ≤ (G.maxDegree : ℝ) * (β * J) :=
        mul_le_mul_of_nonneg_left (tanh_le_self hβJ) (Nat.cast_nonneg _)
    _ = β * J * G.maxDegree := by ring
    _ < 1 := hΔ

omit [Fintype G.edgeSet] in
/-- **The influence-matrix power row sums tend to `0` at high temperature** (GJ §17.1): for `0 ≤ βJ`
and `βJ·Δ(G) < 1`, the row sums of `C^n` tend to `0` as `n → ∞` (squeezed between `0` and `α^n`
with `0 ≤ α < 1`). This is the geometric decay underlying the Dobrushin comparison theorem (not
formalized here). -/
theorem isingInfluenceMatrix_pow_rowSum_tendsto_zero {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hΔ : β * J * G.maxDegree < 1) (x : ι) :
    Filter.Tendsto (fun n => ∑ y, ((isingInfluenceMatrix G β J) ^ n) x y) Filter.atTop
      (nhds 0) := by
  refine squeeze_zero (fun n => Finset.sum_nonneg fun y _ => ?_)
    (fun n => isingInfluenceMatrix_pow_rowSum_le G hβJ n x) ?_
  · exact Matrix.pow_apply_nonneg (isingInfluenceMatrix_nonneg G hβJ) n x y
  · exact tendsto_pow_atTop_nhds_zero_of_lt_one (isingDobrushinCoeff_nonneg G hβJ)
      (isingDobrushinCoeff_lt_one_of_high_temp G hβJ hΔ)

end Dobrushin

end IsingModel

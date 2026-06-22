import IsingModel.Dobrushin.InfluenceMatrixResolvent

/-!
# The Dobrushin resolvent matrix `R = ∑ₙ Cⁿ` and its fixed-point equation (GJ §17.1)

At high temperature the influence matrix `C` (`isingInfluenceMatrix`) has Dobrushin coefficient
`α = Δ(G)·tanh(βJ) < 1`, so each entry of the powers `(Cⁿ)_{xy}` is dominated by `αⁿ` and the
per-entry Neumann series `∑ₙ (Cⁿ)_{xy}` converges. The resulting **resolvent matrix**
`R_{xy} = ∑ₙ (Cⁿ)_{xy}` is the coefficient appearing in the Dobrushin comparison theorem. It is
nonnegative, has row sums equal to the total influence (`isingTotalInfluence`), diagonal `≥ 1`, and
— the substantive result — satisfies the **resolvent fixed-point equation** `R = I + C·R`, i.e.
`R_{xy} = [x = y] + ∑_z C_{xz}·R_{zy}` (the Neumann series solves `(I − C)R = I`; the matrix-inverse
identity `R = (I − C)⁻¹` is not formalized here).

* `dobrushinResolvent` — the resolvent matrix `R_{xy} = ∑ₙ (Cⁿ)_{xy}`.
* `isingInfluenceMatrix_summable_pow_apply` — per-entry summability `Summable (n ↦ (Cⁿ)_{xy})`.
* `dobrushinResolvent_nonneg` / `dobrushinResolvent_rowSum` / `one_le_dobrushinResolvent_diag`.
* `dobrushinResolvent_fixed_point` — `R_{xy} = [x = y] + ∑_z C_{xz}·R_{zy}`.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §17.1, pp. 304–306.
-/

namespace IsingModel

namespace Dobrushin

open Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (G : SimpleGraph ι) [Fintype G.edgeSet] [DecidableRel G.Adj]

/-- **The Dobrushin resolvent matrix** `R_{xy} = ∑ₙ (Cⁿ)_{xy}`: the entry-wise Neumann series of the
single-site influence matrix `C`, the coefficient of the Dobrushin comparison theorem. -/
noncomputable def dobrushinResolvent (β J : ℝ) (x y : ι) : ℝ :=
  ∑' n, ((isingInfluenceMatrix G β J) ^ n) x y

omit [Fintype G.edgeSet] in
/-- **Per-entry summability of the influence-matrix powers**: for `0 ≤ βJ` and `βJ·Δ(G) < 1`, the
single entry `(Cⁿ)_{xy}` is summable in `n` (it is at most the row sum `≤ αⁿ`). -/
theorem isingInfluenceMatrix_summable_pow_apply {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hΔ : β * J * G.maxDegree < 1) (x y : ι) :
    Summable (fun n => ((isingInfluenceMatrix G β J) ^ n) x y) := by
  refine Summable.of_nonneg_of_le
    (fun n => Matrix.pow_apply_nonneg (isingInfluenceMatrix_nonneg G hβJ) n x y) (fun n => ?_)
    (summable_geometric_of_lt_one (isingDobrushinCoeff_nonneg G hβJ)
      (isingDobrushinCoeff_lt_one_of_high_temp G hβJ hΔ))
  calc ((isingInfluenceMatrix G β J) ^ n) x y
      ≤ ∑ y', ((isingInfluenceMatrix G β J) ^ n) x y' :=
        Finset.single_le_sum
          (fun y' _ => Matrix.pow_apply_nonneg (isingInfluenceMatrix_nonneg G hβJ) n x y')
          (Finset.mem_univ y)
    _ ≤ (isingDobrushinCoeff G β J) ^ n := isingInfluenceMatrix_pow_rowSum_le G hβJ n x

omit [Fintype G.edgeSet] in
/-- **The resolvent entries are nonnegative**. -/
theorem dobrushinResolvent_nonneg {β J : ℝ} (hβJ : 0 ≤ β * J) (x y : ι) :
    0 ≤ dobrushinResolvent G β J x y :=
  tsum_nonneg fun n => Matrix.pow_apply_nonneg (isingInfluenceMatrix_nonneg G hβJ) n x y

omit [Fintype G.edgeSet] in
/-- **The resolvent row sums equal the total influence**: `∑_y R_{xy} = isingTotalInfluence x`
(swapping the finite row sum with the Neumann series). -/
theorem dobrushinResolvent_rowSum {β J : ℝ} (hβJ : 0 ≤ β * J) (hΔ : β * J * G.maxDegree < 1)
    (x : ι) : ∑ y, dobrushinResolvent G β J x y = isingTotalInfluence G β J x := by
  simp only [dobrushinResolvent, isingTotalInfluence]
  exact (Summable.tsum_finsetSum
    (fun y _ => isingInfluenceMatrix_summable_pow_apply G hβJ hΔ x y)).symm

omit [Fintype G.edgeSet] in
/-- **The resolvent diagonal is at least `1`**: `R_{xx} ≥ 1` (the identity `n = 0` term). -/
theorem one_le_dobrushinResolvent_diag {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hΔ : β * J * G.maxDegree < 1) (x : ι) : 1 ≤ dobrushinResolvent G β J x x := by
  have h := Summable.le_tsum (isingInfluenceMatrix_summable_pow_apply G hβJ hΔ x x) 0
    fun n _ => Matrix.pow_apply_nonneg (isingInfluenceMatrix_nonneg G hβJ) n x x
  simpa [pow_zero, Matrix.one_apply] using h

omit [Fintype G.edgeSet] in
/-- **The Dobrushin resolvent fixed-point equation** (GJ §17.1): `R = I + C·R`, i.e.
`R_{xy} = [x = y] + ∑_z C_{xz}·R_{zy}`. The Neumann series `∑ₙ Cⁿ` solves `(I − C)R = I`; the
matrix-inverse identity `R = (I − C)^{-1}` is not formalized here. Proof: split off the `n = 0`
identity term, write `C^{n+1} = C·Cⁿ`, and swap the finite `z`-sum with the Neumann series. -/
theorem dobrushinResolvent_fixed_point {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hΔ : β * J * G.maxDegree < 1) (x y : ι) :
    dobrushinResolvent G β J x y
      = (if x = y then (1 : ℝ) else 0)
        + ∑ z, isingInfluenceMatrix G β J x z * dobrushinResolvent G β J z y := by
  rw [dobrushinResolvent,
    Summable.tsum_eq_zero_add (isingInfluenceMatrix_summable_pow_apply G hβJ hΔ x y)]
  have h0 : ((isingInfluenceMatrix G β J) ^ 0) x y = (if x = y then (1 : ℝ) else 0) := by
    simp [pow_zero, Matrix.one_apply]
  have hrest : ∑' n, ((isingInfluenceMatrix G β J) ^ (n + 1)) x y
      = ∑ z, isingInfluenceMatrix G β J x z * dobrushinResolvent G β J z y := by
    have hsumz : ∀ z : ι, Summable
        (fun n => isingInfluenceMatrix G β J x z * ((isingInfluenceMatrix G β J) ^ n) z y) :=
      fun z => (isingInfluenceMatrix_summable_pow_apply G hβJ hΔ z y).mul_left _
    simp_rw [pow_succ', Matrix.mul_apply]
    rw [Summable.tsum_finsetSum (fun z _ => hsumz z)]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [tsum_mul_left, dobrushinResolvent]
  rw [h0, hrest]

end Dobrushin

end IsingModel

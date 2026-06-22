import IsingModel.Dobrushin.DobrushinResolvent
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Exponential distance-decay of the Dobrushin resolvent (GJ §17.1, Issue #4214 §A)

The Dobrushin resolvent `R_{xy} = ∑_n (Cⁿ)_{xy}` of the single-site influence matrix
`C_{xy} = tanh(βJ)·[y∼x]` decays **exponentially in the graph distance**: under the sufficient
high-temperature condition `βJ·Δ(G) < 1` (whence the Dobrushin coefficient `α = Δ(G)·tanh(βJ) < 1`),
\[
  R_{xy} ≤ \frac{α^{d_G(x,y)}}{1 − α}, \qquad α = Δ(G)·tanh(βJ).
\]
This is the quantitative content of Dobrushin uniqueness: the boundary influence on a site decays
geometrically with distance, so (combined with the comparison theorem) the boundary sensitivity of a
local observable decays exponentially. Since `C = tanh(βJ)·A` with `A = G.adjMatrix`, the entry
`(Cⁿ)_{xy} = tanhⁿ·(number of length-`n` walks `x → y`) vanishes for `n < d_G(x,y)` (no such walk),
so only the `n ≥ d_G(x,y)` terms contribute, summing to the geometric tail.

* `isingInfluenceMatrix_eq_smul_adjMatrix` — `C = tanh(βJ) • G.adjMatrix ℝ`.
* `isingInfluenceMatrix_pow_apply_eq_zero_of_lt_dist` — `(Cⁿ)_{xy} = 0` for `n < d_G(x,y)`.
* `dobrushinResolvent_le_pow_dist` — the exponential distance-decay `R_{xy} ≤ αᵈⁱˢᵗ/(1−α)`.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §17.1, pp. 304–306.
-/

namespace IsingModel

namespace Dobrushin

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (G : SimpleGraph ι) [Fintype G.edgeSet] [DecidableRel G.Adj]

omit [Fintype G.edgeSet] in
/-- **The influence matrix is a scalar multiple of the adjacency matrix**: `C = tanh(βJ)·A`. -/
theorem isingInfluenceMatrix_eq_smul_adjMatrix (β J : ℝ) :
    isingInfluenceMatrix G β J = Real.tanh (β * J) • G.adjMatrix ℝ := by
  ext x y
  simp only [isingInfluenceMatrix, isingInfluence, Matrix.smul_apply, SimpleGraph.adjMatrix_apply,
    smul_eq_mul, SimpleGraph.mem_neighborFinset, mul_ite, mul_one, mul_zero]

omit [Fintype G.edgeSet] in
/-- **Entry-wise form of the influence-matrix power**: `(Cⁿ)_{xy} = tanhⁿ·(card of length-`n` walks
`x → y`). -/
theorem isingInfluenceMatrix_pow_apply (β J : ℝ) (n : ℕ) (x y : ι) :
    ((isingInfluenceMatrix G β J) ^ n) x y
      = Real.tanh (β * J) ^ n * (Fintype.card {p : G.Walk x y | p.length = n} : ℝ) := by
  rw [isingInfluenceMatrix_eq_smul_adjMatrix, smul_pow, Matrix.smul_apply, smul_eq_mul,
    G.adjMatrix_pow_apply_eq_card_walk]

omit [Fintype G.edgeSet] in
/-- **The influence-matrix power vanishes below the graph distance** (GJ §17.1): `(Cⁿ)_{xy} = 0`
whenever `n < d_G(x,y)`, since no walk `x → y` of length `n < d_G(x,y)` exists. -/
theorem isingInfluenceMatrix_pow_apply_eq_zero_of_lt_dist (β J : ℝ) {n : ℕ} {x y : ι}
    (hn : n < G.dist x y) : ((isingInfluenceMatrix G β J) ^ n) x y = 0 := by
  rw [isingInfluenceMatrix_pow_apply]
  have hempty : IsEmpty {p : G.Walk x y | p.length = n} :=
    ⟨fun p => absurd (p.2 ▸ G.dist_le p.1) (by omega)⟩
  rw [Fintype.card_eq_zero_iff.mpr hempty]
  simp

omit [Fintype G.edgeSet] in
/-- **The influence-matrix power vanishes between unreachable sites**: `(Cⁿ)_{xy} = 0` whenever `x`
and `y` lie in different connected components, since no walk `x → y` of any length exists. -/
theorem isingInfluenceMatrix_pow_apply_eq_zero_of_not_reachable (β J : ℝ) (n : ℕ) {x y : ι}
    (hxy : ¬ G.Reachable x y) : ((isingInfluenceMatrix G β J) ^ n) x y = 0 := by
  rw [isingInfluenceMatrix_pow_apply]
  have hempty : IsEmpty {p : G.Walk x y | p.length = n} := ⟨fun p => hxy ⟨p.1⟩⟩
  rw [Fintype.card_eq_zero_iff.mpr hempty]
  simp

omit [Fintype G.edgeSet] in
/-- **The Dobrushin resolvent vanishes between unreachable sites**: `R_{xy} = 0` whenever `x` and
`y` lie in different connected components. This sharpens `dobrushinResolvent_le_pow_dist`: on each
connected component `G.dist` is the genuine graph distance and the bound is true exponential decay;
between components `G.dist` is the junk value `0` (so the bound degenerates to the trivial
`(1 − α)⁻¹`), but the resolvent itself is in fact `0`. -/
theorem dobrushinResolvent_eq_zero_of_not_reachable (β J : ℝ) {x y : ι}
    (hxy : ¬ G.Reachable x y) : dobrushinResolvent G β J x y = 0 := by
  rw [dobrushinResolvent]
  simp only [isingInfluenceMatrix_pow_apply_eq_zero_of_not_reachable G β J _ hxy, tsum_zero]

omit [Fintype G.edgeSet] in
/-- **Geometric bound for the shifted influence-power tail**: for any shift `d`, the tail sum
`∑'_n (C^{n+d})_{xy} ≤ αᵈ·(1−α)⁻¹` (`α = Δ(G)·tanh(βJ)`). Keeping `d` a free variable (rather than
`G.dist x y`) avoids whnf-unfolding the noncomputable graph distance in the geometric estimates. -/
theorem isingInfluenceMatrix_tsum_shift_apply_le {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hΔ : β * J * G.maxDegree < 1) (x y : ι) (d : ℕ) :
    ∑' n, ((isingInfluenceMatrix G β J) ^ (n + d)) x y
      ≤ isingDobrushinCoeff G β J ^ d * (1 - isingDobrushinCoeff G β J)⁻¹ := by
  have hα0 : 0 ≤ isingDobrushinCoeff G β J := isingDobrushinCoeff_nonneg G hβJ
  have hα1 : isingDobrushinCoeff G β J < 1 := isingDobrushinCoeff_lt_one_of_high_temp G hβJ hΔ
  have hsummable := isingInfluenceMatrix_summable_pow_apply G hβJ hΔ x y
  have hge : Summable (fun n : ℕ => isingDobrushinCoeff G β J ^ (n + d)) := by
    simp_rw [pow_add]
    exact (summable_geometric_of_lt_one hα0 hα1).mul_right _
  have hle : ∀ n, ((isingInfluenceMatrix G β J) ^ (n + d)) x y
      ≤ isingDobrushinCoeff G β J ^ (n + d) := by
    intro n
    refine le_trans (Finset.single_le_sum
      (fun z _ => Matrix.pow_apply_nonneg (isingInfluenceMatrix_nonneg G hβJ) (n + d) x z)
      (Finset.mem_univ y)) ?_
    exact isingInfluenceMatrix_pow_rowSum_le G hβJ (n + d) x
  refine le_trans (Summable.tsum_le_tsum hle ((summable_nat_add_iff d).mpr hsummable) hge)
    (le_of_eq ?_)
  simp_rw [pow_add]
  rw [tsum_mul_right, tsum_geometric_of_lt_one hα0 hα1, mul_comm]

omit [Fintype G.edgeSet] in
/-- **Exponential distance-decay of the Dobrushin resolvent** (GJ §17.1): under the sufficient
high-temperature condition `βJ·Δ(G) < 1` (whence the Dobrushin coefficient `α = Δ(G)·tanh(βJ) < 1`),
`R_{xy} ≤ αᵈⁱˢᵗ/(1−α)`. For reachable `x, y` (where `G.dist` is the genuine graph distance) this is
true exponential decay; for unreachable pairs `G.dist x y = 0` and the bound degenerates to the
trivial `(1 − α)⁻¹`, while in fact `R_{xy} = 0` (`dobrushinResolvent_eq_zero_of_not_reachable`). -/
theorem dobrushinResolvent_le_pow_dist {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hΔ : β * J * G.maxDegree < 1) (x y : ι) :
    dobrushinResolvent G β J x y
      ≤ isingDobrushinCoeff G β J ^ G.dist x y * (1 - isingDobrushinCoeff G β J)⁻¹ := by
  have hsummable := isingInfluenceMatrix_summable_pow_apply G hβJ hΔ x y
  -- the first `d_G(x,y)` terms vanish (no short walk), so `R = ∑'_n (C^{n+dist})_xy`
  have hzero : ∀ i ∈ Finset.range (G.dist x y), ((isingInfluenceMatrix G β J) ^ i) x y = 0 :=
    fun i hi => isingInfluenceMatrix_pow_apply_eq_zero_of_lt_dist G β J (Finset.mem_range.mp hi)
  have hshift : dobrushinResolvent G β J x y
      = ∑' n, ((isingInfluenceMatrix G β J) ^ (n + G.dist x y)) x y := by
    rw [dobrushinResolvent, ← (hsummable.sum_add_tsum_nat_add (G.dist x y)),
      Finset.sum_eq_zero hzero, zero_add]
  rw [hshift]
  exact isingInfluenceMatrix_tsum_shift_apply_le G hβJ hΔ x y (G.dist x y)

end Dobrushin

end IsingModel

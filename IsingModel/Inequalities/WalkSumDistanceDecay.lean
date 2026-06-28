import IsingModel.Inequalities.WalkSum
import IsingModel.Conditioning.WalkCountDegreeBound
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Geometric distance-decay of the walk-sum (FFS Ch 12 / GJ §18)

The walk-sum `walkSum G z i j n = z^n · #{length-n walks i → j}` (`WalkSum.lean`) is the
right-hand side of the **sharp** random-walk / Simon–Lieb representation of the two-point function
`⟨σ_i σ_j⟩ ≤ ∑_n walkSum G (tanh βJ) i j n` (the sharp `tanh`-coefficient bound; the `⟨⟩ ≤ ∑walk`
ratio step is the FFS switching-lemma core, tracked in #4393).  Here we prove the **geometric
distance-decay** of that right-hand side: the total walk-sum is bounded by a geometric series in the
graph distance,

`∑'_n walkSum G z i j n ≤ (z · Δ)^{dist(i,j)} / (1 − z · Δ)`,   `Δ = G.maxDegree`,  `z · Δ < 1`,

so with `z = tanh(βJ)` and `Δ ≤ 2d` the two-point function *would* decay (once the switching ratio
`⟨⟩ ≤ ∑walk` of #4393 is supplied) at the sharp rate `−log(2d · tanh βJ)`, sharper than the
Simon–Lieb `−log(βJ · 2d)` since `tanh βJ < βJ`.  This is
the mechanical geometric-closure brick (Route A, brick A3) of the sharp-decay programme #4393; the
remaining `⟨⟩ ≤ ∑walk` switching ratio is the research-level core.

Ingredients: walks shorter than the distance do not exist (`SimpleGraph.dist_le`), the length-`n`
walk count is `≤ Δ^n` (`walksFromCount_le_pow`), and the geometric tail
(`Summable.sum_add_tsum_nat_add` shift past the vanishing prefix + `tsum_geometric_of_lt_one`).

## References

* Fernández–Fröhlich–Sokal, *Random Walks, Critical Phenomena, and Triviality* (1992), Ch 12.
* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.
* Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017), §3.7.3.
-/

namespace IsingModel

namespace Ambient

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Walk-sum vanishes below the graph distance**: there are no length-`n` walks `i → j` when
`n < dist(i,j)` (any walk has length `≥ dist`, `SimpleGraph.dist_le`), so the walk-sum is `0`. -/
theorem walkSum_eq_zero_of_lt_dist (z : ℝ) {i j : V} {n : ℕ} (hn : n < G.dist i j) :
    walkSum G z i j n = 0 := by
  rw [walkSum_eq_pow_mul_card]
  have hcard : (G.finsetWalkLength n i j).card = 0 := by
    rw [Finset.card_eq_zero, ← Finset.not_nonempty_iff_eq_empty]
    rintro ⟨w, hw⟩
    have hlen : w.length = n := mem_finsetWalkLength_iff.mp hw
    have hdl := SimpleGraph.dist_le w
    rw [hlen] at hdl
    omega
  rw [hcard]; simp

/-- **Per-length geometric bound on the walk-sum**: for `0 ≤ z`, the length-`n` walk-sum is bounded
by `(z · Δ)^n` with `Δ = G.maxDegree`.  The length-`n` walk count from `i` to `j` is at most the
total count `walksFromCount G i n ≤ Δ^n` (`walksFromCount_le_pow`), and `walkSum = z^n · card`. -/
theorem walkSum_le_mul_maxDegree_pow {z : ℝ} (hz : 0 ≤ z) (i j : V) (n : ℕ) :
    walkSum G z i j n ≤ (z * G.maxDegree) ^ n := by
  rw [walkSum_eq_pow_mul_card, mul_pow]
  have hcard : ((G.finsetWalkLength n i j).card : ℝ) ≤ (G.maxDegree : ℝ) ^ n := by
    have hsingle : (G.finsetWalkLength n i j).card ≤ walksFromCount G i n := by
      rw [walksFromCount]
      exact Finset.single_le_sum (f := fun v => (G.finsetWalkLength n i v).card)
        (fun v _ => Nat.zero_le _) (Finset.mem_univ j)
    have hpow := walksFromCount_le_pow G (fun w => G.degree_le_maxDegree w) n i
    calc ((G.finsetWalkLength n i j).card : ℝ)
        ≤ (walksFromCount G i n : ℝ) := by exact_mod_cast hsingle
      _ ≤ (G.maxDegree : ℝ) ^ n := by exact_mod_cast hpow
  exact mul_le_mul_of_nonneg_left hcard (pow_nonneg hz n)

/-- **Geometric distance-decay of the total walk-sum** (FFS Ch 12 / GJ §18): for `0 ≤ z` and
`z · Δ < 1` (`Δ = G.maxDegree`),

`∑'_n walkSum G z i j n ≤ (z · Δ)^{dist(i,j)} / (1 − z · Δ)`.

The summand vanishes for `n < dist` (`walkSum_eq_zero_of_lt_dist`), so the total sum equals its tail
`∑'_n walkSum (n + dist)` (shift past the vanishing prefix, `Summable.sum_add_tsum_nat_add`); each
tail term is `≤ (z·Δ)^{n+dist}` (`walkSum_le_mul_maxDegree_pow`), and
`∑'_n (z·Δ)^{n+dist} = (z·Δ)^{dist} · (1 − z·Δ)⁻¹` (`tsum_geometric_of_lt_one`). -/
theorem tsum_walkSum_le_geometric {z : ℝ} (hz : 0 ≤ z)
    (hzD : z * G.maxDegree < 1) (i j : V) :
    ∑' n : ℕ, walkSum G z i j n ≤ (z * G.maxDegree) ^ G.dist i j / (1 - z * G.maxDegree) := by
  set r : ℝ := z * G.maxDegree with hr
  have hr0 : 0 ≤ r := mul_nonneg hz (Nat.cast_nonneg _)
  set D : ℕ := G.dist i j with hD
  -- geometric summability and the comparison `walkSum ≤ r^n`.
  have hsum_geo : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_lt_one hr0 hzD
  have hws_nonneg : ∀ n, 0 ≤ walkSum G z i j n := fun n => walkSum_nonneg G hz i j n
  have hws_le : ∀ n, walkSum G z i j n ≤ r ^ n := fun n =>
    walkSum_le_mul_maxDegree_pow G hz i j n
  have hws_sum : Summable (fun n => walkSum G z i j n) :=
    hsum_geo.of_nonneg_of_le hws_nonneg hws_le
  -- the vanishing prefix lets us shift the sum past `D = dist`.
  have hprefix : ∑ k ∈ Finset.range D, walkSum G z i j k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    exact walkSum_eq_zero_of_lt_dist G z (hD ▸ Finset.mem_range.mp hk)
  have hshift : ∑' n, walkSum G z i j n = ∑' n, walkSum G z i j (n + D) := by
    have h := Summable.sum_add_tsum_nat_add D hws_sum
    rw [hprefix, zero_add] at h
    exact h.symm
  -- bound the tail by the shifted geometric series.
  have hgeo_shift_sum : Summable (fun n : ℕ => r ^ (n + D)) :=
    (summable_nat_add_iff D).2 hsum_geo
  have htail_le : ∑' n, walkSum G z i j (n + D) ≤ ∑' n, r ^ (n + D) :=
    ((summable_nat_add_iff D).2 hws_sum).tsum_le_tsum (fun n => hws_le (n + D)) hgeo_shift_sum
  have hgeo_val : ∑' n : ℕ, r ^ (n + D) = r ^ D * (1 - r)⁻¹ := by
    simp_rw [pow_add]
    rw [tsum_mul_right, tsum_geometric_of_lt_one hr0 hzD]
    ring
  calc ∑' n, walkSum G z i j n
      = ∑' n, walkSum G z i j (n + D) := hshift
    _ ≤ ∑' n, r ^ (n + D) := htail_le
    _ = r ^ D * (1 - r)⁻¹ := hgeo_val
    _ = r ^ D / (1 - r) := (div_eq_mul_inv _ _).symm

end Ambient

end IsingModel

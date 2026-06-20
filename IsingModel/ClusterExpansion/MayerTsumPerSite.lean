import IsingModel.ClusterExpansion.MayerTsumBound

/-!
# Volume-uniform (per-site) bound on the Mayer expansion sum (GJ §18.5)

Dividing the explicit Mayer expansion sum bound (`tsum_abs_mayerExpansionTerm_succ_le`,
#4136) by the volume `|V| = Fintype.card ι` gives a **volume-uniform** (per-site) bound:
for `r = Δ²e|t|`, `Δ²e|t| < 1`, `ρ = 4r/(1−r)² < 1`, and a nonempty vertex type,

`(∑'_n |mayerExpansionTerm G (n + 1) t|)/|V| ≤ 1/((1−r)(1−ρ))`,

with a right-hand side independent of the volume.  Since the Kotecky--Preiss condition
`4Δ²e|t|/(1−Δ²e|t|)² < 1` is itself volume-uniform (it depends only on the maximum degree
`Δ`, bounded uniformly on bounded-degree graphs), this is the volume-uniform convergence
of the (per-site) cluster-expansion contribution.

* `tsum_abs_mayerExpansionTerm_succ_div_card_le`.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~332--336.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion).
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Volume-uniform (per-site) bound on the Mayer expansion sum.**  For a nonempty
vertex type, `Δ²e|t| < 1`, and `ρ := 4Δ²e|t|/(1−Δ²e|t|)² < 1`, the per-site total
absolute Mayer expansion sum is bounded by the volume-uniform constant
`1/((1−r)(1−ρ))` (`r = Δ²e|t|`):
`(∑'_n |mayerExpansionTerm G (n + 1) t|)/|V| ≤ ((1−r)(1−ρ))⁻¹`.  Dividing
`tsum_abs_mayerExpansionTerm_succ_le` (#4136) by `|V|`. -/
theorem tsum_abs_mayerExpansionTerm_succ_div_card_le (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] [Nonempty ι] {t : ℝ}
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1)
    (hρ : 4 * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))
        / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ 2 < 1) :
    (∑' n : ℕ, |mayerExpansionTerm G (n + 1) t|) / (Fintype.card ι : ℝ)
      ≤ ((1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))
          * (1 - 4 * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))
                / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ 2))⁻¹ := by
  set rr : ℝ := (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) with hrr
  set q : ℝ := 1 - rr with hq
  have hqpos : 0 < q := by rw [hq]; linarith [hkp]
  set ρ : ℝ := 4 * rr / q ^ 2 with hρdef
  have hρpos : 0 < 1 - ρ := by linarith [hρ]
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ hcard]
  -- `∑' ≤ |V|/q·(1−ρ)⁻¹ = (q(1−ρ))⁻¹·|V|`.
  refine (tsum_abs_mayerExpansionTerm_succ_le G hkp hρ).trans ?_
  rw [mul_inv]
  rw [div_mul_eq_mul_div, mul_comm, ← div_eq_mul_inv, mul_div_assoc]
  exact le_of_eq (by ring)

end IsingModel

import IsingModel.ClusterExpansion.MayerSeriesConvergence

/-!
# Explicit bound on the Mayer expansion sum (GJ §18.5)

Summing the geometric per-order bound
`|mayerExpansionTerm G (n + 1) t| ≤ |V|/(1−r)·(4r/(1−r)²)^n`
(`mayerExpansionTerm_succ_abs_le_card_div_mul_geometric`, #4134) over `n` gives an
explicit closed-form bound on the total (shifted) Mayer expansion sum: for
`r = Δ²e|t|`, `Δ²e|t| < 1`, and `ρ = 4r/(1−r)² < 1`,

`∑'_n |mayerExpansionTerm G (n + 1) t| ≤ |V|/((1−r)(1−ρ))`.

This is the explicit Kotecky--Preiss-type bound on the convergent cluster-expansion sum
(the contribution of the non-trivial Mayer orders).

* `tsum_abs_mayerExpansionTerm_succ_le`.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~332--336.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion).
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Explicit bound on the shifted Mayer expansion sum.**  Summing the geometric
per-order bound (#4134) gives `∑'_n |mayerExpansionTerm G (n + 1) t| ≤ |V|/((1−r)(1−ρ))`
with `r = Δ²e|t|` and `ρ = 4r/(1−r)²`, under `Δ²e|t| < 1` and `ρ < 1`. -/
theorem tsum_abs_mayerExpansionTerm_succ_le (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] {t : ℝ}
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1)
    (hρ : 4 * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))
        / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ 2 < 1) :
    (∑' n : ℕ, |mayerExpansionTerm G (n + 1) t|)
      ≤ (Fintype.card ι : ℝ) / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))
          * (1 - 4 * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))
                / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ 2)⁻¹ := by
  set rr : ℝ := (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) with hrr
  set q : ℝ := 1 - rr with hq
  have hqpos : 0 < q := by rw [hq]; linarith [hkp]
  set ρ : ℝ := 4 * rr / q ^ 2 with hρdef
  have hρ0 : 0 ≤ ρ := by rw [hρdef]; positivity
  have hsummL : Summable fun n : ℕ => |mayerExpansionTerm G (n + 1) t| :=
    summable_abs_mayerExpansionTerm_succ_of_tail_condition G hkp hρ
  have hsummR : Summable fun n : ℕ => (Fintype.card ι : ℝ) / q * ρ ^ n :=
    (summable_geometric_of_lt_one hρ0 hρ).mul_left _
  calc (∑' n : ℕ, |mayerExpansionTerm G (n + 1) t|)
      ≤ ∑' n : ℕ, (Fintype.card ι : ℝ) / q * ρ ^ n :=
        hsummL.tsum_le_tsum
          (fun n => mayerExpansionTerm_succ_abs_le_card_div_mul_geometric G n hkp) hsummR
    _ = (Fintype.card ι : ℝ) / q * (1 - ρ)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hρ0 hρ]

end IsingModel

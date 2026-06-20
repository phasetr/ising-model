import IsingModel.ClusterExpansion.MayerTermTailSummability

/-!
# Convergence of the Mayer expansion series (GJ §18.5)

The absolute summability of the Mayer expansion terms
(`summable_abs_mayerExpansionTerm_of_tail_condition`, #4134) gives, under the sufficient
high-temperature conditions `Δ²e|t| < 1` and `4Δ²e|t|/(1−Δ²e|t|)² < 1`, the convergence
of the Mayer series
itself: the partial sums `mayerPartialSum G N t = ∑_{n=0}^{N} mayerExpansionTerm G n t`
converge to `∑'_n mayerExpansionTerm G n t`.  This discharges the "convergence follows
from Kotecky--Preiss-type bounds (deferred)" note on `mayerPartialSum`.

* `summable_mayerExpansionTerm_of_tail_condition`.
* `tendsto_mayerPartialSum_of_tail_condition`.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~332--336.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion).
-/

namespace IsingModel

open Finset Filter Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The Mayer expansion terms are summable.**  Under the sufficient high-temperature
condition, the Mayer series `n ↦ mayerExpansionTerm G n t` is summable (not merely
absolutely): absolute summability (#4134) implies summability in `ℝ`. -/
theorem summable_mayerExpansionTerm_of_tail_condition (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] {t : ℝ}
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1)
    (hρ : 4 * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))
        / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ 2 < 1) :
    Summable fun n : ℕ => mayerExpansionTerm G n t :=
  (summable_abs_mayerExpansionTerm_of_tail_condition G hkp hρ).of_abs

/-- **Convergence of the Mayer partial sums.**  Under the sufficient high-temperature
condition, the Mayer partial sums `mayerPartialSum G N t` converge to the Mayer series
`∑'_n mayerExpansionTerm G n t`.  This discharges the deferred convergence note on
`mayerPartialSum`: the limit exists in the explicit regime `Δ²e|t| < 1` and
`4Δ²e|t|/(1−Δ²e|t|)² < 1`. -/
theorem tendsto_mayerPartialSum_of_tail_condition (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] {t : ℝ}
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1)
    (hρ : 4 * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))
        / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ 2 < 1) :
    Tendsto (fun N => mayerPartialSum G N t) atTop
      (𝓝 (∑' n, mayerExpansionTerm G n t)) := by
  have hsum := summable_mayerExpansionTerm_of_tail_condition G hkp hρ
  have htend := hsum.hasSum.tendsto_sum_nat
  have hcomp := htend.comp (tendsto_add_atTop_nat 1)
  refine hcomp.congr fun N => ?_
  rw [mayerPartialSum]
  rfl

end IsingModel

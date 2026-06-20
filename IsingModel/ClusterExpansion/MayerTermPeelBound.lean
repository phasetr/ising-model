import IsingModel.ClusterExpansion.MayerCore.MayerTreeSumExpActivity
import IsingModel.ClusterExpansion.RootedParentActiveTreePeelBound

/-!
# The Mayer expansion term bounded by the summed child-count peel bound (GJ §18.5)

Composing the Penrose tree-graph bound on the Mayer expansion term
(`mayerExpansionTerm_succ_abs_le_treeSum_rootedExpActivity`, #4095) with the bound of the
Penrose tree sum by the summed child-count peel bound (`penroseTreeSum_le_sum_peelBound`,
#4119) bounds `|mayerExpansionTerm G (n + 1) t|` by `(n + 1)!⁻¹` times the sum, over
complete-graph spanning-tree shapes, of the child-count peel bound.

* `mayerExpansionTerm_succ_abs_le_sum_peelBound`.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~332--336.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion).
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The Mayer expansion term is bounded by the summed child-count peel bound.**  For
`Δ²·e·|t| < 1` (`Δ = G.maxDegree`), `|mayerExpansionTerm G (n + 1) t|` is at most
`(n + 1)!⁻¹` times the sum, over complete-graph spanning-tree shapes `T`, of the
child-count peel bound for the parent code of `T`.  This composes the Penrose tree-graph
bound (#4095) with the leaf-peel bridge (#4119). -/
theorem mayerExpansionTerm_succ_abs_le_sum_peelBound (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (n : ℕ) {t : ℝ}
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1) :
    |mayerExpansionTerm G (n + 1) t|
      ≤ ((n + 1).factorial : ℝ)⁻¹
        * ∑ T : {S : Finset (Sym2 (Fin (n + 1))) //
            S ∈ Penrose.spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1)))},
          rootedParentActivePeelBound G (Penrose.completeGraphTreeParentCode n T)
            (Finset.univ : Finset (Fin n)) (fun _ => 0) t := by
  refine (mayerExpansionTerm_succ_abs_le_treeSum_rootedExpActivity G n t).trans ?_
  exact mul_le_mul_of_nonneg_left (penroseTreeSum_le_sum_peelBound G n hkp) (by positivity)

end IsingModel

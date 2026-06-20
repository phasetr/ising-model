import IsingModel.ClusterExpansion.UrsellTreeBound
import IsingModel.ClusterExpansion.MayerCore.UrsellMajorant

/-!
# Mayer term bounded by the incompatibility-graph tree sum of activities (GJ §18.5)

The volume-uniform Kotecky--Preiss route bounds each Mayer expansion term by a sum
over the spanning trees of the *polymer incompatibility graph* of the activity
product — crucially keeping the incompatibility-graph tree range (rather than
collapsing to the volume-dependent `(∑_P |t|^{|P|})^n`), so that the per-edge
Kotecky--Preiss weight bound can later be applied along the tree edges.

`mayerExpansionTerm_abs_le_treeSum_activity`:
`|mayerExpansionTerm G n t| ≤ (n!)⁻¹ · ∑_ω ∑_{T spanning tree of incompat(ω)} ∏_i |t|^{|ω i|}`,
combining the triangle inequality (`mayerExpansionTerm_abs_le`), the Penrose
tree-graph Ursell bound `|ϕ^T(ω)| ≤ numSpanningTrees (incompat ω) / n!`
(`ursellCoefficient_abs_le_numSpanningTrees_div_factorial`, which keeps the
incompatibility graph), and the activity factorisation `|z(t,ω)| = ∏_i |t|^{|ω i|}`
(`clusterSeqActivity_abs`).  Rewriting the tree *count* as a constant sum over the
spanning-tree set keeps the trees explicit for the rooted-tree induction.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~332--336.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion / tree-graph inequality).
-/

namespace IsingModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Mayer term bounded by the incompatibility-graph tree sum of activities.**  For
each order `n`,
`|mayerExpansionTerm G n t| ≤ (n!)⁻¹ · ∑_ω ∑_{T tree of incompat(ω)} ∏_i |t|^{|ω i|}`,
where the inner sum ranges over the spanning trees of the polymer incompatibility
graph of `ω`.  Keeping the incompatibility-graph tree range (instead of collapsing
the count) is what lets the per-edge Kotecky--Preiss weight bound be applied along
the tree edges in the rooted-tree induction. -/
theorem mayerExpansionTerm_abs_le_treeSum_activity (G : SimpleGraph ι)
    [Fintype G.edgeSet] (n : ℕ) (t : ℝ) :
    |mayerExpansionTerm G n t| ≤
      ((n.factorial : ℝ)⁻¹) *
        ∑ ω ∈ Fintype.piFinset (fun _ : Fin n => allPolymers G),
          ∑ _T ∈ Penrose.spanningTreeEdgeSubsets (polymerSeqIncompatibilityGraph ω),
            ∏ i : Fin n, |t| ^ (ω i).card := by
  have hpw : ∀ ω ∈ Fintype.piFinset (fun _ : Fin n => allPolymers G),
      |ursellCoefficient ω| * |clusterSeqActivity t ω|
        ≤ ((n.factorial : ℝ)⁻¹)
            * ∑ _T ∈ Penrose.spanningTreeEdgeSubsets (polymerSeqIncompatibilityGraph ω),
                ∏ i : Fin n, |t| ^ (ω i).card := by
    intro ω _
    rw [clusterSeqActivity_abs]
    calc |ursellCoefficient ω| * ∏ i : Fin n, |t| ^ (ω i).card
        ≤ ((Penrose.numSpanningTrees (polymerSeqIncompatibilityGraph ω) : ℝ)
            / n.factorial) * ∏ i : Fin n, |t| ^ (ω i).card :=
          mul_le_mul_of_nonneg_right
            (ursellCoefficient_abs_le_numSpanningTrees_div_factorial ω) (by positivity)
      _ = ((n.factorial : ℝ)⁻¹)
            * ∑ _T ∈ Penrose.spanningTreeEdgeSubsets (polymerSeqIncompatibilityGraph ω),
                ∏ i : Fin n, |t| ^ (ω i).card := by
          rw [Finset.sum_const, nsmul_eq_mul, Penrose.numSpanningTrees]
          ring
  refine (mayerExpansionTerm_abs_le G n t).trans ((Finset.sum_le_sum hpw).trans_eq ?_)
  rw [Finset.mul_sum]

end IsingModel

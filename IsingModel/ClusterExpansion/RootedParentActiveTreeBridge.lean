import IsingModel.ClusterExpansion.Penrose.CompleteTreePolymerConstraint
import IsingModel.ClusterExpansion.Penrose.SpanningTreeMono
import IsingModel.ClusterExpansion.Families.EvenSubgraphs

/-!
# Fubini swap of the Penrose tree sum over complete-tree shapes (GJ §18.5)

The Penrose tree-graph bound on `mayerExpansionTerm` is a double sum
`∑_ω ∑_{T ∈ ST(incompat ω)} W ω` over polymer sequences `ω` and spanning trees `T` of
the incompatibility graph.  Since the spanning trees of a subgraph are spanning trees of
the complete graph (`spanningTreeEdgeSubsets_mono`), this swaps to a sum over the
complete-graph spanning-tree shapes `T`, with the inner sum over the sequences for which
`T` is a spanning tree of `incompat ω`.  Relaxing the latter constraint to the per-edge
parent incompatibility (`sum_filter_treeIncompat_le_filter_parentConstraint`, #4096)
gives the bound the rooted-tree leaf-peel machinery consumes.

* `penroseTreeSum_le_subtype_parentConstraint`.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~332--336.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion / tree-graph inequality).
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Fubini swap of the Penrose tree sum, with parent-constraint relaxation.**  The
Penrose double sum over polymer sequences and spanning trees of the incompatibility
graph is bounded by the sum, over complete-graph spanning-tree shapes `T`, of the weight
over the sequences satisfying the per-edge parent incompatibility for `T`.  The spanning
trees of `incompat ω` are spanning trees of the complete graph, so the two sums swap;
the inner constraint is then relaxed by #4096. -/
theorem penroseTreeSum_le_subtype_parentConstraint (G : SimpleGraph ι) [Fintype G.edgeSet]
    (n : ℕ) (W : (Fin (n + 1) → Finset (Sym2 ι)) → ℝ) (hW : ∀ ω, 0 ≤ W ω) :
    (∑ ω ∈ Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G),
        ∑ _T ∈ Penrose.spanningTreeEdgeSubsets (polymerSeqIncompatibilityGraph ω), W ω)
      ≤ ∑ T : {S : Finset (Sym2 (Fin (n + 1))) //
            S ∈ Penrose.spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1)))},
          ∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
            (fun ω => ∀ i : Fin n, PolymersIncompatible (ω (Fin.succ i))
              (ω (Penrose.completeGraphTreeParentCode n T i))), W ω := by
  classical
  set P := Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G) with hP
  -- Rewrite each inner spanning-tree sum as a subtype sum over complete-graph trees.
  have hinner : ∀ ω, (∑ _T ∈ Penrose.spanningTreeEdgeSubsets
        (polymerSeqIncompatibilityGraph ω), W ω)
      = ∑ T : {S : Finset (Sym2 (Fin (n + 1))) //
            S ∈ Penrose.spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1)))},
          (if T.1 ∈ Penrose.spanningTreeEdgeSubsets (polymerSeqIncompatibilityGraph ω) then
            W ω else 0) := by
    intro ω
    rw [Finset.sum_coe_sort
      (Penrose.spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1))))
      (fun S => if S ∈ Penrose.spanningTreeEdgeSubsets (polymerSeqIncompatibilityGraph ω) then
        W ω else 0),
      ← Finset.sum_filter, Finset.filter_mem_eq_inter,
      Finset.inter_eq_right.mpr (Penrose.spanningTreeEdgeSubsets_mono le_top)]
  calc
    (∑ ω ∈ P, ∑ _T ∈ Penrose.spanningTreeEdgeSubsets (polymerSeqIncompatibilityGraph ω), W ω)
        = ∑ ω ∈ P, ∑ T : {S // S ∈ Penrose.spanningTreeEdgeSubsets
              (⊤ : SimpleGraph (Fin (n + 1)))},
            (if T.1 ∈ Penrose.spanningTreeEdgeSubsets (polymerSeqIncompatibilityGraph ω) then
              W ω else 0) := Finset.sum_congr rfl fun ω _ => hinner ω
    _ = ∑ T : {S // S ∈ Penrose.spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1)))},
          ∑ ω ∈ P,
            (if T.1 ∈ Penrose.spanningTreeEdgeSubsets (polymerSeqIncompatibilityGraph ω) then
              W ω else 0) := Finset.sum_comm
    _ = ∑ T : {S // S ∈ Penrose.spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1)))},
          ∑ ω ∈ P.filter (fun ω =>
            T.1 ∈ Penrose.spanningTreeEdgeSubsets (polymerSeqIncompatibilityGraph ω)), W ω :=
          Finset.sum_congr rfl fun T _ => (Finset.sum_filter _ _).symm
    _ ≤ ∑ T : {S // S ∈ Penrose.spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1)))},
          ∑ ω ∈ P.filter (fun ω => ∀ i : Fin n, PolymersIncompatible (ω (Fin.succ i))
            (ω (Penrose.completeGraphTreeParentCode n T i))), W ω :=
          Finset.sum_le_sum fun T _ =>
            sum_filter_treeIncompat_le_filter_parentConstraint n T P W hW

end IsingModel

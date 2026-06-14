import IsingModel.ClusterExpansion.Penrose.PartitionScheme

/-!
# Kruskal forest preserves reachability (GJ §18.4-18.5, Issue #3954)

Connectivity half of the Kruskal correctness of `treeOf` (PR 3a toward the Penrose
tree-graph inequality).  The Kruskal spanning forest `treeOf S` keeps exactly the
edges that join previously-unjoined endpoints, so it **preserves reachability**:
`(fromEdgeSet ↑(treeOf S)).Reachable a b ↔ (fromEdgeSet ↑S).Reachable a b`.  Hence
`treeOf S` is connected whenever `S` is.

The core is a strong induction over the edge order (the well-founded order pulled
back from `V ×ₗ V` along `edgeKey`): every edge of `S` has `treeOf S`-reachable
endpoints, because a dropped edge `e` (with `reachableLT S e`) has its endpoints
joined by strictly-smaller edges of `S`, each of which — inductively — has
`treeOf S`-reachable endpoints.

Acyclicity, the `|V| - 1` edge count, and the headline
`treeOf_mem_spanningTreeEdgeSubsets` follow in a later PR.

## References
- Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.4–18.5, pp. 378–386.
- Friedli–Velenik, *Statistical Mechanics of Lattice Systems*, §5.7.
-/

namespace IsingModel.Penrose

open Finset SimpleGraph

variable {V : Type*} [LinearOrder V]

/-- **Strict lower edge-prefix** `edgesLT X e`: the edges of `X` strictly below `e`
in the edge order (`edgeKey f < edgeKey e`). -/
def edgesLT (X : Finset (Sym2 V)) (e : Sym2 V) : Finset (Sym2 V) :=
  X.filter (fun f => edgeKey f < edgeKey e)

/-- **Membership in `edgesLT`**: `f ∈ edgesLT X e` iff `f ∈ X` and `edgeKey f < edgeKey e`. -/
theorem mem_edgesLT {X : Finset (Sym2 V)} {e f : Sym2 V} :
    f ∈ edgesLT X e ↔ f ∈ X ∧ edgeKey f < edgeKey e := by
  simp only [edgesLT, Finset.mem_filter]

/-- **Unfolding `reachableLT` on an explicit edge**: `reachableLT X s(a, b)` holds iff
the endpoints `a, b` are reachable within the graph spanned by `edgesLT X s(a, b)`. -/
theorem reachableLT_iff_edgesLT (X : Finset (Sym2 V)) (a b : V) :
    reachableLT X s(a, b) ↔
      (fromEdgeSet (↑(edgesLT X s(a, b)) : Set (Sym2 V))).Reachable a b := by
  simp only [reachableLT, liftSym2Prop, Sym2.lift_mk, edgesLT]

omit [LinearOrder V] in
/-- **Reachability transport along edgewise-reachability**: if every edge of `S` has
`fromEdgeSet ↑T`-reachable endpoints, then reachability in `fromEdgeSet ↑S` descends
to `fromEdgeSet ↑T`.  Proved by `ReflTransGen` induction on the reachability witness. -/
theorem reachable_mono_of_edges_reachable {S T : Finset (Sym2 V)}
    (h : ∀ a b, s(a, b) ∈ S → (fromEdgeSet (↑T : Set (Sym2 V))).Reachable a b) {a b : V}
    (hab : (fromEdgeSet (↑S : Set (Sym2 V))).Reachable a b) :
    (fromEdgeSet (↑T : Set (Sym2 V))).Reachable a b := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hab
  induction hab with
  | refl => exact Reachable.refl _
  | @tail u v _ hadj ih =>
      rw [fromEdgeSet_adj] at hadj
      exact ih.trans (h u v (Finset.mem_coe.mp hadj.1))

variable [Finite V]

/-- **The edge order is well-founded**: the strict edge order `edgeKey f < edgeKey e`
is well-founded, being pulled back along `edgeKey` from the finite linear order
`V ×ₗ V`. -/
theorem wellFounded_edgeKey_lt :
    WellFounded (fun f e : Sym2 V => edgeKey f < edgeKey e) :=
  InvImage.wf edgeKey wellFounded_lt

/-- **Every edge of `S` has `treeOf S`-reachable endpoints** (the Kruskal key lemma):
by strong induction over the edge order.  A kept edge gives a direct adjacency; a
dropped edge `e` (with `reachableLT S e`) has its endpoints joined by strictly-smaller
edges of `S`, each `treeOf S`-reachable by the induction hypothesis, so the transport
lemma closes it. -/
theorem reachable_endpoints_of_mem_treeOf {S : Finset (Sym2 V)} :
    ∀ a b, s(a, b) ∈ S → (fromEdgeSet (↑(treeOf S) : Set (Sym2 V))).Reachable a b := by
  have key : ∀ e : Sym2 V, ∀ a b, e = s(a, b) → s(a, b) ∈ S →
      (fromEdgeSet (↑(treeOf S) : Set (Sym2 V))).Reachable a b := by
    intro e
    refine WellFounded.induction
      (C := fun e => ∀ a b, e = s(a, b) → s(a, b) ∈ S →
        (fromEdgeSet (↑(treeOf S) : Set (Sym2 V))).Reachable a b)
      wellFounded_edgeKey_lt e ?_
    intro e IH a b hab hmem
    subst hab
    by_cases hdiag : a = b
    · subst hdiag; exact Reachable.refl _
    by_cases hlt : reachableLT S s(a, b)
    · rw [reachableLT_iff_edgesLT] at hlt
      refine reachable_mono_of_edges_reachable (T := treeOf S) ?_ hlt
      intro x y hxy
      rw [mem_edgesLT] at hxy
      exact IH s(x, y) hxy.2 x y rfl hxy.1
    · have hmemTree : s(a, b) ∈ treeOf S := mem_treeOf.mpr ⟨hmem, hlt⟩
      refine Adj.reachable ?_
      rw [fromEdgeSet_adj]
      exact ⟨Finset.mem_coe.mpr hmemTree, hdiag⟩
  intro a b hmem
  exact key s(a, b) a b rfl hmem

/-- **Global reachability equivalence**: `treeOf S` and `S` have the same reachability
relation.  The forward direction is monotonicity (`treeOf S ⊆ S`); the converse is the
Kruskal key lemma via the transport lemma. -/
theorem reachable_treeOf_iff_reachable {S : Finset (Sym2 V)} {a b : V} :
    (fromEdgeSet (↑(treeOf S) : Set (Sym2 V))).Reachable a b ↔
      (fromEdgeSet (↑S : Set (Sym2 V))).Reachable a b := by
  constructor
  · intro h
    exact h.mono (fromEdgeSet_mono (Finset.coe_subset.mpr (treeOf_subset S)))
  · intro h
    exact reachable_mono_of_edges_reachable reachable_endpoints_of_mem_treeOf h

/-- **`treeOf S` is connected when `S` is**: reachability is preserved, so the
preconnectedness of `S` transfers (the vertex set is unchanged). -/
theorem connected_treeOf_of_connected {S : Finset (Sym2 V)}
    (hS : (fromEdgeSet (↑S : Set (Sym2 V))).Connected) :
    (fromEdgeSet (↑(treeOf S) : Set (Sym2 V))).Connected := by
  haveI := hS.nonempty
  exact ⟨fun u v => reachable_treeOf_iff_reachable.mpr (hS.preconnected u v)⟩

omit [Finite V] in
/-- **The edge finset of the Kruskal forest is `treeOf S`**: when `S ⊆ G.edgeFinset`
(so `treeOf S` is diagonal-free), reconstructing the graph from `treeOf S` and reading
off its edges recovers `treeOf S`. -/
theorem edgeFinset_fromEdgeSet_treeOf [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {S : Finset (Sym2 V)} (hS : S ⊆ G.edgeFinset) :
    (fromEdgeSet (↑(treeOf S) : Set (Sym2 V))).edgeFinset = treeOf S := by
  ext e
  rw [SimpleGraph.mem_edgeFinset, edgeSet_fromEdgeSet, Set.mem_diff, Finset.mem_coe]
  constructor
  · exact fun h => h.1
  · refine fun he => ⟨he, ?_⟩
    have hmem : e ∈ G.edgeFinset := treeOf_subset_edgeFinset hS he
    rw [SimpleGraph.mem_edgeFinset] at hmem
    exact fun hdiag => G.not_isDiag_of_mem_edgeSet hmem (Sym2.mem_diagSet.mp hdiag)

end IsingModel.Penrose

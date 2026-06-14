import IsingModel.ClusterExpansion.Penrose.SpanningTree
import Mathlib.Data.Sym.Sym2.Order
import Mathlib.Data.Prod.Lex

/-!
# Penrose partition scheme: `treeOf` and `addable` (GJ §18.4-18.5, Issue #3954)

The genuine combinatorial core of the from-scratch Penrose tree-graph inequality
`|alternatingConnectedSubgraphSum G| ≤ numSpanningTrees G`.  We build the Penrose
partition-scheme **data** by the edge-order Kruskal / reachability construction,
with **no hypothesis structures** (the earlier `PenrosePartitionScheme`-reduction
chain was deleted).

Fix a linear order on the edges `Sym2 V` (induced from `[LinearOrder V]` via
`Sym2.sortEquiv`).  For an edge-subset `S`:

* `treeOf S` keeps an edge `e ∈ S` iff `e`'s endpoints are **not** already joined by
  the strictly-smaller kept edges of `S` — the Kruskal minimum spanning forest.
* `addable G T` collects the non-`T` edges `e` of `G` whose endpoints **are**
  joined by the strictly-smaller edges of `T` (so `e` is the maximum edge of the
  fundamental cycle it forms with `T`) — the edges freely addable to `T` inside
  its Boolean interval.

This PR establishes the definitions and their basic structural lemmas
(`treeOf S ⊆ S`, `addable` disjoint from / contained in the edges).  The Kruskal
correctness (`treeOf S` is a spanning tree) and the interval-partition property
follow in later PRs.

## References
- Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.4–18.5, pp. 378–386.
- Friedli–Velenik, *Statistical Mechanics of Lattice Systems*, §5.7.
- Penrose tree-graph inequality (Brydges' lectures).
-/

namespace IsingModel.Penrose

open Finset SimpleGraph

variable {V : Type*}

/-- **Symmetric binary predicate lifted to edges**: a relation `P` on vertices that
is symmetric descends to a predicate on `Sym2 V` (the unordered endpoint pair). -/
def liftSym2Prop (P : V → V → Prop) (hsym : ∀ a b, P a b ↔ P b a) : Sym2 V → Prop :=
  Sym2.lift ⟨P, fun a b => propext (hsym a b)⟩

/-- **Evaluation of `liftSym2Prop` on an explicit edge** `s(a, b)` is `P a b`. -/
@[simp]
theorem liftSym2Prop_mk (P : V → V → Prop) (hsym : ∀ a b, P a b ↔ P b a) (a b : V) :
    liftSym2Prop P hsym s(a, b) = P a b := rfl

/-- **The lexicographic linear order on edges** `Sym2 V` induced from `[LinearOrder V]`:
each edge is sorted into an ordered pair (`Sym2.sortEquiv`) and compared
lexicographically.  Provided as a `def` (not a global instance) to avoid an orphan
instance on the mathlib type `Sym2 V`; callers install it locally with `letI`. -/
@[reducible]
noncomputable def sym2LexLinearOrder (V : Type*) [LinearOrder V] : LinearOrder (Sym2 V) :=
  LinearOrder.lift'
    (fun e : Sym2 V => (toLex (Sym2.sortEquiv e : { p : V × V // p.1 ≤ p.2 }).val : V ×ₗ V))
    (fun _ _ hab => Sym2.sortEquiv.injective (Subtype.ext (toLex.injective hab)))

/-- **Strict-prefix reachability of an edge's endpoints**: for an edge-subset `X` and
an edge `e`, `reachableLT X e` holds iff the endpoints of `e` are joined within the
graph spanned by the edges of `X` strictly below `e` (in the `sym2LexLinearOrder`).
This is the Kruskal "already-connected" test: `e` is redundant in `X` iff
`reachableLT X e`.  Symmetric in the endpoints, so it descends to `Sym2 V`. -/
noncomputable def reachableLT [LinearOrder V] (X : Finset (Sym2 V)) (e : Sym2 V) : Prop := by
  classical
  letI : LinearOrder (Sym2 V) := sym2LexLinearOrder V
  exact
    liftSym2Prop
      (fun a b =>
        (SimpleGraph.fromEdgeSet (↑(X.filter (fun f : Sym2 V => f < e)) : Set (Sym2 V))).Reachable
          a b)
      (fun _ _ => ⟨fun h => h.symm, fun h => h.symm⟩) e

/-- **Kruskal spanning forest** `treeOf S` of an edge-subset `S`: keep the edges of
`S` whose endpoints are not already joined by the strictly-smaller kept edges. -/
noncomputable def treeOf [LinearOrder V] (S : Finset (Sym2 V)) : Finset (Sym2 V) := by
  classical
  exact S.filter (fun e => ¬ reachableLT S e)

/-- **Addable edges** `addable G T` of an edge-subset `T`: the edges `e` of `G` not in
`T` whose endpoints are already joined by the strictly-smaller edges of `T` (i.e. `e`
is the maximum edge of the fundamental cycle it forms with `T`).  These are exactly
the edges freely addable to a spanning tree `T` without changing `treeOf`. -/
noncomputable def addable [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset (Sym2 V)) : Finset (Sym2 V) := by
  classical
  exact G.edgeFinset.filter (fun e => e ∉ T ∧ reachableLT T e)

variable [LinearOrder V]

/-- **Membership in `treeOf`**: `e ∈ treeOf S` iff `e ∈ S` and `e`'s endpoints are not
joined by the strictly-smaller edges of `S`. -/
theorem mem_treeOf {S : Finset (Sym2 V)} {e : Sym2 V} :
    e ∈ treeOf S ↔ e ∈ S ∧ ¬ reachableLT S e := by
  classical
  simp only [treeOf, Finset.mem_filter]

/-- **`treeOf S` is a sub-edge-set of `S`**. -/
theorem treeOf_subset (S : Finset (Sym2 V)) : treeOf S ⊆ S := by
  intro e he
  exact (mem_treeOf.mp he).1

/-- **`treeOf S` stays within the edges of `G`** when `S` does. -/
theorem treeOf_subset_edgeFinset [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {S : Finset (Sym2 V)} (hS : S ⊆ G.edgeFinset) :
    treeOf S ⊆ G.edgeFinset :=
  (treeOf_subset S).trans hS

/-- **Membership in `addable`**: `e ∈ addable G T` iff `e` is an edge of `G`, not in
`T`, with endpoints joined by the strictly-smaller edges of `T`. -/
theorem mem_addable [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {T : Finset (Sym2 V)} {e : Sym2 V} :
    e ∈ addable G T ↔ e ∈ G.edgeFinset ∧ e ∉ T ∧ reachableLT T e := by
  classical
  simp only [addable, Finset.mem_filter]

/-- **Addable edges are edges of `G`**. -/
theorem addable_subset_edges [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (T : Finset (Sym2 V)) : addable G T ⊆ G.edgeFinset := by
  intro e he
  exact (mem_addable.mp he).1

/-- **Addable edges are disjoint from `T`**: by construction `addable G T` excludes
edges of `T`. -/
theorem addable_disjoint [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (T : Finset (Sym2 V)) : Disjoint T (addable G T) := by
  rw [Finset.disjoint_right]
  intro e he heT
  exact (mem_addable.mp he).2.1 heT

end IsingModel.Penrose

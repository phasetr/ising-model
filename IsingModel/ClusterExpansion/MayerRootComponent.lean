import IsingModel.ClusterExpansion.AlternatingCompleteGraph

/-!
# Mayer K_n root-component recurrence — root-component vertex set (GJ §18.4)

Foundations for the root-component bijection
`D_n = ∑_{C ∋ 0} c_{|C|} D_{n-|C|}` underlying the Mayer Phase B identity
`alternatingConnectedSubgraphSum K_n = (-1)^(n-1)(n-1)!` (#1499).

For an edge-subset `S`, `rootComponentFinset S r` is the vertex set of the
connected component of the root `r` in `fromEdgeSet ↑S`. This section sets up the
component-membership characterisation and the crossing-edge-free property used to
split `S` into its within-component and outside-component parts.
-/

namespace IsingModel

open Finset

open Classical in
/-- **Root-component vertex set**: the vertices in the connected component of `r`
in `fromEdgeSet ↑S`, i.e. `{v | C_S(v) = C_S(r)}`. The component `C` of vertex `0`
in the root-component decomposition of `S`. -/
noncomputable def rootComponentFinset {V : Type*} [Fintype V]
    (S : Finset (Sym2 V)) (r : V) : Finset V :=
  Finset.univ.filter (fun v =>
    (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 V))).connectedComponentMk v
      = (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 V))).connectedComponentMk r)

/-- **Membership in `rootComponentFinset`**: `v ∈ rootComponentFinset S r` iff `v`
and `r` lie in the same connected component of `fromEdgeSet ↑S`. -/
theorem mem_rootComponentFinset {V : Type*} [Fintype V]
    {S : Finset (Sym2 V)} {r v : V} :
    v ∈ rootComponentFinset S r ↔
      (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 V))).connectedComponentMk v
        = (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 V))).connectedComponentMk r := by
  classical
  simp [rootComponentFinset]

/-- **The root lies in its own component**: `r ∈ rootComponentFinset S r`. -/
theorem self_mem_rootComponentFinset {V : Type*} [Fintype V]
    (S : Finset (Sym2 V)) (r : V) :
    r ∈ rootComponentFinset S r := by
  rw [mem_rootComponentFinset]

/-- **Crossing-edge-free property**: for an edge `s(a,b) ∈ S` (with `a ≠ b`), the
endpoints `a` and `b` lie in the root component together — either both in
`rootComponentFinset S r` or both outside. Hence no edge of `S` joins the root
component to its complement, which is what makes the root-component split of `S`
multiplicative. From `connectedComponentMk_eq_of_mem`. -/
theorem mem_rootComponentFinset_iff_of_mem_edge {V : Type*} [Fintype V]
    {S : Finset (Sym2 V)} {r a b : V} (hab : s(a, b) ∈ S) (hne : a ≠ b) :
    a ∈ rootComponentFinset S r ↔ b ∈ rootComponentFinset S r := by
  rw [mem_rootComponentFinset, mem_rootComponentFinset,
      connectedComponentMk_eq_of_mem hab hne]

/-- **Edge-count split by the root component**: for an edge-subset `S` of `K_n`
(every edge non-diagonal, `hS`), the number of edges of `S` whose endpoints both
lie in the root component `C = rootComponentFinset S r` (`e ∈ C.sym2`) plus the
number whose endpoints both lie outside `C` (`e ∈ Cᶜ.sym2`) equals `#S`. The
cardinality ingredient `|S| = |S_in| + |S_out|` of the multiplicative
root-component split: by the crossing-edge-free property
`mem_rootComponentFinset_iff_of_mem_edge`, an edge of `S` is either entirely
inside `C` or entirely outside, so `e ∈ Cᶜ.sym2 ↔ ¬ e ∈ C.sym2` on `S`, and
`Finset.card_filter_add_card_filter_not` applies. Uses `Finset.sym2`
(`s(a,b) ∈ C.sym2 ↔ a ∈ C ∧ b ∈ C`). -/
theorem rootComponent_edge_card_split {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset (Sym2 V)) (r : V) (hS : ∀ e ∈ S, ¬ e.IsDiag) :
    #(S.filter (· ∈ (rootComponentFinset S r).sym2))
        + #(S.filter (· ∈ (rootComponentFinset S r)ᶜ.sym2)) = #S := by
  classical
  have hiff : ∀ e ∈ S, (e ∈ (rootComponentFinset S r)ᶜ.sym2)
      ↔ ¬ (e ∈ (rootComponentFinset S r).sym2) := by
    intro e
    refine Sym2.ind (fun a b => ?_) e
    intro he
    have hne : a ≠ b := fun h => hS _ he (by rw [Sym2.mk_isDiag_iff]; exact h)
    rw [Finset.mk_mem_sym2_iff, Finset.mk_mem_sym2_iff, Finset.mem_compl,
        Finset.mem_compl, mem_rootComponentFinset_iff_of_mem_edge he hne]
    constructor
    · rintro ⟨_, hb⟩ ⟨_, hb'⟩; exact hb hb'
    · intro h; exact ⟨fun hb => h ⟨hb, hb⟩, fun hb => h ⟨hb, hb⟩⟩
  rw [Finset.filter_congr hiff]
  exact Finset.card_filter_add_card_filter_not (s := S) (· ∈ (rootComponentFinset S r).sym2)

/-- **`rootComponentFinset` is the support of the root's component**: as a set,
`↑(rootComponentFinset S r) = (fromEdgeSet ↑S).connectedComponentMk r).supp`. -/
theorem coe_rootComponentFinset {V : Type*} [Fintype V] (S : Finset (Sym2 V)) (r : V) :
    (↑(rootComponentFinset S r) : Set V)
      = ((SimpleGraph.fromEdgeSet (↑S : Set (Sym2 V))).connectedComponentMk r).supp := by
  ext v
  rw [Finset.mem_coe, mem_rootComponentFinset,
      SimpleGraph.ConnectedComponent.mem_supp_iff]

/-- **The inside edges induce the same graph on the root component as `S` does**:
on the vertex subset `C = rootComponentFinset S r`, the subgraph induced by the
within-`C` edges `S_in = S ∩ C.sym2` coincides with the subgraph induced by all of
`S` (the outside / crossing edges of `S` contribute no adjacency inside `C`). -/
theorem induce_fromEdgeSet_inside_eq {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset (Sym2 V)) (r : V) :
    (SimpleGraph.fromEdgeSet
        (↑(S.filter (· ∈ (rootComponentFinset S r).sym2)) : Set (Sym2 V))).induce
        (↑(rootComponentFinset S r) : Set V)
      = (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 V))).induce
        (↑(rootComponentFinset S r) : Set V) := by
  ext x y
  simp only [SimpleGraph.comap_adj, Function.Embedding.coe_subtype,
    SimpleGraph.fromEdgeSet_adj, Finset.mem_coe, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hmem, _⟩, hne⟩; exact ⟨hmem, hne⟩
  · rintro ⟨hmem, hne⟩
    refine ⟨⟨hmem, ?_⟩, hne⟩
    rw [Finset.mk_mem_sym2_iff]
    exact ⟨x.2, y.2⟩

/-- **Inside edges form a connected spanning subgraph on the root component**
(Mayer Phase B crux): for an edge-subset `S`, the within-component edges
`S_in = S ∩ C.sym2` (with `C = rootComponentFinset S r`) induce a *connected*
graph on `C`. Because `C` is exactly the connected component of `r` in
`fromEdgeSet ↑S` (`coe_rootComponentFinset`), the induced graph is the
component's `toSimpleGraph`, which is connected (`connected_toSimpleGraph`); and
the inside edges induce the same graph as `S` on `C` (`induce_fromEdgeSet_inside_eq`). -/
theorem induce_fromEdgeSet_inside_connected {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset (Sym2 V)) (r : V) :
    ((SimpleGraph.fromEdgeSet
        (↑(S.filter (· ∈ (rootComponentFinset S r).sym2)) : Set (Sym2 V))).induce
        (↑(rootComponentFinset S r) : Set V)).Connected := by
  rw [induce_fromEdgeSet_inside_eq, coe_rootComponentFinset]
  exact SimpleGraph.ConnectedComponent.connected_toSimpleGraph
    ((SimpleGraph.fromEdgeSet (↑S : Set (Sym2 V))).connectedComponentMk r)

end IsingModel

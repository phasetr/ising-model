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

/-- **Reachability stays inside the root component when no edge crosses it**: if
every edge of `S` lies entirely inside `C` or entirely outside `C` (no crossing
edge, `hcross`) and the root `r ∈ C`, then any vertex `v` reachable from `r` in
`fromEdgeSet ↑S` lies in `C`. The backward half of the fiber characterisation
(`component of r = C`): with no crossing edge, a walk from `r` can never leave
`C`. Proved by `Relation.ReflTransGen` induction on the reachability witness via
`reachable_iff_reflTransGen`; each step's edge is inside `C` (so the new endpoint
stays in `C`) or inside `Cᶜ` (impossible, as the previous endpoint is in `C`). -/
theorem reachable_stays_in_of_no_cross {V : Type*} [Fintype V] [DecidableEq V]
    {S : Finset (Sym2 V)} {C : Finset V} {r : V} (hr : r ∈ C)
    (hcross : ∀ e ∈ S, e ∈ C.sym2 ∨ e ∈ Cᶜ.sym2) {v : V}
    (h : (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 V))).Reachable r v) : v ∈ C := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact hr
  | @tail b c _ hadj ih =>
    rw [SimpleGraph.fromEdgeSet_adj] at hadj
    obtain ⟨hmem, _⟩ := hadj
    rcases hcross _ (Finset.mem_coe.mp hmem) with hin | hout
    · rw [Finset.mk_mem_sym2_iff] at hin
      exact hin.2
    · rw [Finset.mk_mem_sym2_iff, Finset.mem_compl, Finset.mem_compl] at hout
      exact absurd ih hout.1

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

/-- **Fiber characterisation of the root component**: `rootComponentFinset S r = C`
iff (i) the root `r ∈ C`, (ii) no edge of `S` crosses `C` (every edge lies in
`C.sym2` or in `Cᶜ.sym2`), and (iii) the within-`C` edges `S ∩ C.sym2` induce a
connected graph on `C`. This exactly describes the fibre of the
root-component map over a fixed vertex set `C` (with `r ∈ C`): the spanning
edge-subsets whose component of `r` equals `C`. Forward direction packages
`self_mem_rootComponentFinset`, `mem_rootComponentFinset_iff_of_mem_edge`, and the
crux `induce_fromEdgeSet_inside_connected`; backward direction uses
`reachable_stays_in_of_no_cross` (component stays inside `C`) and maps the inside
connectivity into ambient reachability (`Reachable.map` along the subtype
inclusion, then monotonicity to all of `S`). -/
theorem rootComponentFinset_eq_iff {V : Type*} [Fintype V] [DecidableEq V]
    {S : Finset (Sym2 V)} {C : Finset V} {r : V} :
    rootComponentFinset S r = C ↔
      r ∈ C
        ∧ (∀ e ∈ S, e ∈ C.sym2 ∨ e ∈ Cᶜ.sym2)
        ∧ ((SimpleGraph.fromEdgeSet
              (↑(S.filter (· ∈ C.sym2)) : Set (Sym2 V))).induce (↑C : Set V)).Connected := by
  constructor
  · intro hC
    refine ⟨hC ▸ self_mem_rootComponentFinset S r, ?_, hC ▸ induce_fromEdgeSet_inside_connected S r⟩
    intro e he
    revert he
    refine Sym2.ind (fun a b he => ?_) e
    have hiff : a ∈ C ↔ b ∈ C := by
      by_cases hab : a = b
      · subst hab; exact Iff.rfl
      · rw [← hC, mem_rootComponentFinset_iff_of_mem_edge he hab]
    by_cases ha : a ∈ C
    · left
      rw [Finset.mk_mem_sym2_iff]
      exact ⟨ha, hiff.mp ha⟩
    · right
      rw [Finset.mk_mem_sym2_iff]
      exact ⟨Finset.mem_compl.mpr ha, Finset.mem_compl.mpr (fun hb => ha (hiff.mpr hb))⟩
  · rintro ⟨hr, hcross, hconn⟩
    ext v
    rw [mem_rootComponentFinset, SimpleGraph.ConnectedComponent.eq]
    constructor
    · intro hreach
      exact reachable_stays_in_of_no_cross hr hcross hreach.symm
    · intro hv
      have hsub : (S.filter (· ∈ C.sym2) : Finset (Sym2 V)) ⊆ S := Finset.filter_subset _ _
      have hle : SimpleGraph.fromEdgeSet (↑(S.filter (· ∈ C.sym2)) : Set (Sym2 V))
          ≤ SimpleGraph.fromEdgeSet (↑S : Set (Sym2 V)) :=
        SimpleGraph.fromEdgeSet_mono (by exact_mod_cast hsub)
      have h := (hconn.preconnected ⟨r, hr⟩ ⟨v, hv⟩).map
        ({ toFun := Subtype.val, map_rel' := fun {_ _} h => h } :
          (SimpleGraph.fromEdgeSet
              (↑(S.filter (· ∈ C.sym2)) : Set (Sym2 V))).induce (↑C : Set V)
            →g SimpleGraph.fromEdgeSet (↑(S.filter (· ∈ C.sym2)) : Set (Sym2 V)))
      simp only [RelHom.coeFn_mk] at h
      exact ((h.mono hle).symm)

/-- **`C.sym2` and `Cᶜ.sym2` are disjoint**: no `Sym2` lies in both, since an
edge inside `C` has both endpoints in `C` while one inside `Cᶜ` has both outside.
The vertex-level partition `C ⊔ Cᶜ` makes the inside/outside edge split a genuine
partition of any crossing-free edge-subset. -/
theorem mem_sym2_and_compl_sym2_false {V : Type*} [Fintype V] [DecidableEq V]
    {C : Finset V} {e : Sym2 V} (h1 : e ∈ C.sym2) (h2 : e ∈ Cᶜ.sym2) : False := by
  revert h1 h2
  refine Sym2.ind (fun a b h1 h2 => ?_) e
  rw [Finset.mk_mem_sym2_iff] at h1
  rw [Finset.mk_mem_sym2_iff, Finset.mem_compl, Finset.mem_compl] at h2
  exact h2.1 h1.1

open Classical in
/-- **Inside connected-spanning edge-subsets** of `G` over a vertex set `C`: the
subsets `A ⊆ E(G)` whose edges all lie in `C.sym2` and whose `fromEdgeSet`
restricted to `C` is connected. The ambient analogue (living in `Sym2 V`) of the
connected-spanning edge-subsets of the complete graph on `C`; it is the inside
factor of the root-component fibre split. -/
noncomputable def insideConnectedEdgeSubsets {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset V) : Finset (Finset (Sym2 V)) :=
  G.edgeFinset.powerset.filter (fun A => A ⊆ C.sym2
    ∧ ((SimpleGraph.fromEdgeSet (↑A : Set (Sym2 V))).induce (↑C : Set V)).Connected)

open Classical in
/-- **Outside edge-subsets** of `G` over a vertex set `C`: the subsets `B ⊆ E(G)`
whose edges all lie in `Cᶜ.sym2` (entirely outside `C`). The ambient analogue of
all spanning edge-subsets of the complete graph on `Cᶜ`; the outside factor of the
root-component fibre split. -/
noncomputable def outsideEdgeSubsets {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset V) : Finset (Finset (Sym2 V)) :=
  G.edgeFinset.powerset.filter (fun B => B ⊆ Cᶜ.sym2)

/-- **Membership in `insideConnectedEdgeSubsets`**. -/
theorem mem_insideConnectedEdgeSubsets {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {C : Finset V} {A : Finset (Sym2 V)} :
    A ∈ insideConnectedEdgeSubsets G C ↔ A ⊆ G.edgeFinset ∧ A ⊆ C.sym2
      ∧ ((SimpleGraph.fromEdgeSet (↑A : Set (Sym2 V))).induce (↑C : Set V)).Connected := by
  classical
  rw [insideConnectedEdgeSubsets, Finset.mem_filter, Finset.mem_powerset]

/-- **Membership in `outsideEdgeSubsets`**. -/
theorem mem_outsideEdgeSubsets {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {C : Finset V} {B : Finset (Sym2 V)} :
    B ∈ outsideEdgeSubsets G C ↔ B ⊆ G.edgeFinset ∧ B ⊆ Cᶜ.sym2 := by
  classical
  rw [outsideEdgeSubsets, Finset.mem_filter, Finset.mem_powerset]

/-- **Root-component fibre signed sum factorises as a product** (Mayer Phase B
lemma 6): for a fixed vertex set `C` containing the root `r`, the signed sum
`∑ (-1)^|S|` over edge-subsets `S ⊆ E(G)` whose root component equals `C` factors
as the product of the inside connected-spanning signed sum (over `C`) and the
outside signed sum (over `Cᶜ`). Proved by the crossing-free bijection
`S ↦ (S ∩ C.sym2, S ∩ Cᶜ.sym2)` with inverse `(A, B) ↦ A ∪ B`
(`Finset.sum_bij'`): the fibre characterisation `rootComponentFinset_eq_iff`
supplies both membership directions, disjointness `mem_sym2_and_compl_sym2_false`
makes the split a partition, and `rootComponent_edge_card_split` gives
`|S| = |A| + |B|`, so `(-1)^|S| = (-1)^|A|·(-1)^|B|`. The ambient core of the
recurrence `D_n = ∑_{C ∋ 0} c_{|C|} D_{n-|C|}`. -/
theorem fiber_signed_sum_eq_product {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {C : Finset V} {r : V} (hrC : r ∈ C) :
    ∑ S ∈ G.edgeFinset.powerset.filter (fun S => rootComponentFinset S r = C),
        (-1 : ℝ) ^ S.card
      = (∑ A ∈ insideConnectedEdgeSubsets G C, (-1 : ℝ) ^ A.card)
        * (∑ B ∈ outsideEdgeSubsets G C, (-1 : ℝ) ^ B.card) := by
  classical
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_bij'
    (fun S _ => (S.filter (· ∈ C.sym2), S.filter (· ∈ Cᶜ.sym2)))
    (fun p _ => p.1 ∪ p.2) ?_ ?_ ?_ ?_ ?_
  · -- i maps the fibre into inside ×ˢ outside
    intro S hS
    rw [Finset.mem_filter, Finset.mem_powerset] at hS
    obtain ⟨hSsub, hSroot⟩ := hS
    obtain ⟨_, _, hconn⟩ := rootComponentFinset_eq_iff.mp hSroot
    rw [Finset.mem_product]
    refine ⟨mem_insideConnectedEdgeSubsets.mpr ⟨?_, ?_, hconn⟩,
      mem_outsideEdgeSubsets.mpr ⟨?_, ?_⟩⟩
    · exact (Finset.filter_subset _ _).trans hSsub
    · intro e he; exact (Finset.mem_filter.mp he).2
    · exact (Finset.filter_subset _ _).trans hSsub
    · intro e he; exact (Finset.mem_filter.mp he).2
  · -- j maps inside ×ˢ outside into the fibre
    intro p hp
    rw [Finset.mem_product] at hp
    obtain ⟨hA, hB⟩ := hp
    obtain ⟨hAsub, hAC, hAconn⟩ := mem_insideConnectedEdgeSubsets.mp hA
    obtain ⟨hBsub, hBC⟩ := mem_outsideEdgeSubsets.mp hB
    have hfilter : (p.1 ∪ p.2).filter (· ∈ C.sym2) = p.1 := by
      rw [Finset.filter_union, Finset.filter_true_of_mem (fun e he => hAC he),
        Finset.filter_false_of_mem (fun e he h => mem_sym2_and_compl_sym2_false h (hBC he)),
        Finset.union_empty]
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.union_subset hAsub hBsub, rootComponentFinset_eq_iff.mpr ⟨hrC, ?_, ?_⟩⟩
    · intro e he
      rcases Finset.mem_union.mp he with h | h
      · exact Or.inl (hAC h)
      · exact Or.inr (hBC h)
    · rw [hfilter]; exact hAconn
  · -- left inverse: (S ∩ C.sym2) ∪ (S ∩ Cᶜ.sym2) = S
    intro S hS
    rw [Finset.mem_filter, Finset.mem_powerset] at hS
    obtain ⟨_, hcross, _⟩ := rootComponentFinset_eq_iff.mp hS.2
    ext e
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro he
      rcases hcross e he with h | h
      · exact Or.inl ⟨he, h⟩
      · exact Or.inr ⟨he, h⟩
  · -- right inverse: i (A ∪ B) = (A, B)
    intro p hp
    rw [Finset.mem_product] at hp
    obtain ⟨hA, hB⟩ := hp
    obtain ⟨_, hAC, _⟩ := mem_insideConnectedEdgeSubsets.mp hA
    obtain ⟨_, hBC⟩ := mem_outsideEdgeSubsets.mp hB
    have h1 : (p.1 ∪ p.2).filter (· ∈ C.sym2) = p.1 := by
      rw [Finset.filter_union, Finset.filter_true_of_mem (fun e he => hAC he),
        Finset.filter_false_of_mem (fun e he h => mem_sym2_and_compl_sym2_false h (hBC he)),
        Finset.union_empty]
    have h2 : (p.1 ∪ p.2).filter (· ∈ Cᶜ.sym2) = p.2 := by
      rw [Finset.filter_union,
        Finset.filter_false_of_mem (fun e he h => mem_sym2_and_compl_sym2_false (hAC he) h),
        Finset.filter_true_of_mem (fun e he => hBC he), Finset.empty_union]
    exact Prod.ext h1 h2
  · -- value: (-1)^|S| = (-1)^|S∩C.sym2| * (-1)^|S∩Cᶜ.sym2|
    intro S hS
    rw [Finset.mem_filter, Finset.mem_powerset] at hS
    obtain ⟨hSsub, hSroot⟩ := hS
    have hnondiag : ∀ e ∈ S, ¬ e.IsDiag := by
      intro e he
      have hes : e ∈ G.edgeSet := SimpleGraph.mem_edgeFinset.mp (hSsub he)
      revert hes
      refine Sym2.ind (fun a b hes => ?_) e
      rw [SimpleGraph.mem_edgeSet] at hes
      rw [Sym2.mk_isDiag_iff]
      exact G.ne_of_adj hes
    have hcard := rootComponent_edge_card_split S r hnondiag
    rw [hSroot] at hcard
    rw [← hcard, pow_add]

end IsingModel

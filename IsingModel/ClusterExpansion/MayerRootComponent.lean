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

/-- **Real-valued alternating powerset sum dichotomy**: `∑_{B ⊆ X} (-1)^|B|`
equals `1` if `X = ∅` and `0` otherwise. Real-cast of
`Finset.sum_powerset_neg_one_pow_card`. The signed sum over any full powerset is
determined entirely by whether the base set is empty — used to evaluate the
outside factor `D(K_{Cᶜ})` of the Mayer root-component recurrence. -/
theorem real_signed_sum_powerset {α : Type*} [DecidableEq α] (X : Finset α) :
    ∑ B ∈ X.powerset, (-1 : ℝ) ^ B.card = if X = ∅ then 1 else 0 := by
  have h := @Finset.sum_powerset_neg_one_pow_card α _ X
  have hcast : (∑ B ∈ X.powerset, (-1 : ℝ) ^ B.card)
      = (((∑ B ∈ X.powerset, (-1 : ℤ) ^ B.card) : ℤ) : ℝ) := by
    push_cast; rfl
  rw [hcast, h]
  split <;> simp

/-- **`D(G)` dichotomy**: the signed all-subgraph sum is `1` if `G` is edgeless
and `0` otherwise. Restates `allSignedSubgraphSum` via `real_signed_sum_powerset`;
unifies `allSignedSubgraphSum_eq_one_of_edgeFinset_empty` and
`_eq_zero_of_edgeFinset_nonempty`. The outside factor of the root-component
recurrence is evaluated through this dichotomy. -/
theorem allSignedSubgraphSum_eq_ite {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    allSignedSubgraphSum G = if G.edgeFinset = ∅ then 1 else 0 := by
  unfold allSignedSubgraphSum
  exact real_signed_sum_powerset G.edgeFinset

/-- **All-subgraph signed sum as a fibrewise product sum** (Mayer Phase B lemma
7): the signed sum `D(G) = ∑_{S ⊆ E(G)} (-1)^|S|` over *all* spanning edge-subsets
equals the sum over vertex sets `C` containing the root `r` of the per-fibre
product `insideΣ(C) · outsideΣ(C)`. Obtained from `Finset.sum_fiberwise_of_maps_to`
applied to the root-component map `S ↦ rootComponentFinset S r` (which always
contains `r`, `self_mem_rootComponentFinset`), with each fibre evaluated by
`fiber_signed_sum_eq_product`. The ambient form of the root-component recurrence
`D_n = ∑_{C ∋ 0} c_{|C|} D_{n-|C|}` (GJ §18.4); the remaining step is the reindex
`insideΣ(C) = c(K_C)`, `outsideΣ(C) = D(K_{Cᶜ})`. -/
theorem allSignedSubgraphSum_eq_sum_fiber_product {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : V) :
    allSignedSubgraphSum G
      = ∑ C ∈ Finset.univ.powerset.filter (fun C : Finset V => r ∈ C),
          (∑ A ∈ insideConnectedEdgeSubsets G C, (-1 : ℝ) ^ A.card)
            * (∑ B ∈ outsideEdgeSubsets G C, (-1 : ℝ) ^ B.card) := by
  classical
  have hmaps : ∀ S ∈ G.edgeFinset.powerset,
      rootComponentFinset S r ∈ Finset.univ.powerset.filter (fun C : Finset V => r ∈ C) := by
    intro S _
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.subset_univ _, self_mem_rootComponentFinset S r⟩
  unfold allSignedSubgraphSum
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun S => (-1 : ℝ) ^ S.card)]
  refine Finset.sum_congr rfl (fun C hC => ?_)
  rw [Finset.mem_filter] at hC
  exact fiber_signed_sum_eq_product G hC.2

/-- **Outside factor is a plain powerset**: the outside edge-subsets of `G` over
`C` are exactly the subsets of `G.edgeFinset ∩ Cᶜ.sym2` (the edges of `G` lying
entirely outside `C`). No connectivity constraint — the outside factor of the
root-component split carries no spanning condition. -/
theorem outsideEdgeSubsets_eq_powerset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset V) :
    outsideEdgeSubsets G C = (G.edgeFinset ∩ Cᶜ.sym2).powerset := by
  classical
  ext B
  rw [mem_outsideEdgeSubsets, Finset.mem_powerset, Finset.subset_inter_iff]

/-- **Outside factor signed sum dichotomy**: the outside signed sum is `1` if `G`
has no edge entirely outside `C` (i.e. `G.edgeFinset ∩ Cᶜ.sym2 = ∅`) and `0`
otherwise. Combines `outsideEdgeSubsets_eq_powerset` with
`real_signed_sum_powerset`; this evaluates the outside factor `D(K_{Cᶜ})` of the
root-component recurrence directly in ambient terms. -/
theorem outsideEdgeSubsets_signed_sum_eq_ite {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset V) :
    ∑ B ∈ outsideEdgeSubsets G C, (-1 : ℝ) ^ B.card
      = if G.edgeFinset ∩ Cᶜ.sym2 = ∅ then 1 else 0 := by
  rw [outsideEdgeSubsets_eq_powerset, real_signed_sum_powerset]

/-- **No edge lies inside `Cᶜ` iff `Cᶜ` is a (sub)singleton**: for the complete
graph, `edgeFinset ∩ Cᶜ.sym2 = ∅` exactly when `Cᶜ.card ≤ 1`. An edge with both
endpoints in `Cᶜ` requires two distinct vertices in `Cᶜ`
(`Finset.one_lt_card_iff` / `Finset.card_le_one`). Evaluates the outside factor of
the root-component recurrence by the cardinality of the complement. -/
theorem completeGraph_edgeFinset_inter_compl_sym2_empty_iff {V : Type*} [Fintype V] [DecidableEq V]
    (C : Finset V) :
    (⊤ : SimpleGraph V).edgeFinset ∩ Cᶜ.sym2 = ∅ ↔ Cᶜ.card ≤ 1 := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  constructor
  · intro h
    by_contra hc
    rw [not_le, Finset.one_lt_card_iff] at hc
    obtain ⟨a, b, ha, hb, hab⟩ := hc
    refine h s(a, b) (Finset.mem_inter.mpr ⟨?_, Finset.mk_mem_sym2_iff.mpr ⟨ha, hb⟩⟩)
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.top_adj]
    exact hab
  · intro h e he
    rw [Finset.mem_inter] at he
    revert he
    refine Sym2.ind (fun a b => ?_) e
    rintro ⟨h1, h2⟩
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.top_adj] at h1
    rw [Finset.mk_mem_sym2_iff] at h2
    exact h1 (Finset.card_le_one.mp h a h2.1 b h2.2)

/-- **All-subgraph signed sum of a subtype complete graph by cardinality**: for
the complete graph on the subtype `↑(C : Finset V)`, `D(K_C) = 1` if `C.card ≤ 1`
and `0` otherwise. Routes `allSignedSubgraphSum_completeGraph_card` through `Fin`
and the boundary lemmas `allSignedSubgraphSum_completeGraph_eq_one_of_subsingleton`
/ `_eq_zero_of_two_le`. -/
theorem allSignedSubgraphSum_completeGraph_subtype_eq_ite {V : Type*} [DecidableEq V]
    (C : Finset V) :
    allSignedSubgraphSum (⊤ : SimpleGraph (C : Finset V)) = if C.card ≤ 1 then 1 else 0 := by
  classical
  rw [allSignedSubgraphSum_completeGraph_card]
  have hcard : Fintype.card (C : Finset V) = C.card := Fintype.card_coe C
  by_cases h : C.card ≤ 1
  · haveI : Subsingleton (Fin (Fintype.card (C : Finset V))) :=
      Fintype.card_le_one_iff_subsingleton.mp (by rw [Fintype.card_fin, hcard]; exact h)
    rw [allSignedSubgraphSum_completeGraph_eq_one_of_subsingleton, if_pos h]
  · rw [allSignedSubgraphSum_completeGraph_eq_zero_of_two_le (by rw [hcard]; omega), if_neg h]

/-- **Outside factor reindex** (Mayer Phase B, outside half of lemma 8): the
outside signed sum of the complete graph on `V` over `C` equals the all-subgraph
signed sum of the complete graph on the subtype `↑Cᶜ`, i.e. `outsideΣ(C) =
D(K_{Cᶜ})`. Both sides reduce to `if Cᶜ.card ≤ 1 then 1 else 0` — the outside
factor via `outsideEdgeSubsets_signed_sum_eq_ite` +
`completeGraph_edgeFinset_inter_compl_sym2_empty_iff`, and `D(K_{Cᶜ})` via
`allSignedSubgraphSum_completeGraph_subtype_eq_ite`. -/
theorem outsideEdgeSubsets_completeGraph_signed_sum {V : Type*} [Fintype V] [DecidableEq V]
    (C : Finset V) :
    ∑ B ∈ outsideEdgeSubsets (⊤ : SimpleGraph V) C, (-1 : ℝ) ^ B.card
      = allSignedSubgraphSum (⊤ : SimpleGraph (Cᶜ : Finset V)) := by
  rw [outsideEdgeSubsets_signed_sum_eq_ite, allSignedSubgraphSum_completeGraph_subtype_eq_ite]
  exact if_congr (completeGraph_edgeFinset_inter_compl_sym2_empty_iff C) rfl rfl

/-- **Reindexed inside edges induce the subtype graph**: for `T : Finset (Sym2 ↑C)`,
mapping `T` into `Sym2 V` by the subtype `sym2`-embedding and inducing back on `C`
recovers `fromEdgeSet ↑T` on `↑C`. The graph equality transferring connectivity
between the ambient inside factor and the subtype complete-graph connected-spanning
sum (inside half of the Mayer reindex). Proved by `ext`: an inside edge
`s(↑a, ↑b)` of `T.map e` corresponds to the edge `s(a, b)` of `T` (the embedding is
injective), and `↑a ≠ ↑b ↔ a ≠ b`. -/
theorem induce_fromEdgeSet_map_subtype {V : Type*}
    (C : Finset V) (T : Finset (Sym2 (C : Finset V))) :
    (SimpleGraph.fromEdgeSet
        (↑(T.map (Function.Embedding.subtype (· ∈ C)).sym2Map) : Set (Sym2 V))).induce
        (↑C : Set V)
      = SimpleGraph.fromEdgeSet (↑T : Set (Sym2 (C : Finset V))) := by
  ext a b
  simp only [SimpleGraph.comap_adj, Function.Embedding.coe_subtype,
    SimpleGraph.fromEdgeSet_adj, Finset.mem_coe, Finset.mem_map,
    Function.Embedding.sym2Map_apply, ne_eq]
  constructor
  · rintro ⟨⟨z, hz, hzeq⟩, hne⟩
    refine ⟨?_, fun h => hne (by rw [h])⟩
    revert hz hzeq
    refine Sym2.ind (fun p q hz hzeq => ?_) z
    rw [Sym2.map_mk] at hzeq
    rw [Sym2.eq_iff] at hzeq
    rcases hzeq with ⟨hp, hq⟩ | ⟨hp, hq⟩
    · have : p = a := Subtype.ext hp
      have : q = b := Subtype.ext hq
      subst_vars; exact hz
    · have : p = b := Subtype.ext hp
      have : q = a := Subtype.ext hq
      subst_vars; rw [Sym2.eq_swap]; exact hz
  · rintro ⟨hmem, hne⟩
    refine ⟨⟨s(a, b), hmem, by rw [Sym2.map_mk]⟩, fun h => hne (Subtype.ext h)⟩

/-- **Inside edges lie in the range of the subtype embedding**: for `A ⊆ C.sym2`
(every edge has both endpoints in `C`), each edge of `A` is `e z` for some
`z : Sym2 ↑C`, where `e` is the subtype `sym2`-embedding. (No non-diagonal
hypothesis is needed; the statement holds for diagonal pairs as well.) -/
theorem inside_mem_range_sym2Map {V : Type*}
    {C : Finset V} {A : Finset (Sym2 V)} (hAC : A ⊆ C.sym2) :
    ∀ x ∈ A, ∃ z : Sym2 (C : Finset V),
      (Function.Embedding.subtype (· ∈ C)).sym2Map z = x := by
  intro x hx
  revert hx
  refine Sym2.ind (fun p q hx => ?_) x
  have hpq := hAC hx
  rw [Finset.mk_mem_sym2_iff] at hpq
  exact ⟨s(⟨p, hpq.1⟩, ⟨q, hpq.2⟩), by
    rw [Function.Embedding.sym2Map_apply, Function.Embedding.coe_subtype, Sym2.map_mk]⟩

/-- **Preimage-then-map roundtrip for inside subsets**: for an inside subset
`A ⊆ C.sym2`, pulling `A` back along the subtype embedding and pushing forward
recovers `A` (since every edge of `A` is in the range of the embedding,
`inside_mem_range_sym2Map`). -/
theorem inside_preimage_map_eq {V : Type*}
    {C : Finset V} {A : Finset (Sym2 V)} (hAC : A ⊆ C.sym2) :
    (A.preimage (Function.Embedding.subtype (· ∈ C)).sym2Map
        (Function.Embedding.injective _).injOn).map
        (Function.Embedding.subtype (· ∈ C)).sym2Map = A := by
  ext x
  simp only [Finset.mem_map, Finset.mem_preimage]
  constructor
  · rintro ⟨z, hz, rfl⟩; exact hz
  · intro hx
    obtain ⟨z, hz⟩ := inside_mem_range_sym2Map hAC x hx
    exact ⟨z, hz ▸ hx, hz⟩

/-- **Inside factor reindex** (Mayer Phase B, inside half of lemma 8): the inside
connected-spanning signed sum of the complete graph on `V` over `C` equals the
connected-spanning signed sum of the complete graph on the subtype `↑C`, i.e.
`insideΣ(C) = c(K_C)`. Proved by the connectivity-preserving bijection
`T ↦ T.map e` / `A ↦ A.preimage e` (`Finset.sum_bij'`, `e` the subtype
`sym2`-embedding): connectivity transfers through the graph equality
`induce_fromEdgeSet_map_subtype`, membership through `inside_mem_range_sym2Map`,
and the roundtrips through `Finset.preimage_map` / `inside_preimage_map_eq`. -/
theorem insideConnectedEdgeSubsets_completeGraph_signed_sum {V : Type*} [Fintype V] [DecidableEq V]
    (C : Finset V) :
    ∑ A ∈ insideConnectedEdgeSubsets (⊤ : SimpleGraph V) C, (-1 : ℝ) ^ A.card
      = alternatingConnectedSubgraphSum (⊤ : SimpleGraph (C : Finset V)) := by
  classical
  unfold alternatingConnectedSubgraphSum
  refine Finset.sum_bij'
    (fun A _ => A.preimage (Function.Embedding.subtype (· ∈ C)).sym2Map
        (Function.Embedding.injective _).injOn)
    (fun T _ => T.map (Function.Embedding.subtype (· ∈ C)).sym2Map) ?_ ?_ ?_ ?_ ?_
  · -- i maps inside into connectedSpanning (⊤ : ↑C)
    intro A hA
    rw [mem_insideConnectedEdgeSubsets] at hA
    obtain ⟨hAedge, hAC, hAconn⟩ := hA
    rw [mem_connectedSpanningEdgeSubsets]
    refine ⟨?_, ?_⟩
    · intro z hz
      rw [Finset.mem_preimage] at hz
      revert hz
      refine Sym2.ind (fun p q => ?_) z
      intro hz
      rw [Function.Embedding.sym2Map_apply, Function.Embedding.coe_subtype, Sym2.map_mk] at hz
      have hedge := hAedge hz
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.top_adj] at hedge
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.top_adj]
      exact fun h => hedge (by rw [h])
    · rw [← induce_fromEdgeSet_map_subtype C, inside_preimage_map_eq hAC]
      exact hAconn
  · -- j maps connectedSpanning (⊤ : ↑C) into inside
    intro T hT
    rw [mem_connectedSpanningEdgeSubsets] at hT
    rw [mem_insideConnectedEdgeSubsets]
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rw [Finset.mem_map] at hx
      obtain ⟨z, hz, rfl⟩ := hx
      revert hz
      refine Sym2.ind (fun p q hz => ?_) z
      have hedge := hT.1 hz
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.top_adj] at hedge
      rw [Function.Embedding.sym2Map_apply, Function.Embedding.coe_subtype, Sym2.map_mk,
        SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.top_adj]
      exact fun h => hedge (Subtype.ext h)
    · intro x hx
      rw [Finset.mem_map] at hx
      obtain ⟨z, hz, rfl⟩ := hx
      revert hz
      refine Sym2.ind (fun p q _ => ?_) z
      rw [Function.Embedding.sym2Map_apply, Function.Embedding.coe_subtype, Sym2.map_mk,
        Finset.mk_mem_sym2_iff]
      exact ⟨p.2, q.2⟩
    · rw [induce_fromEdgeSet_map_subtype]
      exact hT.2
  · -- left inverse: (A.preimage e).map e = A
    intro A hA
    rw [mem_insideConnectedEdgeSubsets] at hA
    exact inside_preimage_map_eq hA.2.1
  · -- right inverse: (T.map e).preimage e = T
    intro T _
    exact Finset.preimage_map _ _
  · -- value: (-1)^|A| = (-1)^|A.preimage e|
    intro A hA
    rw [mem_insideConnectedEdgeSubsets] at hA
    rw [← Finset.card_map (Function.Embedding.subtype (· ∈ C)).sym2Map,
      inside_preimage_map_eq hA.2.1]

/-- **Root-component recurrence for the complete graph** (Mayer Phase B): the
signed all-subgraph sum of `K_n` decomposes over the root component `C ∋ r` as
`D_n = ∑_{C ∋ r} c(K_C) · D(K_{Cᶜ})`, i.e.
`D_n = ∑_{C ∋ 0} c_{|C|} D_{n-|C|}` once `c`, `D` are seen to depend only on the
cardinalities. Assembles the fibrewise decomposition
`allSignedSubgraphSum_eq_sum_fiber_product` (lemma 7) with the inside and outside
reindexes (`insideConnectedEdgeSubsets_completeGraph_signed_sum`,
`outsideEdgeSubsets_completeGraph_signed_sum`). The combinatorial core of the
Mayer identity `alternatingConnectedSubgraphSum K_n = (-1)^(n-1)(n-1)!` (GJ §18.4);
the remaining step is the collapse `D_m = 0` (`m ≥ 2`), `D_0 = D_1 = 1` to
`c_n + (n-1)c_{n-1} = 0`. -/
theorem allSignedSubgraphSum_completeGraph_root_recurrence {V : Type*} [Fintype V] [DecidableEq V]
    (r : V) :
    allSignedSubgraphSum (⊤ : SimpleGraph V)
      = ∑ C ∈ Finset.univ.powerset.filter (fun C : Finset V => r ∈ C),
          alternatingConnectedSubgraphSum (⊤ : SimpleGraph (C : Finset V))
            * allSignedSubgraphSum (⊤ : SimpleGraph (Cᶜ : Finset V)) := by
  rw [allSignedSubgraphSum_eq_sum_fiber_product (⊤ : SimpleGraph V) r]
  refine Finset.sum_congr rfl (fun C _ => ?_)
  rw [insideConnectedEdgeSubsets_completeGraph_signed_sum,
    outsideEdgeSubsets_completeGraph_signed_sum]

/-- **Surviving root-component sets**: in the recurrence over `K_n`, the vertex
sets `C` containing the root `0` whose complement has `≤ 1` element are exactly
`univ` (full set) together with the cofinite singletons `{j}ᶜ` for `j ≠ 0`. The
sets with `|Cᶜ| ≥ 2` contribute `0` (since `D(K_{Cᶜ}) = 0`), so only these survive
the collapse `D_n = c_n + (n-1)c_{n-1}`. -/
theorem mayer_surviving_set {n : ℕ} [NeZero n] :
    Finset.univ.powerset.filter
        (fun C : Finset (Fin n) => (0 : Fin n) ∈ C ∧ Cᶜ.card ≤ 1)
      = insert Finset.univ
          ((Finset.univ.erase (0 : Fin n)).image (fun j => ({j}ᶜ : Finset (Fin n)))) := by
  classical
  ext C
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and,
    Finset.mem_insert, Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true]
  constructor
  · rintro ⟨h0, hcard⟩
    by_cases hCc : Cᶜ = ∅
    · left
      rw [← compl_compl C, hCc, compl_empty]
    · right
      obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hCc
      have hCcj : Cᶜ = {j} := by
        apply Finset.Subset.antisymm
        · intro a ha
          rw [Finset.mem_singleton]
          exact Finset.card_le_one.mp hcard a ha j hj
        · rw [Finset.singleton_subset_iff]; exact hj
      refine ⟨j, fun h => (Finset.mem_compl.mp (h ▸ hj)) h0, ?_⟩
      rw [← compl_compl C, hCcj]
  · rintro (rfl | ⟨j, hj0, rfl⟩)
    · exact ⟨Finset.mem_univ 0, by rw [compl_univ]; simp⟩
    · refine ⟨?_, ?_⟩
      · rw [Finset.mem_compl, Finset.mem_singleton]
        exact fun h => hj0 h.symm
      · rw [compl_compl, Finset.card_singleton]

/-- **Mayer recurrence for the complete-graph connected-spanning sum**: for
`n ≥ 2`, `c_n + (n-1)·c_{n-1} = 0` where `c_m = alternatingConnectedSubgraphSum
(⊤ : SimpleGraph (Fin m))`. Collapses the root-component recurrence
`allSignedSubgraphSum_completeGraph_root_recurrence`: `D_n = ∑_{C ∋ 0} c(K_C)·D(K_{Cᶜ})`,
using `D(K_{Cᶜ}) = 0` unless `|Cᶜ| ≤ 1` (so only `C = univ` and the `n-1` cofinite
singletons `{j}ᶜ` survive, `mayer_surviving_set`), `c`'s cardinality-invariance,
and `D_n = 0` for `n ≥ 2`. The recurrence yielding the closed form
`c_n = (-1)^(n-1)(n-1)!`. -/
theorem alternatingConnectedSubgraphSum_completeGraph_recurrence {n : ℕ} (hn : 2 ≤ n) :
    alternatingConnectedSubgraphSum (⊤ : SimpleGraph (Fin n))
      + (↑(n - 1) : ℝ) * alternatingConnectedSubgraphSum (⊤ : SimpleGraph (Fin (n - 1))) = 0 := by
  classical
  haveI : NeZero n := ⟨by omega⟩
  have hrec := allSignedSubgraphSum_completeGraph_root_recurrence (V := Fin n) (0 : Fin n)
  rw [allSignedSubgraphSum_completeGraph_eq_zero_of_two_le hn] at hrec
  -- fold `D(K_Cᶜ)` into an `ite` and restrict to the surviving sets
  have key : ∀ C : Finset (Fin n),
      alternatingConnectedSubgraphSum (⊤ : SimpleGraph (C : Finset (Fin n)))
          * allSignedSubgraphSum (⊤ : SimpleGraph (Cᶜ : Finset (Fin n)))
        = if Cᶜ.card ≤ 1 then
            alternatingConnectedSubgraphSum (⊤ : SimpleGraph (C : Finset (Fin n))) else 0 := by
    intro C
    rw [allSignedSubgraphSum_completeGraph_subtype_eq_ite]
    split <;> simp
  simp_rw [key] at hrec
  rw [← Finset.sum_filter, Finset.filter_filter, mayer_surviving_set] at hrec
  -- the two surviving groups: `univ` and the cofinite singletons `{j}ᶜ`
  have hnotmem : (Finset.univ : Finset (Fin n)) ∉
      (Finset.univ.erase (0 : Fin n)).image (fun j => ({j}ᶜ : Finset (Fin n))) := by
    rw [Finset.mem_image]
    rintro ⟨j, _, hj⟩
    have : ({j} : Finset (Fin n)) = ∅ := by
      rw [← compl_compl ({j} : Finset (Fin n)), hj, compl_univ]
    simp at this
  have himinj : Set.InjOn (fun j => ({j}ᶜ : Finset (Fin n)))
      (Finset.univ.erase (0 : Fin n)) := by
    intro a _ b _ hab
    simpa using compl_injective hab
  rw [Finset.sum_insert hnotmem, Finset.sum_image himinj] at hrec
  -- evaluate the `univ` term as `c_n`
  have huniv : alternatingConnectedSubgraphSum (⊤ : SimpleGraph ((Finset.univ : Finset (Fin n)))) =
      alternatingConnectedSubgraphSum (⊤ : SimpleGraph (Fin n)) := by
    rw [alternatingConnectedSubgraphSum_completeGraph_card]
    rw [show Fintype.card (((Finset.univ : Finset (Fin n)) : Finset (Fin n))) = n by
      rw [Fintype.card_coe, Finset.card_univ, Fintype.card_fin]]
  -- evaluate each singleton term as `c_{n-1}`
  have hsingle : ∀ j ∈ Finset.univ.erase (0 : Fin n),
      alternatingConnectedSubgraphSum (⊤ : SimpleGraph (({j}ᶜ : Finset (Fin n)))) =
        alternatingConnectedSubgraphSum (⊤ : SimpleGraph (Fin (n - 1))) := by
    intro j _
    rw [alternatingConnectedSubgraphSum_completeGraph_card]
    rw [show Fintype.card ((({j}ᶜ : Finset (Fin n)) : Finset (Fin n))) = n - 1 by
      rw [Fintype.card_coe, Finset.card_compl, Finset.card_singleton, Fintype.card_fin]]
  rw [huniv, Finset.sum_congr rfl hsingle, Finset.sum_const, nsmul_eq_mul,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at hrec
  -- hrec : 0 = c_n + (↑(n-1)) * c_{n-1}
  linarith [hrec]

/-- **Mayer closed form** (GJ §18.4, the general-`n` Mayer coefficient identity):
`alternatingConnectedSubgraphSum K_n = (-1)^(n-1)(n-1)!` for `n ≥ 1`. Proved by
induction from the recurrence `alternatingConnectedSubgraphSum_completeGraph_recurrence`
(`c_n = -(n-1)c_{n-1}`) with base case `alternatingConnectedSubgraphSum_K1`
(`c_1 = 1`); the step uses `m! = m·(m-1)!` and `(-1)^m = -(-1)^(m-1)`. This is the
Mayer/Ursell coefficient of the complete-graph cluster expansion, completing the
root-component recurrence programme for the connected-spanning signed sum. -/
theorem alternatingConnectedSubgraphSum_completeGraph_closed_form {n : ℕ} (hn : 1 ≤ n) :
    alternatingConnectedSubgraphSum (⊤ : SimpleGraph (Fin n))
      = (-1 : ℝ) ^ (n - 1) * (Nat.factorial (n - 1) : ℝ) := by
  induction n, hn using Nat.le_induction with
  | base =>
    rw [alternatingConnectedSubgraphSum_K1]
    norm_num
  | succ m hm ih =>
    have hrec := alternatingConnectedSubgraphSum_completeGraph_recurrence (n := m + 1) (by omega)
    rw [Nat.add_sub_cancel] at hrec
    have hc : alternatingConnectedSubgraphSum (⊤ : SimpleGraph (Fin (m + 1)))
        = -(↑m : ℝ) * alternatingConnectedSubgraphSum (⊤ : SimpleGraph (Fin m)) := by
      linarith [hrec]
    have hfac : (Nat.factorial m : ℝ) = (m : ℝ) * (Nat.factorial (m - 1) : ℝ) := by
      rw [← Nat.mul_factorial_pred (show m ≠ 0 by omega)]
      push_cast
      ring
    have hpow : (-1 : ℝ) ^ m = -((-1 : ℝ) ^ (m - 1)) := by
      conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ]
      ring
    rw [hc, ih, Nat.add_sub_cancel, hfac, hpow]
    ring

end IsingModel

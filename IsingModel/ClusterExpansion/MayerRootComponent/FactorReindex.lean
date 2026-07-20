import IsingModel.ClusterExpansion.AlternatingCompleteGraph
import IsingModel.ClusterExpansion.Incompatibility
import IsingModel.ClusterExpansion.MayerRootComponent.FiberProduct

/-!
# Mayer K_n root-component recurrence (3/5): reindexing both factors as complete-graph sums

Structural split (3/5) of `IsingModel.ClusterExpansion.MayerRootComponent`.
This child evaluates both factors of the fibre split as complete-graph sums: the outside
factor becomes `D (K_{Cᶜ})` via `outsideEdgeSubsets_eq_powerset`, its alternating dichotomy,
the complement-cardinality criterion and the subtype evaluation of `D`; the inside factor
becomes `c (K_C)` via the `Sym2.map` graph identity together with its range and roundtrip
lemmas.  See the `IsingModel.ClusterExpansion.MayerRootComponent` facade module for the full
contents overview.
-/

namespace IsingModel

open Finset

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

end IsingModel

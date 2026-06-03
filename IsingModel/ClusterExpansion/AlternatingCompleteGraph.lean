import IsingModel.ClusterExpansion.MayerCore

/-!
# Cluster expansion complete-graph alternating sums

Mechanical child split from `ClusterExpansion.lean`.
-/

namespace IsingModel

open Finset

/-! ## K_n alternating connected-spanning subgraph sum (Mayer Phase B)

**Goal**: prove the Mayer combinatorial identity
  Σ_{S ⊆ E(K_n) connected spanning} (-1)^|S| = (-1)^(n-1) · (n-1)!

at least for small `n` cases (`n = 0, 1, 2`), and document the
general-n proof as research-level work (via matrix-tree / Tutte
polynomial / inclusion-exclusion). -/

/-- **Alternating connected-spanning sum** (helper definition):
`Σ_{S ∈ connectedSpanningEdgeSubsets G} (-1)^|S|`. The Mayer
combinatorial identity asserts this equals `(-1)^(n-1) · (n-1)!`
for `K_n`. -/
noncomputable def alternatingConnectedSubgraphSum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  ∑ S ∈ connectedSpanningEdgeSubsets G, (-1 : ℝ) ^ S.card

/-! ### All-subgraph signed sum `D_n` (root-component recurrence foundation)

The Mayer Phase B identity `alternatingConnectedSubgraphSum K_n =
(-1)^(n-1)·(n-1)!` is proved by the root-component recurrence: classifying every
spanning edge-subset by the connected component of vertex `0` gives
`D_n = ∑_{C ∋ 0} c_{|C|} · D_{n-|C|}`, where `c_m = alternatingConnectedSubgraphSum`
and `D_m = allSignedSubgraphSum` is the signed sum over *all* (not necessarily
connected) spanning edge-subsets. Since `D_m = 0` for `m ≥ 2` and `D_0 = D_1 = 1`,
the recurrence collapses to `c_n + (n-1)·c_{n-1} = 0`. This section establishes
the `D_n` values; the recurrence and closed form follow in later work (#1499). -/

/-- **Alternating all-subgraph sum** `D(G)`: `Σ_{S ⊆ E(G)} (-1)^|S|`, the signed
sum over *all* spanning edge-subsets (not necessarily connected). Plays the role
of `D_n` in the root-component recurrence for the complete-graph connected sum. -/
noncomputable def allSignedSubgraphSum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  ∑ S ∈ G.edgeFinset.powerset, (-1 : ℝ) ^ S.card

/-- **`D(G) = 0` when `G` has an edge**: if `G.edgeFinset` is nonempty then the
signed all-subgraph sum vanishes. Direct real-cast of
`Finset.sum_powerset_neg_one_pow_card_of_nonempty`. -/
theorem allSignedSubgraphSum_eq_zero_of_edgeFinset_nonempty
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.edgeFinset.Nonempty) :
    allSignedSubgraphSum G = 0 := by
  unfold allSignedSubgraphSum
  have hℤ : (∑ S ∈ G.edgeFinset.powerset, (-1 : ℤ) ^ S.card) = 0 :=
    Finset.sum_powerset_neg_one_pow_card_of_nonempty h
  have hcast : (∑ S ∈ G.edgeFinset.powerset, (-1 : ℝ) ^ S.card)
      = (((∑ S ∈ G.edgeFinset.powerset, (-1 : ℤ) ^ S.card) : ℤ) : ℝ) := by
    push_cast
    rfl
  rw [hcast, hℤ, Int.cast_zero]

/-- **`D(G) = 1` when `G` is edgeless**: if `G.edgeFinset = ∅` then the only
spanning edge-subset is `∅`, contributing `(-1)^0 = 1`. -/
theorem allSignedSubgraphSum_eq_one_of_edgeFinset_empty
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.edgeFinset = ∅) :
    allSignedSubgraphSum G = 1 := by
  unfold allSignedSubgraphSum
  rw [h]
  simp

/-- **Edge-relabelling embedding from a graph isomorphism**: `Sym2.map φ` as a
`Sym2 V ↪ Sym2 W`, injective since `φ` is. Relabels edge-subsets under `φ`. -/
private def isoEdgeEmbedding {V W : Type*}
    {G : SimpleGraph V} {H : SimpleGraph W} (φ : G ≃g H) :
    Sym2 V ↪ Sym2 W :=
  ⟨Sym2.map φ, Sym2.map.injective (EquivLike.injective φ)⟩

/-- **`D` is a graph-isomorphism invariant**: for `φ : G ≃g H`,
`allSignedSubgraphSum G = allSignedSubgraphSum H`. The relabelling
`S ↦ S.map (Sym2.map φ)` is a cardinality-preserving bijection between
`G.edgeFinset.powerset` and `H.edgeFinset.powerset`
(`SimpleGraph.Iso.map_mem_edgeSet_iff`). Supplies the `D_{n-|C|} = D(K_{n-|C|})`
ingredient of the Mayer root-component recurrence via `K_n|_C ≅ K_{|C|}`. -/
theorem allSignedSubgraphSum_iso {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] {G : SimpleGraph V} {H : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel H.Adj] (φ : G ≃g H) :
    allSignedSubgraphSum G = allSignedSubgraphSum H := by
  classical
  unfold allSignedSubgraphSum
  refine Finset.sum_bij'
    (fun S _ => S.map (isoEdgeEmbedding φ))
    (fun T _ => T.map (isoEdgeEmbedding φ.symm)) ?_ ?_ ?_ ?_ ?_
  · intro S hS
    rw [Finset.mem_powerset] at hS ⊢
    intro e he
    rw [Finset.mem_map] at he
    obtain ⟨a, ha, rfl⟩ := he
    rw [SimpleGraph.mem_edgeFinset]
    exact (SimpleGraph.Iso.map_mem_edgeSet_iff φ).mpr
      (SimpleGraph.mem_edgeFinset.mp (hS ha))
  · intro T hT
    rw [Finset.mem_powerset] at hT ⊢
    intro e he
    rw [Finset.mem_map] at he
    obtain ⟨a, ha, rfl⟩ := he
    rw [SimpleGraph.mem_edgeFinset]
    exact (SimpleGraph.Iso.map_mem_edgeSet_iff φ.symm).mpr
      (SimpleGraph.mem_edgeFinset.mp (hT ha))
  · intro S _
    have hcomp : (isoEdgeEmbedding φ).trans (isoEdgeEmbedding φ.symm)
        = Function.Embedding.refl _ := by
      ext e
      refine Sym2.ind (fun a b => ?_) e
      simp [isoEdgeEmbedding]
    simp only [Finset.map_map, hcomp, Finset.map_refl]
  · intro T _
    have hcomp : (isoEdgeEmbedding φ.symm).trans (isoEdgeEmbedding φ)
        = Function.Embedding.refl _ := by
      ext e
      refine Sym2.ind (fun a b => ?_) e
      simp [isoEdgeEmbedding]
    simp only [Finset.map_map, hcomp, Finset.map_refl]
  · intro S _
    rw [Finset.card_map]

/-- **Graph isomorphism preserves connectivity of edge-subset subgraphs**: for
`φ : G ≃g H`, the same vertex bijection is an isomorphism
`fromEdgeSet ↑S ≃g fromEdgeSet ↑(S.map (Sym2.map φ))`, so connectivity transfers. -/
private theorem fromEdgeSet_map_iso_connected_iff {V W : Type*}
    {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G ≃g H) (S : Finset (Sym2 V)) :
    (SimpleGraph.fromEdgeSet (↑(S.map (isoEdgeEmbedding φ)) : Set (Sym2 W))).Connected ↔
      (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 V))).Connected := by
  refine SimpleGraph.Iso.connected_iff (G := SimpleGraph.fromEdgeSet (↑S : Set (Sym2 V)))
    (H := SimpleGraph.fromEdgeSet (↑(S.map (isoEdgeEmbedding φ)) : Set (Sym2 W)))
    ⟨φ.toEquiv, ?_⟩ |>.symm
  intro a b
  simp only [SimpleGraph.fromEdgeSet_adj, Finset.mem_coe, RelIso.coe_fn_toEquiv]
  rw [show (s(φ a, φ b) : Sym2 W) = isoEdgeEmbedding φ s(a, b) by
        simp [isoEdgeEmbedding, Sym2.map_mk],
      Finset.mem_map' (isoEdgeEmbedding φ)]
  exact and_congr Iff.rfl (EquivLike.injective φ).ne_iff

/-- **`c` (connected-spanning signed sum) is a graph-isomorphism invariant**:
for `φ : G ≃g H`, `alternatingConnectedSubgraphSum G = alternatingConnectedSubgraphSum H`.
Same edge-subset relabelling as `allSignedSubgraphSum_iso`, restricted to the
connected-spanning subsets: `φ` carries `fromEdgeSet ↑S` isomorphically to
`fromEdgeSet ↑(S.map (Sym2.map φ))` (same vertex bijection), so connectivity is
preserved (`SimpleGraph.Iso.connected_iff`). Supplies the `c_{|C|} = c(K_{|C|})`
ingredient of the Mayer root-component recurrence via `K_n|_C ≅ K_{|C|}`. -/
theorem alternatingConnectedSubgraphSum_iso {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] {G : SimpleGraph V} {H : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel H.Adj] (φ : G ≃g H) :
    alternatingConnectedSubgraphSum G = alternatingConnectedSubgraphSum H := by
  classical
  unfold alternatingConnectedSubgraphSum
  refine Finset.sum_bij'
    (fun S _ => S.map (isoEdgeEmbedding φ))
    (fun T _ => T.map (isoEdgeEmbedding φ.symm)) ?_ ?_ ?_ ?_ ?_
  · intro S hS
    rw [mem_connectedSpanningEdgeSubsets] at hS ⊢
    refine ⟨?_, ?_⟩
    · intro e he
      rw [Finset.mem_map] at he
      obtain ⟨a, ha, rfl⟩ := he
      rw [SimpleGraph.mem_edgeFinset]
      exact (SimpleGraph.Iso.map_mem_edgeSet_iff φ).mpr
        (SimpleGraph.mem_edgeFinset.mp (hS.1 ha))
    · exact (fromEdgeSet_map_iso_connected_iff φ S).mpr hS.2
  · intro T hT
    rw [mem_connectedSpanningEdgeSubsets] at hT ⊢
    refine ⟨?_, ?_⟩
    · intro e he
      rw [Finset.mem_map] at he
      obtain ⟨a, ha, rfl⟩ := he
      rw [SimpleGraph.mem_edgeFinset]
      exact (SimpleGraph.Iso.map_mem_edgeSet_iff φ.symm).mpr
        (SimpleGraph.mem_edgeFinset.mp (hT.1 ha))
    · exact (fromEdgeSet_map_iso_connected_iff φ.symm T).mpr hT.2
  · intro S _
    have hcomp : (isoEdgeEmbedding φ).trans (isoEdgeEmbedding φ.symm)
        = Function.Embedding.refl _ := by
      ext e
      refine Sym2.ind (fun a b => ?_) e
      simp [isoEdgeEmbedding]
    simp only [Finset.map_map, hcomp, Finset.map_refl]
  · intro T _
    have hcomp : (isoEdgeEmbedding φ.symm).trans (isoEdgeEmbedding φ)
        = Function.Embedding.refl _ := by
      ext e
      refine Sym2.ind (fun a b => ?_) e
      simp [isoEdgeEmbedding]
    simp only [Finset.map_map, hcomp, Finset.map_refl]
  · intro S _
    rw [Finset.card_map]

/-- **`c(K_V)` depends only on `|V|`**: for any finite `V`, the connected-spanning
signed sum of the complete graph on `V` equals that of `K_{|V|}`. Iso-invariance
applied to `K_V ≅ K_{Fin |V|}` (`SimpleGraph.Iso.completeGraph (Fintype.equivFin V)`).
Gives `c_{|C|} = c(K_{|C|})` for the root-component recurrence (with `V := ↑C`). -/
theorem alternatingConnectedSubgraphSum_completeGraph_card
    {V : Type*} [Fintype V] [DecidableEq V] :
    alternatingConnectedSubgraphSum (⊤ : SimpleGraph V)
      = alternatingConnectedSubgraphSum (⊤ : SimpleGraph (Fin (Fintype.card V))) :=
  alternatingConnectedSubgraphSum_iso (SimpleGraph.Iso.completeGraph (Fintype.equivFin V))

/-- **`D(K_V)` depends only on `|V|`**: for any finite `V`, the all-subgraph signed
sum of the complete graph on `V` equals that of `K_{|V|}`. Iso-invariance applied to
`K_V ≅ K_{Fin |V|}`. Gives `D_{n-|C|} = D(K_{n-|C|})` for the recurrence. -/
theorem allSignedSubgraphSum_completeGraph_card
    {V : Type*} [Fintype V] [DecidableEq V] :
    allSignedSubgraphSum (⊤ : SimpleGraph V)
      = allSignedSubgraphSum (⊤ : SimpleGraph (Fin (Fintype.card V))) :=
  allSignedSubgraphSum_iso (SimpleGraph.Iso.completeGraph (Fintype.equivFin V))

/-- **Edges of `S` do not cross connected components**: in `fromEdgeSet ↑S`, the
two endpoints of any edge `s(a,b) ∈ S` (with `a ≠ b`) lie in the same connected
component. Direct from `SimpleGraph.connectedComponentMk_eq_of_adj`. The
crossing-edge-free property underlying the root-component decomposition: the edges
of `S` within the component `C` of vertex `0` and those outside `C` have no
edge of `S` between them. -/
theorem connectedComponentMk_eq_of_mem {V : Type*} {S : Finset (Sym2 V)} {a b : V}
    (hab : s(a, b) ∈ S) (hne : a ≠ b) :
    (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 V))).connectedComponentMk a
      = (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 V))).connectedComponentMk b := by
  apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
  rw [SimpleGraph.fromEdgeSet_adj]
  exact ⟨Finset.mem_coe.mpr hab, hne⟩

/-- **`D_n = 0` for `K_n`, `n ≥ 2`**: the signed all-subgraph sum over the
complete graph vanishes once there is at least one edge (`s(0,1)`). The `D_m = 0`
ingredient of the Mayer root-component recurrence. -/
theorem allSignedSubgraphSum_completeGraph_eq_zero_of_two_le
    {n : ℕ} (hn : 2 ≤ n) :
    allSignedSubgraphSum (⊤ : SimpleGraph (Fin n)) = 0 := by
  apply allSignedSubgraphSum_eq_zero_of_edgeFinset_nonempty
  refine ⟨s(⟨0, by omega⟩, ⟨1, by omega⟩), ?_⟩
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.top_adj]
  exact Fin.ne_of_val_ne Nat.zero_ne_one

/-- **`D(G) = 1` for an edgeless complete graph on a `Subsingleton`**: `K_n` with
`n ≤ 1` (here via `Subsingleton (Fin n)`) has no edges, so `D = 1`. Covers the
`n = 0` and `n = 1` boundary values of the recurrence uniformly. -/
theorem allSignedSubgraphSum_completeGraph_eq_one_of_subsingleton
    {n : ℕ} [Subsingleton (Fin n)] :
    allSignedSubgraphSum (⊤ : SimpleGraph (Fin n)) = 1 := by
  apply allSignedSubgraphSum_eq_one_of_edgeFinset_empty
  rw [Finset.eq_empty_iff_forall_notMem]
  intro e he
  rw [SimpleGraph.mem_edgeFinset] at he
  revert he
  refine Sym2.ind (fun a b hab => ?_) e
  rw [SimpleGraph.mem_edgeSet, SimpleGraph.top_adj] at hab
  exact hab (Subsingleton.elim a b)

/-- **`K_0` alternating sum = 0** (Mayer Phase B base case): for the
empty graph on `Fin 0`, no SimpleGraph is `Connected` (Connected
requires `Nonempty V`), so `connectedSpanningEdgeSubsets = ∅` and
the alternating sum is 0. -/
theorem alternatingConnectedSubgraphSum_K0 :
    alternatingConnectedSubgraphSum (⊤ : SimpleGraph (Fin 0)) = 0 := by
  classical
  unfold alternatingConnectedSubgraphSum connectedSpanningEdgeSubsets
  refine Finset.sum_eq_zero ?_ |>.trans rfl
  intro S hS
  exfalso
  rw [Finset.mem_filter] at hS
  exact hS.2.nonempty.elim Fin.elim0

/-- **`K_n` is loopless on Fin 1**: K_1 has no edges since SimpleGraph
disallows self-loops and Fin 1 has only one vertex. -/
private theorem top_simpleGraph_fin_one_edgeFinset :
    (⊤ : SimpleGraph (Fin 1)).edgeFinset = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro e he
  rw [SimpleGraph.mem_edgeFinset] at he
  induction e using Sym2.ind with
  | h a b =>
    rw [SimpleGraph.mem_edgeSet, SimpleGraph.top_adj] at he
    exact he (Subsingleton.elim a b)

/-- **`K_2` edge set = {s(0,1)}**: K_2 on `Fin 2` has the single
edge `s(0,1)`. -/
private theorem top_simpleGraph_fin_two_edgeFinset :
    (⊤ : SimpleGraph (Fin 2)).edgeFinset = {s(0, 1)} := by
  classical
  apply Finset.ext
  intro e
  rw [SimpleGraph.mem_edgeFinset, Finset.mem_singleton]
  refine ⟨?_, fun h => ?_⟩
  · induction e using Sym2.ind with
    | h a b =>
      intro hab
      rw [SimpleGraph.mem_edgeSet, SimpleGraph.top_adj] at hab
      fin_cases a <;> fin_cases b <;> simp_all [Sym2.eq_swap]
  · rw [h, SimpleGraph.mem_edgeSet, SimpleGraph.top_adj]
    decide

/-- **`K_3` edge set = {s(0,1), s(0,2), s(1,2)}**: K_3 has the 3
edges between distinct vertex pairs. -/
private theorem top_simpleGraph_fin_three_edgeFinset :
    (⊤ : SimpleGraph (Fin 3)).edgeFinset = {s(0, 1), s(0, 2), s(1, 2)} := by
  classical
  apply Finset.ext
  intro e
  rw [SimpleGraph.mem_edgeFinset]
  refine ⟨?_, fun h => ?_⟩
  · induction e using Sym2.ind with
    | h a b =>
      intro hab
      rw [SimpleGraph.mem_edgeSet, SimpleGraph.top_adj] at hab
      fin_cases a <;> fin_cases b <;> simp_all [Sym2.eq_swap]
  · rcases (by simpa using h : e = s(0,1) ∨ e = s(0,2) ∨ e = s(1,2)) with h | h | h <;>
      · subst h; rw [SimpleGraph.mem_edgeSet, SimpleGraph.top_adj]; decide

/-- **`K_2` alternating sum = -1** (Mayer Phase B base case):
`(-1)^(2-1) · (2-1)! = -1 · 1 = -1`. The connected spanning subgraphs
of K_2 are: only `{edge}` (since ∅ leaves both vertices isolated).
Sum = `(-1)^1 = -1`. -/
theorem alternatingConnectedSubgraphSum_K2 :
    alternatingConnectedSubgraphSum (⊤ : SimpleGraph (Fin 2)) = -1 := by
  classical
  unfold alternatingConnectedSubgraphSum
  -- Key: (fromEdgeSet ∅) on Fin 2 is disconnected; (fromEdgeSet {s(0,1)}) is connected.
  have h_zero_ne_one : (0 : Fin 2) ≠ (1 : Fin 2) := by decide
  have h_disconn_empty :
      ¬ (SimpleGraph.fromEdgeSet (∅ : Set (Sym2 (Fin 2)))).Connected := by
    intro hc
    obtain ⟨w⟩ := hc.preconnected 0 1
    cases w with
    | cons hadj _ =>
      rw [SimpleGraph.fromEdgeSet_adj] at hadj
      exact hadj.1
  have h_conn_full :
      (SimpleGraph.fromEdgeSet ({s(0, 1)} : Set (Sym2 (Fin 2)))).Connected := by
    refine { preconnected := ?_, nonempty := ⟨0⟩ }
    intro u v
    have h_adj_uv : ∀ a b : Fin 2, a ≠ b →
        (SimpleGraph.fromEdgeSet ({s(0, 1)} : Set (Sym2 (Fin 2)))).Adj a b := by
      intro a b hne
      rw [SimpleGraph.fromEdgeSet_adj]
      refine ⟨?_, hne⟩
      fin_cases a <;> fin_cases b <;> simp_all [Sym2.eq_swap]
    by_cases huv : u = v
    · exact huv ▸ SimpleGraph.Reachable.refl u
    · exact ⟨SimpleGraph.Walk.cons (h_adj_uv u v huv) SimpleGraph.Walk.nil⟩
  have h_set : connectedSpanningEdgeSubsets (⊤ : SimpleGraph (Fin 2)) = {{s(0, 1)}} := by
    apply Finset.ext
    intro S
    rw [mem_connectedSpanningEdgeSubsets, top_simpleGraph_fin_two_edgeFinset,
        Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · rintro ⟨hS_sub, hS_conn⟩
      rw [Finset.subset_singleton_iff] at hS_sub
      rcases hS_sub with rfl | rfl
      · exact absurd (by simpa using hS_conn) h_disconn_empty
      · rfl
    · intro hS_eq
      refine ⟨by rw [hS_eq], ?_⟩
      rw [hS_eq]
      simpa using h_conn_full
  rw [h_set, Finset.sum_singleton, Finset.card_singleton, pow_one]

/-- **`K_1` alternating sum = 1** (Mayer Phase B base case):
`(-1)^(1-1) · (1-1)! = (-1)^0 · 0! = 1 · 1 = 1`. The only edge subset
of an edgeless K_1 is `∅`, which gives a single-vertex graph that is
trivially connected; sum = `(-1)^0 = 1`. -/
theorem alternatingConnectedSubgraphSum_K1 :
    alternatingConnectedSubgraphSum (⊤ : SimpleGraph (Fin 1)) = 1 := by
  classical
  unfold alternatingConnectedSubgraphSum
  -- connectedSpanningEdgeSubsets ⊤ = {∅} for K_1
  have h_set : connectedSpanningEdgeSubsets (⊤ : SimpleGraph (Fin 1)) = {∅} := by
    apply Finset.ext
    intro S
    rw [mem_connectedSpanningEdgeSubsets, Finset.mem_singleton,
        top_simpleGraph_fin_one_edgeFinset, Finset.subset_empty]
    refine ⟨fun h => h.1, fun hS => ⟨hS, ?_⟩⟩
    rw [hS]
    refine { preconnected := ?_, nonempty := ⟨0⟩ }
    intro u v
    have huv : u = v := Subsingleton.elim u v
    exact huv ▸ SimpleGraph.Reachable.refl u
  rw [h_set, Finset.sum_singleton, Finset.card_empty, pow_zero]

/-- **K_3 connected: pair {s(0,1), s(0,2)} as Finset** (path 1-0-2),
proved by `decide`. -/
private theorem fin_three_connected_01_02_finset :
    (SimpleGraph.fromEdgeSet
        (↑({s(0, 1), s(0, 2)} : Finset (Sym2 (Fin 3))) : Set (Sym2 (Fin 3)))).Connected := by
  decide

/-- **K_3 connected: pair {s(0,1), s(1,2)} as Finset** (path 0-1-2),
proved by `decide`. -/
private theorem fin_three_connected_01_12_finset :
    (SimpleGraph.fromEdgeSet
        (↑({s(0, 1), s(1, 2)} : Finset (Sym2 (Fin 3))) : Set (Sym2 (Fin 3)))).Connected := by
  decide

/-- **K_3 connected: pair {s(0,2), s(1,2)} as Finset** (path 0-2-1),
proved by `decide`. -/
private theorem fin_three_connected_02_12_finset :
    (SimpleGraph.fromEdgeSet
        (↑({s(0, 2), s(1, 2)} : Finset (Sym2 (Fin 3))) : Set (Sym2 (Fin 3)))).Connected := by
  decide

/-- **K_3 connected: triangle as Finset**, proved by `decide`. -/
private theorem fin_three_connected_triangle_finset :
    (SimpleGraph.fromEdgeSet
        (↑({s(0, 1), s(0, 2), s(1, 2)} : Finset (Sym2 (Fin 3))) :
          Set (Sym2 (Fin 3)))).Connected := by
  decide

/-- **K_3 disconnected: empty edge set as Finset**, proved by `decide`. -/
private theorem fin_three_disconnected_empty_finset :
    ¬ (SimpleGraph.fromEdgeSet
        (↑(∅ : Finset (Sym2 (Fin 3))) : Set (Sym2 (Fin 3)))).Connected := by
  decide

/-- **K_3 disconnected: {s(0,1)} as Finset**, proved by `decide`. -/
private theorem fin_three_disconnected_01_finset :
    ¬ (SimpleGraph.fromEdgeSet
        (↑({s(0, 1)} : Finset (Sym2 (Fin 3))) : Set (Sym2 (Fin 3)))).Connected := by
  decide

/-- **K_3 disconnected: {s(0,2)} as Finset**, proved by `decide`. -/
private theorem fin_three_disconnected_02_finset :
    ¬ (SimpleGraph.fromEdgeSet
        (↑({s(0, 2)} : Finset (Sym2 (Fin 3))) : Set (Sym2 (Fin 3)))).Connected := by
  decide

/-- **K_3 disconnected: {s(1,2)} as Finset**, proved by `decide`. -/
private theorem fin_three_disconnected_12_finset :
    ¬ (SimpleGraph.fromEdgeSet
        (↑({s(1, 2)} : Finset (Sym2 (Fin 3))) : Set (Sym2 (Fin 3)))).Connected := by
  decide

/-- **`K_3` alternating sum = 2** (Mayer Phase B base case):
`(-1)^(3-1) · (3-1)! = 1 · 2 = 2`. The 4 connected spanning subgraphs
of `K_3` are the 3 paths (size 2 each) and the triangle (size 3):
sum = `3 · (-1)^2 + (-1)^3 = 3 - 1 = 2`. Connectivity / disconnectivity
of each subset is verified by `decide` on the finite-graph
`SimpleGraph.Connected` decidable instance. -/
theorem alternatingConnectedSubgraphSum_K3 :
    alternatingConnectedSubgraphSum (⊤ : SimpleGraph (Fin 3)) = 2 := by
  classical
  unfold alternatingConnectedSubgraphSum
  have h_set : connectedSpanningEdgeSubsets (⊤ : SimpleGraph (Fin 3)) =
      ({{s(0, 1), s(0, 2)}, {s(0, 1), s(1, 2)}, {s(0, 2), s(1, 2)},
          {s(0, 1), s(0, 2), s(1, 2)}} : Finset (Finset (Sym2 (Fin 3)))) := by
    ext S
    rw [mem_connectedSpanningEdgeSubsets, top_simpleGraph_fin_three_edgeFinset]
    constructor
    · rintro ⟨hsub, hconn⟩
      have hpow : S ∈ ({s(0, 1), s(0, 2), s(1, 2)} :
          Finset (Sym2 (Fin 3))).powerset :=
        Finset.mem_powerset.mpr hsub
      -- powerset of a 3-element finset has 8 specific elements (verify by decide).
      have h_pow_eq : ({s(0, 1), s(0, 2), s(1, 2)} :
          Finset (Sym2 (Fin 3))).powerset =
          ({∅, {s(0, 1)}, {s(0, 2)}, {s(1, 2)},
              {s(0, 1), s(0, 2)}, {s(0, 1), s(1, 2)},
              {s(0, 2), s(1, 2)}, {s(0, 1), s(0, 2), s(1, 2)}} :
            Finset (Finset (Sym2 (Fin 3)))) := by decide
      rw [h_pow_eq] at hpow
      simp only [Finset.mem_insert, Finset.mem_singleton] at hpow
      rcases hpow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact absurd hconn fin_three_disconnected_empty_finset
      · exact absurd hconn fin_three_disconnected_01_finset
      · exact absurd hconn fin_three_disconnected_02_finset
      · exact absurd hconn fin_three_disconnected_12_finset
      · decide
      · decide
      · decide
      · decide
    · intro hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl | rfl | rfl
      · refine ⟨by decide, fin_three_connected_01_02_finset⟩
      · refine ⟨by decide, fin_three_connected_01_12_finset⟩
      · refine ⟨by decide, fin_three_connected_02_12_finset⟩
      · refine ⟨by decide, fin_three_connected_triangle_finset⟩
  rw [h_set]
  -- Now compute the sum: (-1)^2 + (-1)^2 + (-1)^2 + (-1)^3 = 2.
  -- The 4 finsets are pairwise distinct (verify by decide).
  have h1 : ({s(0, 1), s(0, 2)} : Finset (Sym2 (Fin 3))).card = 2 := by decide
  have h2 : ({s(0, 1), s(1, 2)} : Finset (Sym2 (Fin 3))).card = 2 := by decide
  have h3 : ({s(0, 2), s(1, 2)} : Finset (Sym2 (Fin 3))).card = 2 := by decide
  have h4 : ({s(0, 1), s(0, 2), s(1, 2)} : Finset (Sym2 (Fin 3))).card = 3 := by decide
  have hd1 : ({s(0, 1), s(0, 2)} : Finset (Sym2 (Fin 3))) ∉
      ({{s(0, 1), s(1, 2)}, {s(0, 2), s(1, 2)}, {s(0, 1), s(0, 2), s(1, 2)}} :
        Finset (Finset (Sym2 (Fin 3)))) := by decide
  have hd2 : ({s(0, 1), s(1, 2)} : Finset (Sym2 (Fin 3))) ∉
      ({{s(0, 2), s(1, 2)}, {s(0, 1), s(0, 2), s(1, 2)}} :
        Finset (Finset (Sym2 (Fin 3)))) := by decide
  have hd3 : ({s(0, 2), s(1, 2)} : Finset (Sym2 (Fin 3))) ∉
      ({{s(0, 1), s(0, 2), s(1, 2)}} : Finset (Finset (Sym2 (Fin 3)))) := by decide
  rw [show ({{s(0, 1), s(0, 2)}, {s(0, 1), s(1, 2)}, {s(0, 2), s(1, 2)},
            {s(0, 1), s(0, 2), s(1, 2)}} : Finset (Finset (Sym2 (Fin 3)))) =
        insert ({s(0, 1), s(0, 2)} : Finset (Sym2 (Fin 3)))
          (insert ({s(0, 1), s(1, 2)} : Finset (Sym2 (Fin 3)))
            (insert ({s(0, 2), s(1, 2)} : Finset (Sym2 (Fin 3)))
              ({{s(0, 1), s(0, 2), s(1, 2)}} : Finset (Finset (Sym2 (Fin 3))))))
        from rfl,
      Finset.sum_insert hd1, Finset.sum_insert hd2, Finset.sum_insert hd3,
      Finset.sum_singleton, h1, h2, h3, h4]
  norm_num

set_option maxRecDepth 2000 in
/-- **`K_4` alternating sum = -6** (Mayer Phase B base case):
`(-1)^(4-1) · (4-1)! = -1 · 6 = -6`. The `connectedSpanningEdgeSubsets`
of K_4 has 38 elements (16 spanning trees of size 3, plus larger
connected subgraphs); the alternating sum of `(-1)^|S|` collapses to
`-6` by `decide` on the integer-valued sum, which reduces to a
finite filter over the powerset of K_4's 6 edges. -/
theorem alternatingConnectedSubgraphSum_K4 :
    alternatingConnectedSubgraphSum (⊤ : SimpleGraph (Fin 4)) = -6 := by
  unfold alternatingConnectedSubgraphSum connectedSpanningEdgeSubsets
  -- Convert the real-valued sum to an integer-valued sum via cast.
  have h_int :
      (∑ S ∈ (⊤ : SimpleGraph (Fin 4)).edgeFinset.powerset.filter
        (fun S : Finset (Sym2 (Fin 4)) =>
          (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin 4)))).Connected),
        ((-1 : ℤ) ^ S.card)) = -6 := by decide
  have h_cast :
      (∑ S ∈ (⊤ : SimpleGraph (Fin 4)).edgeFinset.powerset.filter
          (fun S : Finset (Sym2 (Fin 4)) =>
            (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin 4)))).Connected),
        ((-1 : ℝ) ^ S.card)) =
        (((∑ S ∈ (⊤ : SimpleGraph (Fin 4)).edgeFinset.powerset.filter
            (fun S : Finset (Sym2 (Fin 4)) =>
              (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin 4)))).Connected),
          ((-1 : ℤ) ^ S.card)) : ℤ) : ℝ) := by
    push_cast
    rfl
  rw [h_cast, h_int]
  norm_num

/-- **Mayer expansion term restricts to connected polymer sequences**:
the sum defining `mayerExpansionTerm G n t` can be restricted to
sequences `ω : Fin n → polymers` such that the index-side
incompatibility graph `polymerSeqIncompatibilityGraph ω` is
`Connected`. Proof: for disconnected `ω`, Step 584
(`ursellCoefficient_eq_zero_of_disconnected`) gives `ϕ^T(ω) = 0`,
so the contribution `ϕ^T(ω) · z(t, ω)` vanishes.

This sharpens the Mayer expansion identity: only **cluster
sequences** (connected sequences in the incompatibility graph)
contribute to `log Ξ`, matching the standard formulation
`log Ξ = ∑_{n ≥ 1} ∑_{cluster sequences ω} ϕ^T(ω) · z(t, ω)`. -/
theorem mayerExpansionTerm_filter_connected
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (n : ℕ) (t : ℝ) :
    mayerExpansionTerm G n t =
      ∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allPolymers G)).filter
        (fun ω => (polymerSeqIncompatibilityGraph ω).Connected),
        ursellCoefficient ω * clusterSeqActivity t ω := by
  classical
  unfold mayerExpansionTerm
  rw [← Finset.sum_filter_add_sum_filter_not
        (Fintype.piFinset (fun _ : Fin n => allPolymers G))
        (fun ω => (polymerSeqIncompatibilityGraph ω).Connected)
        (fun ω => ursellCoefficient ω * clusterSeqActivity t ω)]
  have h_disc :
      (∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allPolymers G)).filter
          (fun ω => ¬ (polymerSeqIncompatibilityGraph ω).Connected),
        ursellCoefficient ω * clusterSeqActivity t ω) = 0 := by
    apply Finset.sum_eq_zero
    intro ω hω
    rw [Finset.mem_filter] at hω
    rw [ursellCoefficient_eq_zero_of_disconnected ω hω.2, zero_mul]
  rw [h_disc, add_zero]

/-- **Mayer partial sum restricts to connected polymer sequences**:
the partial sum `mayerPartialSum G N t = ∑_{n=0..N} mayerExpansionTerm G n t`
can be rewritten so each term sums only over cluster sequences (those
`ω : Fin n → polymers` with connected incompatibility graph).
Direct corollary of `mayerExpansionTerm_filter_connected` applied
term-by-term. -/
theorem mayerPartialSum_filter_connected
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (N : ℕ) (t : ℝ) :
    mayerPartialSum G N t =
      ∑ n ∈ Finset.range (N + 1),
        ∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allPolymers G)).filter
          (fun ω => (polymerSeqIncompatibilityGraph ω).Connected),
          ursellCoefficient ω * clusterSeqActivity t ω := by
  unfold mayerPartialSum
  refine Finset.sum_congr rfl (fun n _ => ?_)
  exact mayerExpansionTerm_filter_connected G n t

/-- **Mayer expansion term restricted to connected sequences (n=0)**:
`mayerExpansionTerm G 0 t = 0` since the unique `ω : Fin 0 → polymers`
gives a graph on `Fin 0` which is disconnected (`Connected` requires
`Nonempty`). The filtered sum is empty. -/
theorem mayerExpansionTerm_filter_connected_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (_t : ℝ) :
    (Fintype.piFinset (fun _ : Fin 0 => allPolymers G)).filter
        (fun ω => (polymerSeqIncompatibilityGraph ω).Connected) = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro ω hω
  rw [Finset.mem_filter] at hω
  exact hω.2.nonempty.elim Fin.elim0

/-- **Mayer expansion term restricted to connected sequences (n=1)**:
every singleton sequence `ω : Fin 1 → polymers` has trivially-
connected incompatibility graph (single vertex, vacuously
preconnected), so the filter is the entire piFinset. -/
theorem mayerExpansionTerm_filter_connected_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    (Fintype.piFinset (fun _ : Fin 1 => allPolymers G)).filter
        (fun ω => (polymerSeqIncompatibilityGraph ω).Connected) =
      Fintype.piFinset (fun _ : Fin 1 => allPolymers G) := by
  classical
  apply Finset.filter_eq_self.mpr
  intro ω _
  refine { preconnected := ?_, nonempty := ⟨0⟩ }
  intro u v
  have huv : u = v := Subsingleton.elim u v
  exact huv ▸ SimpleGraph.Reachable.refl u

end IsingModel

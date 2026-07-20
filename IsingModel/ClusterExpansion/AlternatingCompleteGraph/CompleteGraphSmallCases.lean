import IsingModel.ClusterExpansion.Incompatibility
import IsingModel.ClusterExpansion.AlternatingCompleteGraph.SignedSums

/-!
# Cluster expansion complete-graph alternating sums (2/4): small complete graphs `K_0`–`K_3`

Structural split (2/4) of `IsingModel.ClusterExpansion.AlternatingCompleteGraph`.
This child holds the Mayer Phase B base values `c(K_0) = 0`, `c(K_1) = 1`, `c(K_2) = -1`
and `c(K_3) = 2`, together with the `Fin 1 / Fin 2 / Fin 3` edge-set and connectivity
helpers they need.  See the `IsingModel.ClusterExpansion.AlternatingCompleteGraph` facade
module for the full contents overview.
-/

namespace IsingModel

open Finset

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

end IsingModel

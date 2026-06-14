import IsingModel.AbstractPolymer.Cluster

/-!
# Penrose tree-graph inequality — the partition-scheme reduction (GJ §18.4)

The Kotecký–Preiss convergence of the cluster expansion (Issue #3954) hinges on
the *Penrose tree-graph inequality*: for a finite connected graph `G` on vertex
set `V`,

`|∑_{S ⊆ E(G), (V,S) connected} (-1)^{|S|}| ≤ #{spanning trees of G}`,

i.e. `|alternatingConnectedSubgraphSum G| ≤ (spanningTreeEdgeSubsets G).card`.
The signed sum on the left, with its enormous cancellation, is otherwise
uncontrollable: the trivial bound `2^{#E}` makes the cluster sum diverge.

The standard proof (Penrose, 1967) is a *partition scheme*: a vertex ordering
induces, for each spanning tree `T`, a set `addable T` of edges such that the
Boolean intervals `[T, T ∪ addable T]` partition the connected spanning
edge-subsets.  Over such an interval the alternating sum
`∑_{B ⊆ addable T} (-1)^{|T|+|B|}` collapses to `(-1)^{|T|}·𝟙[addable T = ∅]`,
so only spanning trees with no addable edge survive and the absolute value is
bounded by the number of spanning trees.

This file performs the **reduction**: it isolates the hard combinatorial content
of Penrose's construction into a single hypothesis — the existence of a
`PenrosePartitionScheme` — and proves, fully and generally, the Boolean-interval
sign-cancellation argument and the resulting tree-graph inequality.  The
construction of an actual scheme (the remaining combinatorial milestone) is left
to a subsequent step; this mirrors the project's convention of pushing a hard
infrastructural input into a single documented obligation.

## References

* O. Penrose, *Convergence of fugacity expansions for fluids and lattice gases*,
  in *Statistical Mechanics* (1967).
* Friedli–Velenik, *Statistical Mechanics of Lattice Systems*, §5.7 (Theorem 5.4).
* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.4, pp. 378–386.
-/

namespace IsingModel.AbstractPolymer

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Spanning-tree edge-subsets** of `G`: the connected spanning edge-subsets
`S` with `|S| + 1 = |V|`.  By `isTree_iff_connected_and_card`, among connected
spanning subgraphs this cardinality condition is exactly the condition of being a
tree, so this `Finset` is precisely the set of spanning trees of `G`, recorded as
edge-subsets. -/
noncomputable def spanningTreeEdgeSubsets (G : SimpleGraph V) [DecidableRel G.Adj] :
    Finset (Finset (Sym2 V)) :=
  (connectedSpanningEdgeSubsets G).filter (fun S => S.card + 1 = Fintype.card V)

/-- **Membership in `spanningTreeEdgeSubsets`**: `S` is a spanning tree iff it is a
connected spanning edge-subset of cardinality `|V| - 1`. -/
theorem mem_spanningTreeEdgeSubsets {G : SimpleGraph V} [DecidableRel G.Adj]
    {S : Finset (Sym2 V)} :
    S ∈ spanningTreeEdgeSubsets G ↔
      S ∈ connectedSpanningEdgeSubsets G ∧ S.card + 1 = Fintype.card V := by
  unfold spanningTreeEdgeSubsets; rw [Finset.mem_filter]

/-- **Spanning trees are connected spanning edge-subsets**. -/
theorem spanningTreeEdgeSubsets_subset {G : SimpleGraph V} [DecidableRel G.Adj] :
    spanningTreeEdgeSubsets G ⊆ connectedSpanningEdgeSubsets G :=
  fun _ hS => (mem_spanningTreeEdgeSubsets.mp hS).1

/-- **Connected spanning edge-subsets are upward closed (within `G`)**: a superset
`T ⊆ S ⊆ E(G)` of a connected spanning edge-subset `T` is again connected
spanning, since adding edges only enlarges reachability. -/
theorem mem_connectedSpanningEdgeSubsets_of_subset {G : SimpleGraph V} [DecidableRel G.Adj]
    {S T : Finset (Sym2 V)} (hT : T ∈ connectedSpanningEdgeSubsets G)
    (hTS : T ⊆ S) (hS : S ⊆ G.edgeFinset) :
    S ∈ connectedSpanningEdgeSubsets G := by
  rw [mem_connectedSpanningEdgeSubsets] at hT ⊢
  refine ⟨hS, ?_⟩
  have hle : SimpleGraph.fromEdgeSet (↑T : Set (Sym2 V))
      ≤ SimpleGraph.fromEdgeSet (↑S : Set (Sym2 V)) :=
    SimpleGraph.fromEdgeSet_mono (Finset.coe_subset.mpr hTS)
  exact { preconnected := fun u v => (hT.2.preconnected u v).mono hle,
          nonempty := hT.2.nonempty }

omit [Fintype V] in
/-- **Real-valued alternating powerset sum**: `∑_{B ⊆ A} (-1)^{|B|} = 𝟙[A = ∅]`.
The real-coefficient form of `Finset.sum_powerset_neg_one_pow_card`. -/
theorem real_sum_powerset_neg_one_pow_card (A : Finset (Sym2 V)) :
    (∑ B ∈ A.powerset, (-1 : ℝ) ^ B.card) = if A = ∅ then 1 else 0 := by
  have hcast : (∑ B ∈ A.powerset, (-1 : ℝ) ^ B.card)
      = ((∑ B ∈ A.powerset, (-1 : ℤ) ^ B.card : ℤ) : ℝ) := by push_cast; rfl
  rw [hcast, Finset.sum_powerset_neg_one_pow_card]
  split_ifs <;> simp

/-- **Penrose partition scheme** for `G`: the combinatorial datum underlying the
tree-graph inequality.  To each edge-subset it assigns a spanning tree `treeOf S`
and to each spanning tree `T` a set `addable T` of *addable edges*, such that the
Boolean intervals `[T, T ∪ addable T]` partition the connected spanning
edge-subsets (expressed fibrewise: `treeOf S = T ↔ T ⊆ S ⊆ T ∪ addable T`).
Penrose constructs such a scheme from a vertex ordering; here it is the single
hypothesis from which the tree-graph inequality follows. -/
structure PenrosePartitionScheme (G : SimpleGraph V) [DecidableRel G.Adj] where
  /-- The spanning tree assigned to an edge-subset (the retraction onto trees). -/
  treeOf : Finset (Sym2 V) → Finset (Sym2 V)
  /-- The addable edges of a spanning tree (defining its Boolean interval). -/
  addable : Finset (Sym2 V) → Finset (Sym2 V)
  /-- `treeOf` maps connected spanning edge-subsets to spanning trees. -/
  treeOf_mem : ∀ S ∈ connectedSpanningEdgeSubsets G, treeOf S ∈ spanningTreeEdgeSubsets G
  /-- The addable edges of a tree are disjoint from the tree itself. -/
  addable_disjoint : ∀ T ∈ spanningTreeEdgeSubsets G, Disjoint T (addable T)
  /-- The addable edges of a tree are edges of `G`. -/
  addable_subset_edges : ∀ T ∈ spanningTreeEdgeSubsets G, addable T ⊆ G.edgeFinset
  /-- **Partition property**: a connected spanning edge-subset `S` lies in the
  Boolean interval of the tree `treeOf S`, and in no other. -/
  fiber_iff : ∀ S ∈ connectedSpanningEdgeSubsets G, ∀ T ∈ spanningTreeEdgeSubsets G,
    (treeOf S = T ↔ T ⊆ S ∧ S ⊆ T ∪ addable T)

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **The fiber of `treeOf` over a tree `T` is its Boolean interval**, realised as
the image of `addable T`'s powerset under `B ↦ T ∪ B`. -/
theorem fiber_eq_image (sch : PenrosePartitionScheme G) {T : Finset (Sym2 V)}
    (hT : T ∈ spanningTreeEdgeSubsets G) :
    (connectedSpanningEdgeSubsets G).filter (fun S => sch.treeOf S = T)
      = (sch.addable T).powerset.image (fun B => T ∪ B) := by
  ext S
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_powerset]
  constructor
  · rintro ⟨hScse, hSt⟩
    obtain ⟨hTsub, hSsub⟩ := (sch.fiber_iff S hScse T hT).mp hSt
    refine ⟨S \ T, ?_, Finset.union_sdiff_of_subset hTsub⟩
    calc S \ T ⊆ (T ∪ sch.addable T) \ T := Finset.sdiff_subset_sdiff hSsub (le_refl T)
      _ = sch.addable T \ T := Finset.union_sdiff_left _ _
      _ ⊆ sch.addable T := Finset.sdiff_subset
  · rintro ⟨B, hB, rfl⟩
    have hTcse : T ∈ connectedSpanningEdgeSubsets G := spanningTreeEdgeSubsets_subset hT
    have hsub_edges : T ∪ B ⊆ G.edgeFinset :=
      Finset.union_subset (mem_connectedSpanningEdgeSubsets.mp hTcse).1
        (subset_trans hB (sch.addable_subset_edges T hT))
    have hcse : (T ∪ B) ∈ connectedSpanningEdgeSubsets G :=
      mem_connectedSpanningEdgeSubsets_of_subset hTcse Finset.subset_union_left hsub_edges
    refine ⟨hcse, ?_⟩
    rw [sch.fiber_iff (T ∪ B) hcse T hT]
    exact ⟨Finset.subset_union_left, Finset.union_subset_union (le_refl T) hB⟩

/-- **The alternating connected-subgraph sum collapses onto spanning trees**: under
a partition scheme,
`alternatingConnectedSubgraphSum G = ∑_{T tree} (-1)^{|T|} · 𝟙[addable T = ∅]`.
This is the Boolean-interval sign-cancellation at the heart of Penrose's proof. -/
theorem alternatingConnectedSubgraphSum_eq_tree_sum (sch : PenrosePartitionScheme G) :
    alternatingConnectedSubgraphSum G
      = ∑ T ∈ spanningTreeEdgeSubsets G,
          (-1 : ℝ) ^ T.card * (if sch.addable T = ∅ then 1 else 0) := by
  unfold alternatingConnectedSubgraphSum
  rw [← Finset.sum_fiberwise_of_maps_to sch.treeOf_mem (fun S => (-1 : ℝ) ^ S.card)]
  refine Finset.sum_congr rfl (fun T hT => ?_)
  rw [fiber_eq_image sch hT]
  have hinj : ∀ B₁ ∈ (sch.addable T).powerset, ∀ B₂ ∈ (sch.addable T).powerset,
      T ∪ B₁ = T ∪ B₂ → B₁ = B₂ := by
    intro B₁ h1 B₂ h2 heq
    rw [Finset.mem_powerset] at h1 h2
    have hd1 : Disjoint T B₁ := Finset.disjoint_of_subset_right h1 (sch.addable_disjoint T hT)
    have hd2 : Disjoint T B₂ := Finset.disjoint_of_subset_right h2 (sch.addable_disjoint T hT)
    have hcg := congrArg (fun S => S \ T) heq
    simpa only [Finset.union_sdiff_cancel_left hd1, Finset.union_sdiff_cancel_left hd2] using hcg
  rw [Finset.sum_image hinj]
  have hcard : ∀ B ∈ (sch.addable T).powerset,
      (-1 : ℝ) ^ (T ∪ B).card = (-1) ^ T.card * (-1) ^ B.card := by
    intro B hB
    rw [Finset.mem_powerset] at hB
    have hdisj : Disjoint T B :=
      Finset.disjoint_of_subset_right hB (sch.addable_disjoint T hT)
    rw [Finset.card_union_of_disjoint hdisj, pow_add]
  rw [Finset.sum_congr rfl hcard, ← Finset.mul_sum, real_sum_powerset_neg_one_pow_card]

/-- **Penrose tree-graph inequality (reduction form)**: given a partition scheme,
`|alternatingConnectedSubgraphSum G| ≤ #{spanning trees of G}`.  Each spanning
tree contributes at most `1` in absolute value, and only those with no addable
edge contribute at all, so the signed sum is bounded by the number of spanning
trees.  This is the bound that powers Kotecký–Preiss convergence. -/
theorem abs_alternatingConnectedSubgraphSum_le_card_spanningTrees
    (sch : PenrosePartitionScheme G) :
    |alternatingConnectedSubgraphSum G| ≤ (spanningTreeEdgeSubsets G).card := by
  rw [alternatingConnectedSubgraphSum_eq_tree_sum sch]
  calc |∑ T ∈ spanningTreeEdgeSubsets G,
          (-1 : ℝ) ^ T.card * (if sch.addable T = ∅ then 1 else 0)|
      ≤ ∑ T ∈ spanningTreeEdgeSubsets G,
          |(-1 : ℝ) ^ T.card * (if sch.addable T = ∅ then 1 else 0)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _T ∈ spanningTreeEdgeSubsets G, (1 : ℝ) := by
        refine Finset.sum_le_sum (fun T _ => ?_)
        rw [abs_mul, abs_pow]
        simp only [abs_neg, abs_one, one_pow, one_mul]
        split_ifs <;> norm_num
    _ = (spanningTreeEdgeSubsets G).card := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]

end IsingModel.AbstractPolymer

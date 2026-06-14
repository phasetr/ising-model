import IsingModel.ClusterExpansion.Penrose.IntervalPartition
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.SuccPred

/-!
# Spanning-tree count of the complete graph `Kₙ` (Penrose tree-graph, GJ §18.4-18.5)

The Penrose tree-graph inequality (Issue #3954, M1) bounds the alternating
connected-subgraph sum of a finite graph by its number of spanning trees,
`numSpanningTrees G`.  For the cluster-expansion convergence (M2) one needs a
*summable majorant* for `numSpanningTrees (⊤ : SimpleGraph (Fin n))`, the number
of spanning trees of the complete graph `Kₙ`.

The exact Cayley value `nⁿ⁻²` is **not** required: the weaker, unconditional
bound `numSpanningTrees (⊤ : SimpleGraph (Fin n)) ≤ n ^ (n - 1)` already yields a
finite radius of convergence `1/e` for the Mayer series, since
`∑ₙ n^(n-1)/n! · Rⁿ` converges for `R < 1/e` (ratio `(1+1/n)^(n-1) · R → e·R`).

This bound follows from a *parent-function injection* avoiding Prüfer/Cayley:
each spanning tree `T` of `K_{n+1}` (rooted at `0`) sends every non-root vertex
`Fin.succ i` to its **parent**, the unique neighbour decreasing the distance to
the root by one.  The edge set of `T` is recovered as the image of this parent
code (`completeGraphTree_edges_eq_parentCode_image`), so the parent code is an
injection of the spanning trees into `Fin n → Fin (n + 1)`, whence
`numSpanningTrees (⊤ : SimpleGraph (Fin (n + 1))) ≤ (n + 1) ^ n`.

## References
- Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.4, pp. 378–386.
- A. Cayley (1889), "A theorem on trees".
- Friedli–Velenik, *Statistical Mechanics of Lattice Systems*, §5.7.
-/

namespace IsingModel.Penrose

open Finset SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- **Existence of a parent toward the root** in a tree: for any vertex `v`
distinct from the root `r`, some neighbour `p` of `v` lies strictly closer to
`r`, i.e. `dist r v = dist r p + 1` (the unique path `v → r` steps to `p`). -/
theorem exists_parent_adj_dist_of_isTree (hG : G.IsTree) (r : V) {v : V}
    (hv : v ≠ r) :
    ∃ p : V, G.Adj v p ∧ G.dist r v = G.dist r p + 1 := by
  obtain ⟨w, hw_len⟩ := hG.connected.exists_walk_length_eq_dist v r
  have hne : ¬ w.Nil := SimpleGraph.Walk.not_nil_of_ne hv
  have hadj : G.Adj v w.snd := SimpleGraph.Walk.adj_snd hne
  refine ⟨w.snd, hadj, ?_⟩
  have htail : w.tail.length + 1 = w.length := SimpleGraph.Walk.length_tail_add_one hne
  have hsnd_le : G.dist r w.snd ≤ w.tail.length := by
    rw [dist_comm]; exact SimpleGraph.dist_le w.tail
  have hrv_ne : G.dist r v ≠ 0 :=
    (SimpleGraph.dist_ne_zero_iff_ne_and_reachable).mpr ⟨hv.symm, hG.connected r v⟩
  have hrv : G.dist r v = w.length := by rw [dist_comm]; exact hw_len.symm
  rcases hG.dist_eq_dist_add_one_of_adj r hadj with h | h
  · exact h
  · exfalso; omega

/-- **Uniqueness of the parent** in a tree: a neighbour of `v` that decreases the
distance to the root by one is unique.  Both candidates extend to a shortest
path `v → r`; the tree has a unique such path, so the second vertices agree. -/
theorem parent_adj_dist_unique_of_isTree (hG : G.IsTree) (r v p q : V)
    (hp_adj : G.Adj v p) (hp_dist : G.dist r v = G.dist r p + 1)
    (hq_adj : G.Adj v q) (hq_dist : G.dist r v = G.dist r q + 1) :
    p = q := by
  obtain ⟨wp, hwp_len⟩ := hG.connected.exists_walk_length_eq_dist p r
  obtain ⟨wq, hwq_len⟩ := hG.connected.exists_walk_length_eq_dist q r
  have hlen_p : (SimpleGraph.Walk.cons hp_adj wp).length = G.dist v r := by
    rw [SimpleGraph.Walk.length_cons, hwp_len, SimpleGraph.dist_comm (u := p) (v := r),
      ← hp_dist, SimpleGraph.dist_comm (u := r) (v := v)]
  have hlen_q : (SimpleGraph.Walk.cons hq_adj wq).length = G.dist v r := by
    rw [SimpleGraph.Walk.length_cons, hwq_len, SimpleGraph.dist_comm (u := q) (v := r),
      ← hq_dist, SimpleGraph.dist_comm (u := r) (v := v)]
  have hpath_p := (SimpleGraph.Walk.cons hp_adj wp).isPath_of_length_eq_dist hlen_p
  have hpath_q := (SimpleGraph.Walk.cons hq_adj wq).isPath_of_length_eq_dist hlen_q
  have heq := (hG.existsUnique_path v r).unique hpath_p hpath_q
  have hsnd := congrArg SimpleGraph.Walk.snd heq
  simpa using hsnd

/-- **Existence-and-uniqueness of the parent** in a tree, packaging
`exists_parent_adj_dist_of_isTree` and `parent_adj_dist_unique_of_isTree`. -/
theorem existsUnique_parent_adj_dist_of_isTree (hG : G.IsTree) (r : V) {v : V}
    (hv : v ≠ r) :
    ∃! p : V, G.Adj v p ∧ G.dist r v = G.dist r p + 1 := by
  obtain ⟨p, hadj, hdist⟩ := exists_parent_adj_dist_of_isTree hG r hv
  refine ⟨p, ⟨hadj, hdist⟩, ?_⟩
  rintro q ⟨hadj_q, hdist_q⟩
  exact parent_adj_dist_unique_of_isTree hG r v q p hadj_q hdist_q hadj hdist

/-- **The parent of a vertex** in a tree rooted at `r`: the unique neighbour
decreasing the distance to `r` by one. -/
noncomputable def treeParent (hG : G.IsTree) (r v : V) (hv : v ≠ r) : V :=
  (existsUnique_parent_adj_dist_of_isTree hG r hv).exists.choose

/-- **Defining property of `treeParent`**: it is a neighbour of `v` lying one
step closer to the root `r`. -/
theorem treeParent_spec (hG : G.IsTree) (r v : V) (hv : v ≠ r) :
    G.Adj v (treeParent hG r v hv) ∧
      G.dist r v = G.dist r (treeParent hG r v hv) + 1 :=
  (existsUnique_parent_adj_dist_of_isTree hG r hv).exists.choose_spec

/-- **The parent code of a spanning tree of `K_{n+1}`**: rooted at `0`, each
non-root vertex `Fin.succ i` is sent to its parent. -/
noncomputable def completeGraphTreeParentCode (n : ℕ)
    (T : {S : Finset (Sym2 (Fin (n + 1))) //
      S ∈ spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1)))}) :
    Fin n → Fin (n + 1) :=
  fun i => treeParent (isTree_fromEdgeSet_of_mem_spanningTreeEdgeSubsets T.2) 0
    (Fin.succ i) (Fin.succ_ne_zero i)

/-- **Edge-set recovery from the parent code**: the edge set of a spanning tree
of `K_{n+1}` is exactly the image of its parent code,
`{s(Fin.succ i, parent (Fin.succ i)) : i}`.  This is the crux of the injection:
for an edge `s(a, b)`, the endpoint farther from the root has the other as its
unique parent. -/
theorem completeGraphTree_edges_eq_parentCode_image (n : ℕ)
    (T : {S : Finset (Sym2 (Fin (n + 1))) //
      S ∈ spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1)))}) :
    T.1 = Finset.univ.image
      (fun i : Fin n => s(Fin.succ i, completeGraphTreeParentCode n T i)) := by
  have hG : (SimpleGraph.fromEdgeSet (↑T.1 : Set (Sym2 (Fin (n + 1))))).IsTree :=
    isTree_fromEdgeSet_of_mem_spanningTreeEdgeSubsets T.2
  have hSsub : T.1 ⊆ (⊤ : SimpleGraph (Fin (n + 1))).edgeFinset :=
    (mem_spanningTreeEdgeSubsets.mp T.2).1.1
  apply Finset.ext
  intro e
  induction e using Sym2.ind with
  | _ a b =>
    constructor
    · -- forward: an edge of the tree is a parent edge of its farther endpoint
      intro he
      have hab : a ≠ b := by
        have := hSsub he
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at this
        exact this.ne
      have hadj : (SimpleGraph.fromEdgeSet (↑T.1 : Set (Sym2 (Fin (n + 1))))).Adj a b := by
        rw [SimpleGraph.fromEdgeSet_adj]
        exact ⟨Finset.mem_coe.mpr he, hab⟩
      rcases hG.dist_eq_dist_add_one_of_adj 0 hadj with h | h
      · -- a is farther: parent a = b
        have ha0 : a ≠ 0 := by
          intro h0; rw [h0] at h; simp at h
        obtain ⟨i, rfl⟩ := Fin.exists_succ_eq_of_ne_zero ha0
        have hspec := treeParent_spec hG 0 (Fin.succ i) (Fin.succ_ne_zero i)
        have hb_eq : completeGraphTreeParentCode n T i = b :=
          parent_adj_dist_unique_of_isTree hG 0 (Fin.succ i) _ b hspec.1 hspec.2 hadj h
        refine Finset.mem_image.mpr ⟨i, Finset.mem_univ i, ?_⟩
        rw [hb_eq]
      · -- b is farther: parent b = a, use s(a,b) = s(b,a)
        have hb0 : b ≠ 0 := by
          intro h0; rw [h0] at h; simp at h
        obtain ⟨j, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hb0
        have hspec := treeParent_spec hG 0 (Fin.succ j) (Fin.succ_ne_zero j)
        have ha_eq : completeGraphTreeParentCode n T j = a :=
          parent_adj_dist_unique_of_isTree hG 0 (Fin.succ j) _ a hspec.1 hspec.2 hadj.symm h
        refine Finset.mem_image.mpr ⟨j, Finset.mem_univ j, ?_⟩
        rw [ha_eq, Sym2.eq_swap]
    · -- backward: every parent edge belongs to the tree
      intro he
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp he
      have hspec := treeParent_spec hG 0 (Fin.succ i) (Fin.succ_ne_zero i)
      have hadj : (SimpleGraph.fromEdgeSet (↑T.1 : Set (Sym2 (Fin (n + 1))))).Adj
          (Fin.succ i) (completeGraphTreeParentCode n T i) := hspec.1
      rw [SimpleGraph.fromEdgeSet_adj] at hadj
      have hmem : s(Fin.succ i, completeGraphTreeParentCode n T i) ∈ T.1 :=
        Finset.mem_coe.mp hadj.1
      rwa [hi] at hmem

/-- **The parent code is injective** on spanning trees of `K_{n+1}`: a spanning
tree is recovered from its parent code via the edge-set recovery. -/
theorem completeGraphTreeParentCode_injective (n : ℕ) :
    Function.Injective (completeGraphTreeParentCode n) := by
  intro T₁ T₂ h
  apply Subtype.ext
  rw [completeGraphTree_edges_eq_parentCode_image n T₁,
      completeGraphTree_edges_eq_parentCode_image n T₂]
  exact Finset.image_congr (fun i _ => by rw [congrFun h i])

/-- **Spanning-tree bound for `K_{n+1}`**:
`numSpanningTrees (⊤ : SimpleGraph (Fin (n + 1))) ≤ (n + 1) ^ n`, via the
injection of spanning trees into parent codes `Fin n → Fin (n + 1)`. -/
theorem numSpanningTrees_top_fin_succ_le_pow (n : ℕ) :
    numSpanningTrees (⊤ : SimpleGraph (Fin (n + 1))) ≤ (n + 1) ^ n := by
  have hcard : Fintype.card
      {S : Finset (Sym2 (Fin (n + 1))) //
        S ∈ spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1)))}
        = numSpanningTrees (⊤ : SimpleGraph (Fin (n + 1))) := by
    rw [numSpanningTrees]; exact Fintype.card_coe _
  calc numSpanningTrees (⊤ : SimpleGraph (Fin (n + 1)))
      = Fintype.card
          {S : Finset (Sym2 (Fin (n + 1))) //
            S ∈ spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1)))} := hcard.symm
    _ ≤ Fintype.card (Fin n → Fin (n + 1)) :=
        Fintype.card_le_of_injective _ (completeGraphTreeParentCode_injective n)
    _ = (n + 1) ^ n := by rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-- **Spanning-tree count of the complete graph `Kₙ`** is at most `n^(n-1)`
(unconditional; weaker than Cayley's exact `nⁿ⁻²` but enough for the
cluster-expansion convergence radius `1/e`). -/
theorem numSpanningTrees_top_fin_le_pow_pred (n : ℕ) :
    numSpanningTrees (⊤ : SimpleGraph (Fin n)) ≤ n ^ (n - 1) := by
  cases n with
  | zero =>
    simp only [Nat.zero_sub, pow_zero]
    calc numSpanningTrees (⊤ : SimpleGraph (Fin 0))
        ≤ 2 ^ (⊤ : SimpleGraph (Fin 0)).edgeFinset.card := numSpanningTrees_le_two_pow _
      _ = 1 := by rw [card_edgeFinset_top_eq_card_choose_two]; simp
  | succ m =>
    simpa using numSpanningTrees_top_fin_succ_le_pow m

end IsingModel.Penrose

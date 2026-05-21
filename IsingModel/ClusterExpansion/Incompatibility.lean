import IsingModel.ClusterExpansion.Basic

/-!
# Cluster expansion incompatibility and Ursell coefficients

Mechanical child split from `ClusterExpansion.lean`.
-/

namespace IsingModel

open Finset

/-- **Polymer incompatibility relation** (Step 576, Mayer expansion
foundation): two polymers `P, Q` are *incompatible* iff their supports
overlap, i.e. they share a vertex. This is the negation of
`IsPolymerVertexDisjoint` and is the foundational relation for cluster
decomposition: a *cluster* is (informally) a multi-set of polymers whose
incompatibility graph is connected, and the Mayer/cluster expansion
expresses `log Ξ` as a sum over clusters with the Ursell coefficient.
A non-empty polymer is incompatible with itself, which corresponds to
the standard convention that clusters are multi-sets (not sets). -/
def PolymersIncompatible {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P Q : Finset (Sym2 ι)) : Prop :=
  ¬ Disjoint (polymerSupport P) (polymerSupport Q)

/-- **`PolymersIncompatible` is decidable**: inherits decidability from
`Disjoint` on `Finset`. -/
instance PolymersIncompatible.decidable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P Q : Finset (Sym2 ι)) : Decidable (PolymersIncompatible P Q) := by
  unfold PolymersIncompatible
  exact instDecidableNot

/-- **`PolymersIncompatible` is symmetric**: incompatibility is a
symmetric relation since support overlap is. -/
theorem PolymersIncompatible.symm
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P Q : Finset (Sym2 ι)} (h : PolymersIncompatible P Q) :
    PolymersIncompatible Q P := by
  unfold PolymersIncompatible at *
  rwa [disjoint_comm]

/-- **`PolymersIncompatible` is the negation of `IsPolymerVertexDisjoint`**.
This makes the duality between the compatibility used in the
even-subgraph bijection (`IsPolymerVertexDisjoint`) and the
incompatibility used in cluster decomposition explicit. -/
theorem PolymersIncompatible.iff_not_isPolymerVertexDisjoint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P Q : Finset (Sym2 ι)} :
    PolymersIncompatible P Q ↔ ¬ IsPolymerVertexDisjoint P Q :=
  Iff.rfl

/-- **Characterisation via shared vertex**: two polymers are
incompatible iff there is a vertex in both supports. The forward
direction uses `Finset.not_disjoint_iff`; the backward direction is
immediate. -/
theorem PolymersIncompatible.iff_exists_shared_vertex
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P Q : Finset (Sym2 ι)} :
    PolymersIncompatible P Q ↔
    ∃ v : ι, v ∈ polymerSupport P ∧ v ∈ polymerSupport Q := by
  unfold PolymersIncompatible
  rw [Finset.not_disjoint_iff]

/-- **Self-incompatibility for non-empty polymers**: any non-empty
polymer is incompatible with itself, since its non-empty support
overlaps with itself. This is the dual of
`not_isPolymerVertexDisjoint_self_of_isPolymer` and reflects the
standard convention that clusters in Mayer expansion are multi-sets
where polymers can repeat. -/
theorem PolymersIncompatible.self_of_isPolymer
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : SimpleGraph ι} [Fintype G.edgeSet]
    {P : Finset (Sym2 ι)} (hP : IsPolymer G P) :
    PolymersIncompatible P P :=
  PolymersIncompatible.iff_not_isPolymerVertexDisjoint.mpr
    (not_isPolymerVertexDisjoint_self_of_isPolymer hP)

/-- **Polymer incompatibility graph** (Step 577, Mayer expansion
foundation): the simple graph on `Finset (Sym2 ι)` (the space of all
edge subsets, viewed as candidate polymers) where two distinct polymers
`P, Q` are adjacent iff they are incompatible (share a vertex). Built
via `SimpleGraph.fromRel PolymersIncompatible`, which automatically
provides symmetry and irreflexivity (the diagonal is removed even though
`PolymersIncompatible` is reflexive on non-empty polymers). Connected
components of this graph (or of induced subgraphs on a multi-set of
polymers) are precisely the *clusters* in the Mayer expansion. -/
def incompatibilityGraph {ι : Type*} [Fintype ι] [DecidableEq ι] :
    SimpleGraph (Finset (Sym2 ι)) :=
  SimpleGraph.fromRel PolymersIncompatible

/-- **Adjacency in the incompatibility graph**: two polymers are
adjacent iff they are distinct and incompatible. The disjunction
`PolymersIncompatible P Q ∨ PolymersIncompatible Q P` from
`SimpleGraph.fromRel` collapses to a single conjunct because
`PolymersIncompatible` is symmetric. -/
theorem incompatibilityGraph_adj {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P Q : Finset (Sym2 ι)} :
    (incompatibilityGraph (ι := ι)).Adj P Q ↔
      P ≠ Q ∧ PolymersIncompatible P Q := by
  unfold incompatibilityGraph
  rw [SimpleGraph.fromRel_adj]
  refine ⟨?_, ?_⟩
  · rintro ⟨hne, hPQ | hQP⟩
    · exact ⟨hne, hPQ⟩
    · exact ⟨hne, hQP.symm⟩
  · rintro ⟨hne, hPQ⟩
    exact ⟨hne, Or.inl hPQ⟩

/-- **Decidable adjacency** in the incompatibility graph, derived from
the `Decidable` instance of `PolymersIncompatible` and `DecidableEq` on
`Finset`. Required for finite sums and computational use of the graph. -/
instance incompatibilityGraph_decidableAdj
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    DecidableRel (incompatibilityGraph (ι := ι)).Adj := by
  intro P Q
  rw [incompatibilityGraph_adj]
  exact instDecidableAnd

/-- **Polymer-sequence incompatibility graph** (Step 579, Mayer
expansion foundation): given a sequence `ω : α → Finset (Sym2 ι)` of
polymers indexed by an arbitrary type `α`, the *index-side*
incompatibility graph on `α` has `i ~ j` iff `i ≠ j` and
`PolymersIncompatible (ω i) (ω j)`. Built via `SimpleGraph.fromRel`
applied to `fun i j => PolymersIncompatible (ω i) (ω j)`. This
generalises `incompatibilityGraph` (Step 577) — the special case
`α = Finset (Sym2 ι)` and `ω = id` — and supports the multi-set /
sequence-level cluster definition needed for Mayer expansion. -/
def polymerSeqIncompatibilityGraph
    {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (ω : α → Finset (Sym2 ι)) : SimpleGraph α :=
  SimpleGraph.fromRel (fun i j => PolymersIncompatible (ω i) (ω j))

/-- **Adjacency in the polymer-sequence incompatibility graph**:
indices `i, j` are adjacent iff `i ≠ j` and the underlying polymers are
incompatible. The disjunction in `SimpleGraph.fromRel` collapses by
symmetry of `PolymersIncompatible`. -/
theorem polymerSeqIncompatibilityGraph_adj
    {ι α : Type*} [Fintype ι] [DecidableEq ι]
    {ω : α → Finset (Sym2 ι)} {i j : α} :
    (polymerSeqIncompatibilityGraph ω).Adj i j ↔
      i ≠ j ∧ PolymersIncompatible (ω i) (ω j) := by
  unfold polymerSeqIncompatibilityGraph
  rw [SimpleGraph.fromRel_adj]
  refine ⟨?_, ?_⟩
  · rintro ⟨hne, hij | hji⟩
    · exact ⟨hne, hij⟩
    · exact ⟨hne, hji.symm⟩
  · rintro ⟨hne, hij⟩
    exact ⟨hne, Or.inl hij⟩

/-- **Decidable adjacency** for the polymer-sequence incompatibility
graph, given a `DecidableEq` instance on the index type. -/
instance polymerSeqIncompatibilityGraph_decidableAdj
    {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (ω : α → Finset (Sym2 ι)) :
    DecidableRel (polymerSeqIncompatibilityGraph ω).Adj := by
  intro i j
  rw [polymerSeqIncompatibilityGraph_adj]
  exact instDecidableAnd

/-- **Specialisation to the polymer-space graph** (Step 577): the
identity-indexed sequence on the polymer space `Finset (Sym2 ι)`
recovers `incompatibilityGraph`. -/
theorem polymerSeqIncompatibilityGraph_id
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    polymerSeqIncompatibilityGraph (id : Finset (Sym2 ι) → Finset (Sym2 ι)) =
      incompatibilityGraph (ι := ι) := rfl

/-- **Constant polymer sequence gives `K_n`** (Step 647): for a polymer
`P_0` and the constant sequence `ω : Fin n → {P_0}`,
`polymerSeqIncompatibilityGraph ω = ⊤`. Since `P_0` is self-incompatible
(Step 576), every distinct pair `i, j ∈ Fin n` is adjacent. Useful for
the Mayer expansion of one-polymer graphs (where `log(1+x)` Taylor series
emerges). -/
theorem polymerSeqIncompatibilityGraph_const_polymer
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : SimpleGraph ι} [Fintype G.edgeSet]
    {P_0 : Finset (Sym2 ι)} (hP : IsPolymer G P_0) (n : ℕ) :
    polymerSeqIncompatibilityGraph (fun _ : Fin n => P_0) = ⊤ := by
  ext i j
  rw [polymerSeqIncompatibilityGraph_adj, SimpleGraph.top_adj]
  refine ⟨fun ⟨hne, _⟩ => hne, fun hne => ⟨hne, ?_⟩⟩
  exact PolymersIncompatible.self_of_isPolymer hP

/-- **`polymerSeqIncompatibilityGraph_const_polymer` adjacency**
(Step 648): direct corollary — for the constant polymer sequence, two
distinct indices are always adjacent. -/
theorem polymerSeqIncompatibilityGraph_const_polymer_adj
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : SimpleGraph ι} [Fintype G.edgeSet]
    {P_0 : Finset (Sym2 ι)} (hP : IsPolymer G P_0)
    {n : ℕ} {i j : Fin n} (hne : i ≠ j) :
    (polymerSeqIncompatibilityGraph (fun _ : Fin n => P_0)).Adj i j := by
  rw [polymerSeqIncompatibilityGraph_adj]
  exact ⟨hne, PolymersIncompatible.self_of_isPolymer hP⟩

/-- **Cluster polymer sequence** (Step 580, Mayer expansion foundation):
a sequence `ω : Fin n → Finset (Sym2 ι)` of polymers (with `n ≥ 1`) is a
*cluster sequence* iff every entry is a polymer of `G` and the
index-side incompatibility graph on `Fin n` (Step 579) is `Connected`.
This is the sequence-level analogue of `IsClusterPolymerSet` (Step 578),
allowing multiplicities — the same polymer may appear at multiple
indices. The Mayer expansion sums over cluster sequences (modulo
permutation symmetry, divided by `n!`) weighted by the Ursell
coefficient. -/
def IsClusterPolymerSequence {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {n : ℕ} (_hn : 1 ≤ n) (ω : Fin n → Finset (Sym2 ι)) : Prop :=
  (∀ i : Fin n, IsPolymer G (ω i)) ∧
  (polymerSeqIncompatibilityGraph ω).Connected

/-- **Singleton cluster sequence**: any one-element sequence
`ω : Fin 1 → Finset (Sym2 ι)` whose single entry is a polymer is a
cluster sequence. The index-side graph on `Fin 1` is `Connected`
because there is only one vertex (`Reachable.refl`). -/
theorem IsClusterPolymerSequence.singleton
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {ω : Fin 1 → Finset (Sym2 ι)} (hω : IsPolymer G (ω 0)) :
    IsClusterPolymerSequence G (n := 1) (le_refl 1) ω := by
  refine ⟨?_, ?_⟩
  · intro i
    have : i = 0 := Fin.fin_one_eq_zero i
    exact this ▸ hω
  · refine { preconnected := ?_, nonempty := ⟨0⟩ }
    intro u v
    have huv : u = v := Subsingleton.elim u v
    exact huv ▸ SimpleGraph.Reachable.refl u

/-- **Cluster-sequence activity** (Step 581, Mayer expansion foundation):
for a cluster sequence `ω : Fin n → Finset (Sym2 ι)` and an activity
parameter `t : ℝ`, the activity factor is the monomial product
`z(ω) = ∏ i, t ^ |ω i|`. This is the factor multiplying the Ursell
coefficient in the Mayer expansion
`log Ξ = ∑_{n ≥ 1} ∑_ω ϕ^T(ω) · z(ω)` (the `1/n!` factor is absorbed
into `ursellCoefficient`; cf. Step 583). -/
def clusterSeqActivity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ℝ) {n : ℕ} (ω : Fin n → Finset (Sym2 ι)) : ℝ :=
  ∏ i : Fin n, t ^ (ω i).card

/-- **Activity at a singleton sequence**: `z(ω) = t ^ |ω 0|` for
`ω : Fin 1 → polymer`. The product over `Fin 1` collapses to the value
at the single index. -/
theorem clusterSeqActivity_singleton {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ℝ) (ω : Fin 1 → Finset (Sym2 ι)) :
    clusterSeqActivity t ω = t ^ (ω 0).card := by
  unfold clusterSeqActivity
  rw [Fin.prod_univ_one]

/-- **Activity is non-negative for non-negative activity**: when
`0 ≤ t`, every factor `t ^ |ω i| ≥ 0`, so the product is non-negative. -/
theorem clusterSeqActivity_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {t : ℝ} (ht : 0 ≤ t) {n : ℕ} (ω : Fin n → Finset (Sym2 ι)) :
    0 ≤ clusterSeqActivity t ω := by
  unfold clusterSeqActivity
  exact Finset.prod_nonneg (fun i _ => pow_nonneg ht _)

/-- **Activity at the empty sequence (`n = 0`)**: the empty product
equals `1`, regardless of `t`. -/
theorem clusterSeqActivity_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ℝ) (ω : Fin 0 → Finset (Sym2 ι)) :
    clusterSeqActivity t ω = 1 := by
  unfold clusterSeqActivity
  rw [Fin.prod_univ_zero]

/-- **Connected spanning edge subsets** (Step 582, Mayer expansion
foundation): for a finite-vertex SimpleGraph `G`, the `Finset` of edge
subsets `S ⊆ G.edgeFinset` such that the SimpleGraph reconstructed from
`S` (with vertex set `V`) is `Connected`. The Ursell coefficient of a
cluster sequence will be the alternating-sign sum
`(∑_{S ∈ connectedSpanningEdgeSubsets G(ω)} (-1)^|S|) / n!` (cf. Step 583). -/
noncomputable def connectedSpanningEdgeSubsets {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Finset (Finset (Sym2 V)) :=
  G.edgeFinset.powerset.filter
    (fun S => (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 V))).Connected)

/-- **Membership in `connectedSpanningEdgeSubsets`**: `S` belongs iff
`S ⊆ G.edgeFinset` and the SimpleGraph from `S` is connected. -/
theorem mem_connectedSpanningEdgeSubsets {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {S : Finset (Sym2 V)} :
    S ∈ connectedSpanningEdgeSubsets G ↔
      S ⊆ G.edgeFinset ∧
      (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 V))).Connected := by
  unfold connectedSpanningEdgeSubsets
  rw [Finset.mem_filter, Finset.mem_powerset]

/-- **Ursell (truncated) coefficient** (Step 583, Mayer expansion):
for a polymer sequence `ω : Fin n → Finset (Sym2 ι)`, the Ursell
coefficient is
  `ϕ^T(ω) = (1/n!) · ∑_{S ∈ connectedSpanningEdgeSubsets G(ω)} (-1)^|S|`,
where `G(ω) = polymerSeqIncompatibilityGraph ω` is the index-side
incompatibility graph on `Fin n`. The Mayer expansion expresses the
logarithm of the polymer partition function as
  `log Ξ = ∑_{n ≥ 1} ∑_{ω ∈ polymers^n} ϕ^T(ω) · z(ω)`,
where `z(ω)` is the activity factor (Step 581). -/
noncomputable def ursellCoefficient
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (ω : Fin n → Finset (Sym2 ι)) : ℝ :=
  (∑ S ∈ connectedSpanningEdgeSubsets (polymerSeqIncompatibilityGraph ω),
    (-1 : ℝ) ^ S.card) / (n.factorial : ℝ)

/-- **Singleton Ursell coefficient**: `ϕ^T(ω) = 1` for any one-element
sequence `ω : Fin 1 → polymer`. The index-side graph on `Fin 1` has no
edges (no `i ≠ j` with `i, j : Fin 1`), so the only edge subset is
`∅`; the spanning subgraph from `∅` on a single vertex is connected.
Sum = `(-1)^0 = 1`, divided by `1! = 1`. -/
theorem ursellCoefficient_singleton
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ω : Fin 1 → Finset (Sym2 ι)) :
    ursellCoefficient ω = 1 := by
  unfold ursellCoefficient
  -- `G(ω).edgeFinset = ∅` on `Fin 1` since there is no `i ≠ j`.
  have h_emptyG : (polymerSeqIncompatibilityGraph ω).edgeFinset = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro e he
    rw [SimpleGraph.mem_edgeFinset] at he
    induction e using Sym2.ind with
    | h a b =>
      have hab : (polymerSeqIncompatibilityGraph ω).Adj a b := he
      rw [polymerSeqIncompatibilityGraph_adj] at hab
      have hab_eq : a = b := Subsingleton.elim a b
      exact hab.1 hab_eq
  -- Connected spanning edge subsets reduces to {∅}.
  have h_set : connectedSpanningEdgeSubsets (polymerSeqIncompatibilityGraph ω) = {∅} := by
    apply Finset.ext
    intro S
    rw [mem_connectedSpanningEdgeSubsets, Finset.mem_singleton]
    constructor
    · rintro ⟨hS_sub, _⟩
      rw [h_emptyG, Finset.subset_empty] at hS_sub
      exact hS_sub
    · intro hS_eq
      refine ⟨?_, ?_⟩
      · rw [hS_eq, h_emptyG]
      · -- The spanning graph on Fin 1 from ∅ is connected (singleton).
        rw [hS_eq]
        refine { preconnected := ?_, nonempty := ⟨0⟩ }
        intro u v
        have huv : u = v := Subsingleton.elim u v
        exact huv ▸ SimpleGraph.Reachable.refl u
  rw [h_set]
  simp [Nat.factorial]

/-- **Pair Ursell coefficient (incompatible)** (Step 585): for
`ω : Fin 2 → polymers` with `PolymersIncompatible (ω 0) (ω 1)`,
`ϕ^T(ω) = -1/2`. The index-side graph `G(ω)` on `Fin 2` has the single
edge `s(0, 1)`; the only connected spanning subgraph is the full graph
itself (the empty edge subset gives a disconnected 2-vertex graph).
Sum = `(-1)^1 = -1`, divided by `2! = 2`. Together with Step 584
(vanishing for compatible/disconnected pairs), this gives the leading
non-trivial Mayer-expansion coefficient
`-(1/2) ∑_{P, Q incompat} z(P) z(Q)`. -/
theorem ursellCoefficient_pair_incompatible
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ω : Fin 2 → Finset (Sym2 ι)}
    (hω : PolymersIncompatible (ω 0) (ω 1)) :
    ursellCoefficient ω = -1/2 := by
  unfold ursellCoefficient
  have h_zero_ne_one : (0 : Fin 2) ≠ (1 : Fin 2) := by decide
  -- G(ω).Adj 0 1.
  have h_adj_01 : (polymerSeqIncompatibilityGraph ω).Adj 0 1 := by
    rw [polymerSeqIncompatibilityGraph_adj]
    exact ⟨h_zero_ne_one, hω⟩
  -- G(ω).edgeFinset = {s(0, 1)}.
  have h_edges :
      (polymerSeqIncompatibilityGraph ω).edgeFinset = {s(0, 1)} := by
    apply Finset.ext
    intro e
    rw [SimpleGraph.mem_edgeFinset, Finset.mem_singleton]
    refine ⟨?_, fun h => h ▸ h_adj_01⟩
    induction e using Sym2.ind with
    | h a b =>
      intro hab
      rw [SimpleGraph.mem_edgeSet, polymerSeqIncompatibilityGraph_adj] at hab
      obtain ⟨h_ne, _⟩ := hab
      fin_cases a <;> fin_cases b <;> simp_all [Sym2.eq_swap]
  -- The spanning graph from `{s(0, 1)}` on `Fin 2` is connected.
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
  -- The empty edge set on `Fin 2` is NOT connected.
  have h_disconn_empty :
      ¬ (SimpleGraph.fromEdgeSet (∅ : Set (Sym2 (Fin 2)))).Connected := by
    intro h
    obtain ⟨w⟩ := h.preconnected 0 1
    cases w with
    | cons hadj _ =>
      rw [SimpleGraph.fromEdgeSet_adj] at hadj
      exact hadj.1
  -- connectedSpanningEdgeSubsets = {{s(0, 1)}}.
  have h_set :
      connectedSpanningEdgeSubsets (polymerSeqIncompatibilityGraph ω) = {{s(0, 1)}} := by
    apply Finset.ext
    intro S
    rw [mem_connectedSpanningEdgeSubsets, h_edges, Finset.mem_singleton]
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
  rw [h_set, Finset.sum_singleton, Finset.card_singleton]
  norm_num [Nat.factorial]

/-- **Ursell coefficient vanishes for disconnected sequences** (Step
584): if the index-side incompatibility graph `G(ω)` is not
`Connected`, then `ϕ^T(ω) = 0`. The Mayer-expansion sum effectively
restricts to *cluster* sequences (Step 580). Argument: any connected
spanning subgraph `fromEdgeSet ↑S` of `G(ω)` (with `S ⊆ G(ω).edgeFinset`)
implies `G(ω)` itself is `Connected` (via `Reachable.mono`), so
disconnected `G(ω)` forces `connectedSpanningEdgeSubsets G(ω) = ∅`. -/
theorem ursellCoefficient_eq_zero_of_disconnected
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (ω : Fin n → Finset (Sym2 ι))
    (h_disc : ¬ (polymerSeqIncompatibilityGraph ω).Connected) :
    ursellCoefficient ω = 0 := by
  unfold ursellCoefficient
  have h_empty :
      connectedSpanningEdgeSubsets (polymerSeqIncompatibilityGraph ω) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro S hS
    rw [mem_connectedSpanningEdgeSubsets] at hS
    obtain ⟨hS_sub, hS_conn⟩ := hS
    apply h_disc
    refine { preconnected := ?_, nonempty := hS_conn.nonempty }
    intro u v
    have h_le : SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin n))) ≤
        polymerSeqIncompatibilityGraph ω := by
      intro a b hab
      rw [SimpleGraph.fromEdgeSet_adj] at hab
      obtain ⟨h_in, _⟩ := hab
      have h_in_finset : s(a, b) ∈ S := h_in
      have h_in_eS :
          s(a, b) ∈ (polymerSeqIncompatibilityGraph ω).edgeFinset :=
        hS_sub h_in_finset
      rwa [SimpleGraph.mem_edgeFinset] at h_in_eS
    exact (hS_conn.preconnected u v).mono h_le
  rw [h_empty, Finset.sum_empty, zero_div]

/-- **Pair Ursell coefficient (compatible)** (Step 586): for
`ω : Fin 2 → polymers` with `¬ PolymersIncompatible (ω 0) (ω 1)`,
`ϕ^T(ω) = 0`. Compatibility means no edge in `G(ω)` between the only
two vertices `0, 1 : Fin 2`; the graph is disconnected and Step 584
applies. -/
theorem ursellCoefficient_pair_compatible
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ω : Fin 2 → Finset (Sym2 ι)}
    (hω : ¬ PolymersIncompatible (ω 0) (ω 1)) :
    ursellCoefficient ω = 0 := by
  apply ursellCoefficient_eq_zero_of_disconnected
  intro h_conn
  obtain ⟨w⟩ := h_conn.preconnected 0 1
  -- A walk from 0 to 1 has a first edge `G(ω).Adj 0 v`. On `Fin 2`,
  -- the only vertex `v ≠ 0` is `1`, so this gives
  -- `PolymersIncompatible (ω 0) (ω 1)` — contradicting the
  -- compatibility hypothesis.
  cases w with
  | @cons _ v _ hadj _ =>
    rw [polymerSeqIncompatibilityGraph_adj] at hadj
    obtain ⟨h_ne, h_inc⟩ := hadj
    apply hω
    fin_cases v
    · exact absurd rfl h_ne
    · exact h_inc

/-- **Pair Ursell coefficient (unified)** (Step 586): unified
case-conditional formula for n=2:
`ϕ^T(ω) = if PolymersIncompatible (ω 0) (ω 1) then -1/2 else 0`.
Combines Step 585 (incompatible: `-1/2`) with Step 586's compatible
case (`= 0`). -/
theorem ursellCoefficient_pair {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ω : Fin 2 → Finset (Sym2 ι)) :
    ursellCoefficient ω =
      (if PolymersIncompatible (ω 0) (ω 1) then -1/2 else 0) := by
  by_cases hω : PolymersIncompatible (ω 0) (ω 1)
  · rw [if_pos hω]
    exact ursellCoefficient_pair_incompatible hω
  · rw [if_neg hω]
    exact ursellCoefficient_pair_compatible hω

end IsingModel

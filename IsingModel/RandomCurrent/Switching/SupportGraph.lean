import IsingModel.RandomCurrent.Switching.Core

/-!
# The support of a current and the simple graph it carries

The edges a current is nonzero at, the simple graph they induce on `↥Λ`, and what the source
set of the current inherits from that graph. The graph `G : SimpleGraph V` and the finite
volume `Λ : Finset V` are arbitrary throughout, and `inducedGraph G Λ` denotes the subgraph
of `G` that `Λ` induces.

`Current.support G Λ n` is the `Finset` of edges of `inducedGraph G Λ` at which `n` is
nonzero; membership in it is `n e ≠ 0`. The support of `n - m` is contained in the support of
`n`, the support is monotone in the pointwise order on currents, and it is empty exactly when
the current is the zero current.

`Current.Adj G Λ n u v` holds when `u` and `v` are distinct and some edge of the support of
`n` contains both. It is irreflexive and symmetric, and at the zero current it is equivalent
to `False`. `Current.toSimpleGraph G Λ n` packages it as a `SimpleGraph ↥Λ` whose adjacency
is that relation; at the zero current that graph is `⊥`, it is bounded above by
`inducedGraph G Λ`, and it is monotone in the pointwise order on currents.

The source set is tied to the support. A vertex of the source set of `n` lies on some edge of
the support, hence has a `Current.Adj`-neighbour; and a vertex `v` such that no `u` satisfies
`Current.Adj G Λ n u v` is not in the source set.

`Current.supportAt G Λ n v` restricts the support to the edges containing `v`. It is
contained in the support and is nonempty at every vertex of the source set. The total
incident degree `Current.degreeAt G Λ n v` is the sum of the multiplicities `n e` over it,
and its cardinality is at most that degree, so the degree is strictly positive at every
vertex of the source set.

The edge-endpoint cardinality, the handshake count that uses it and the `ZMod 2` consequence
of that count are recorded together: the endpoint `Finset` of an edge of `inducedGraph G Λ`
has cardinality `2`; the sum of `Current.degreeAt G Λ n v` over all vertices of `Λ` is twice
the sum of `n e` over all edges; and the sum of `Current.parity G Λ n v` over all vertices is
`0` in `ZMod 2`. A further statement records that the `ℕ`-valued indicator of
`Current.parity G Λ n v ≠ 0`, cast into `ZMod 2`, is that parity again.

Every statement here takes `[DecidableEq ↥Λ]`. The edge-endpoint cardinality is the only one
that does not take `[Fintype (inducedGraph G Λ).edgeSet]`, and it is also the only one whose
statement does not mention a current.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **Membership in `Current.support`**: `e ∈ n.support ↔ n e ≠ 0`.
By definitional unfolding of `support := univ.filter (n e ≠ 0)`. -/
theorem Current.mem_support_iff (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (e : (inducedGraph G Λ).edgeSet) :
    e ∈ n.support G Λ ↔ n e ≠ 0 := by
  classical
  unfold Current.support
  simp [Finset.mem_filter]

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **Sub support is bounded by minuend support**:
`(n - m).support ⊆ n.support`. If `(n - m) e ≠ 0` then `n e - m e > 0`
(truncated `Nat.sub`), so `n e > m e ≥ 0`, hence `n e ≠ 0`. -/
theorem Current.support_sub_subset (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n m : Current G Λ) :
    (n - m).support G Λ ⊆ n.support G Λ := by
  intro e he
  rw [Current.mem_support_iff] at he ⊢
  rw [Current.sub_apply] at he
  omega

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **Support is monotone in the current**: if `m ≤ M` (pointwise),
then `m.support ⊆ M.support`. If `m e ≠ 0` then `m e ≥ 1`, and
`m e ≤ M e` forces `M e ≥ 1 ≠ 0`, i.e. `e ∈ M.support`
(`Current.mem_support_iff`). Sibling of `Current.support_sub_subset`. -/
theorem Current.support_mono_of_le (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    {m M : Current G Λ} (h : m ≤ M) :
    Current.support G Λ m ⊆ Current.support G Λ M := by
  intro e he
  rw [Current.mem_support_iff] at he ⊢
  have hle : m e ≤ M e := h e
  omega

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **Empty support characterizes zero**: `n.support = ∅ ↔ n = 0`.
Forward: every edge has `n e = 0` so `n = 0` by extensionality.
Backward: `support_zero`. -/
theorem Current.support_eq_empty_iff (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) :
    n.support G Λ = ∅ ↔ n = 0 := by
  constructor
  · intro h
    ext e
    have : e ∉ n.support G Λ := by rw [h]; exact Finset.notMem_empty e
    rw [Current.mem_support_iff, not_not] at this
    rw [this]
    rfl
  · rintro rfl
    exact Current.support_zero G Λ

/-- **Current adjacency**: vertices `u, v ∈ ↑Λ` are *adjacent in `n`*
iff they are distinct and connected by an edge in `n.support` (i.e.
some `e` with `n e ≠ 0` containing both `u` and `v`). The vertex
adjacency relation of the multigraph defined by `n`'s active edges,
the foundation for the connectivity-based Aizenman switching argument
(Aizenman 1982 Lemma 4.1 / FV §3.7). -/
def Current.Adj (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (u v : ↑Λ) : Prop :=
  u ≠ v ∧ ∃ e ∈ n.support G Λ,
    u ∈ (e : Sym2 ↑Λ) ∧ v ∈ (e : Sym2 ↑Λ)

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **Current adjacency is irreflexive**: a vertex is never adjacent to itself. -/
theorem Current.Adj_irrefl (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (u : ↑Λ) :
    ¬ n.Adj G Λ u u := by
  rintro ⟨huu, _⟩
  exact huu rfl

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **Current adjacency is symmetric**: `n.Adj u v → n.Adj v u`. -/
theorem Current.Adj_symm (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) {u v : ↑Λ} (h : n.Adj G Λ u v) :
    n.Adj G Λ v u := by
  obtain ⟨hne, e, he, hu, hv⟩ := h
  exact ⟨hne.symm, e, he, hv, hu⟩

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **Zero current has no adjacencies**: `(0 : Current).Adj u v ↔ False`,
since `support 0 = ∅`. -/
theorem Current.Adj_of_zero_iff (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (u v : ↑Λ) :
    (0 : Current G Λ).Adj G Λ u v ↔ False := by
  unfold Current.Adj
  constructor
  · rintro ⟨_, e, he, _, _⟩
    rw [Current.support_zero] at he
    exact (Finset.notMem_empty e he).elim
  · intro h; exact h.elim

/-- **`Current.toSimpleGraph`**: the `SimpleGraph` on `↑Λ` whose
adjacency relation is `Current.Adj` (active-edge adjacency in the
multigraph defined by `n`). The first-class `SimpleGraph` object
enabling mathlib's connectivity / path / component APIs needed for
the switching lemma. -/
def Current.toSimpleGraph (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) : SimpleGraph ↑Λ where
  Adj := n.Adj G Λ
  symm := fun _ _ h => Current.Adj_symm G Λ n h
  loopless := ⟨fun u h => Current.Adj_irrefl G Λ n u h⟩

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **`toSimpleGraph` adjacency unfolding**:
`(n.toSimpleGraph).Adj u v ↔ n.Adj u v` (definitional). -/
@[simp]
theorem Current.toSimpleGraph_adj_iff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (u v : ↑Λ) :
    (n.toSimpleGraph G Λ).Adj u v ↔ n.Adj G Λ u v := Iff.rfl

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **Zero current's `toSimpleGraph` is the empty graph**: by
`Adj_of_zero_iff` (no adjacencies), the SimpleGraph is `⊥`. -/
theorem Current.toSimpleGraph_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ] :
    (0 : Current G Λ).toSimpleGraph G Λ = (⊥ : SimpleGraph ↑Λ) := by
  ext u v
  rw [Current.toSimpleGraph_adj_iff, Current.Adj_of_zero_iff]
  simp [SimpleGraph.bot_adj]

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **`toSimpleGraph` is a subgraph of `inducedGraph`**:
`n.toSimpleGraph G Λ ≤ inducedGraph G Λ`. Each adjacency in
`n.toSimpleGraph` arises from a support edge `e ∈ n.support`, which
satisfies `e.val ∈ (inducedGraph G Λ).edgeSet`; combined with vertex
membership and distinctness, this gives `inducedGraph.Adj` via
`SimpleGraph.adj_iff_exists_edge`. -/
theorem Current.toSimpleGraph_le_inducedGraph
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) :
    n.toSimpleGraph G Λ ≤ inducedGraph G Λ := by
  intro u v h
  rw [Current.toSimpleGraph_adj_iff] at h
  obtain ⟨hne, e, _, hu, hv⟩ := h
  rw [SimpleGraph.adj_iff_exists_edge]
  exact ⟨hne, (e : Sym2 ↑Λ), e.2, hu, hv⟩

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **Support graph is monotone in the current**: if `m ≤ M`
(pointwise), then `m.toSimpleGraph ≤ M.toSimpleGraph` as simple graphs
on `↑Λ`. Every adjacency of `m.toSimpleGraph` arises from a support
edge `e ∈ m.support ⊆ M.support` (`Current.support_mono_of_le`) with
the same two endpoints, hence is an adjacency of `M.toSimpleGraph`
(`Current.Adj`). Consequently reachability is monotone via
`SimpleGraph.Reachable.mono`. -/
theorem Current.toSimpleGraph_mono_of_le (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    {m M : Current G Λ} (h : m ≤ M) :
    Current.toSimpleGraph G Λ m ≤ Current.toSimpleGraph G Λ M := by
  intro u v huv
  rw [Current.toSimpleGraph_adj_iff] at huv ⊢
  obtain ⟨hne, e, he, hu, hv⟩ := huv
  exact ⟨hne, e, Current.support_mono_of_le G Λ h he, hu, hv⟩

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **A source vertex is incident to an active edge**: if
`v ∈ n.sources`, then there exists an edge `e ∈ n.support` containing
`v`. The foundation for the Aizenman switching argument: the boundary
vertices of a current are non-isolated in the active-edge multigraph.
(Aizenman 1982 Lemma 4.1 / FV §3.7.) -/
theorem Current.exists_support_edge_of_mem_sources
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) {v : ↑Λ} (hv : v ∈ n.sources G Λ) :
    ∃ e ∈ n.support G Λ, v ∈ (e : Sym2 ↑Λ) := by
  classical
  by_contra habs
  push Not at habs
  rw [Current.mem_sources_iff] at hv
  apply hv
  rw [Current.parity_eq_degreeAt]
  have hdeg : n.degreeAt G Λ v = 0 := by
    unfold Current.degreeAt
    refine Finset.sum_eq_zero ?_
    intro e _
    by_cases hve : v ∈ (e : Sym2 ↑Λ)
    · rw [if_pos hve]
      by_contra hne
      exact habs e ((Current.mem_support_iff G Λ n e).mpr hne) hve
    · rw [if_neg hve]
  rw [hdeg]
  simp

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **A source vertex has a `Current.Adj` neighbour**: if
`v ∈ n.sources`, then there exists `u` with `n.Adj G Λ u v`, i.e.
`v` is not isolated in `n.toSimpleGraph`. A foundational step toward
the switching lemma's path argument (Aizenman 1982 / FV §3.7):
non-isolation of source vertices is the base case for constructing
walks from source to source in the active-edge graph. Path existence
itself is a downstream consequence, not established here. -/
theorem Current.exists_adj_of_mem_sources
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) {v : ↑Λ} (hv : v ∈ n.sources G Λ) :
    ∃ u, n.Adj G Λ u v := by
  obtain ⟨e, he_supp, hve⟩ := Current.exists_support_edge_of_mem_sources G Λ n hv
  refine ⟨Sym2.Mem.other hve, ?_, e, he_supp, Sym2.other_mem hve, hve⟩
  exact SimpleGraph.edge_other_ne _ e.2 hve

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **Isolated vertices are not sources**: the contrapositive of
`exists_adj_of_mem_sources`. If no `u` is `Current.Adj`-adjacent to
`v`, then `v ∉ n.sources`. Convenient downstream when excluding
potential sources via local isolation. -/
theorem Current.not_mem_sources_of_isolated
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) {v : ↑Λ} (hv : ∀ u, ¬ n.Adj G Λ u v) :
    v ∉ n.sources G Λ := by
  intro hmem
  obtain ⟨u, hadj⟩ := Current.exists_adj_of_mem_sources G Λ n hmem
  exact hv u hadj

/-- **Active edges incident to a vertex**: for a current `n` and a
vertex `v : ↑Λ`, the Finset of edges `e ∈ n.support` containing `v`.
The Finset form of `exists_support_edge_of_mem_sources`, usable in
downstream counting / partitioning arguments for the switching lemma
(Aizenman 1982 / FV §3.7). -/
noncomputable def Current.supportAt (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (v : ↑Λ) :
    Finset ((inducedGraph G Λ).edgeSet) :=
  (n.support G Λ).filter (fun e => v ∈ (e : Sym2 ↑Λ))

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **Membership in `Current.supportAt`**: `e ∈ n.supportAt v ↔
e ∈ n.support ∧ v ∈ (e : Sym2 ↑Λ)`. -/
theorem Current.mem_supportAt_iff (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (v : ↑Λ) (e : (inducedGraph G Λ).edgeSet) :
    e ∈ n.supportAt G Λ v ↔ e ∈ n.support G Λ ∧ v ∈ (e : Sym2 ↑Λ) := by
  classical
  unfold Current.supportAt
  exact Finset.mem_filter

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **`supportAt` is contained in `support`**: edges at a vertex are
in particular active edges. -/
theorem Current.supportAt_subset_support (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (v : ↑Λ) :
    n.supportAt G Λ v ⊆ n.support G Λ := by
  classical
  unfold Current.supportAt
  exact Finset.filter_subset _ _

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **Source vertices have non-empty `supportAt`**: the Finset form
of `exists_support_edge_of_mem_sources`. If `v ∈ n.sources`, then
`(n.supportAt v).Nonempty`. -/
theorem Current.supportAt_nonempty_of_mem_sources
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) {v : ↑Λ} (hv : v ∈ n.sources G Λ) :
    (n.supportAt G Λ v).Nonempty := by
  obtain ⟨e, he_supp, hve⟩ := Current.exists_support_edge_of_mem_sources G Λ n hv
  exact ⟨e, (Current.mem_supportAt_iff G Λ n v e).mpr ⟨he_supp, hve⟩⟩

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **`degreeAt` equals the sum of `n` over `supportAt`**: the
ℕ-valued total incident degree is recovered by summing `n e` over
the Finset of active incident edges at `v`. The definitional
expression over all edges with an `if`-guard contracts to the
support-restricted sum, since edges contributing zero (either not
incident to `v` or with `n e = 0`) vanish. -/
theorem Current.degreeAt_eq_sum_supportAt
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (v : ↑Λ) :
    n.degreeAt G Λ v = ∑ e ∈ n.supportAt G Λ v, n e := by
  classical
  unfold Current.degreeAt
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_subset
  · intro e he
    rw [Current.mem_supportAt_iff] at he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, he.2⟩
  · intro e he he'
    rw [Finset.mem_filter] at he
    rw [Current.mem_supportAt_iff] at he'
    push Not at he'
    by_contra hne
    exact he' ((Current.mem_support_iff G Λ n e).mpr hne) he.2

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **`supportAt` cardinality is bounded by `degreeAt`**: each
active incident edge contributes at least `1` to `n.degreeAt v`
(since `n e ≠ 0` on the support gives `n e ≥ 1` in ℕ), so the
edge count is at most the total degree. -/
theorem Current.card_supportAt_le_degreeAt
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (v : ↑Λ) :
    (n.supportAt G Λ v).card ≤ n.degreeAt G Λ v := by
  rw [Current.degreeAt_eq_sum_supportAt, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro e he
  rw [Current.mem_supportAt_iff, Current.mem_support_iff] at he
  exact Nat.one_le_iff_ne_zero.mpr he.1

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **`degreeAt` is positive at a source**: `v ∈ n.sources` forces
at least one active incident edge (step 94), and by the
`supportAt`↔`degreeAt` bridge the total degree is at least that
edge's count, which is positive. -/
theorem Current.degreeAt_pos_of_mem_sources
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) {v : ↑Λ} (hv : v ∈ n.sources G Λ) :
    0 < n.degreeAt G Λ v := by
  have hne := Current.supportAt_nonempty_of_mem_sources G Λ n hv
  have hcard : 0 < (n.supportAt G Λ v).card := Finset.card_pos.mpr hne
  exact lt_of_lt_of_le hcard (Current.card_supportAt_le_degreeAt G Λ n v)

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **Edge vertex set has cardinality two**: each edge `e` in the
`inducedGraph G Λ` edgeSet has `(e : Sym2 ↑Λ).toFinset.card = 2`,
since edges are non-diagonal. The building block for the multigraph
handshake identity. -/
theorem Current.edgeSet_toFinset_card_eq_two
    (G : SimpleGraph V) (Λ : Finset V)
    [DecidableEq ↑Λ]
    (e : (inducedGraph G Λ).edgeSet) :
    (e : Sym2 ↑Λ).toFinset.card = 2 :=
  Sym2.card_toFinset_of_not_isDiag _
    (SimpleGraph.not_isDiag_of_mem_edgeSet _ e.2)

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **Multigraph handshake identity**: `∑_v n.degreeAt v
= 2 * ∑_e n e`. Each edge of multiplicity `n e` contributes to the
degree of its two endpoints, so the vertex-side total degree is
exactly twice the edge-side total multiplicity. Specialization of
`Current.sum_degreeAt_smul` at `M := ℕ`, `f := fun _ => 1`, combined
with `edgeSet_toFinset_card_eq_two`. -/
theorem Current.sum_degreeAt_eq_two_mul_total
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) :
    ∑ v : ↑Λ, n.degreeAt G Λ v
      = 2 * ∑ e : (inducedGraph G Λ).edgeSet, n e := by
  classical
  unfold Current.degreeAt
  rw [Finset.sum_comm]
  have key : ∀ (e : (inducedGraph G Λ).edgeSet),
      (∑ v : ↑Λ, if v ∈ (e : Sym2 ↑Λ) then n e else 0) = 2 * n e := by
    intro e
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    congr 1
    have hfilter : ((Finset.univ : Finset ↑Λ).filter
        (fun v => v ∈ (e : Sym2 ↑Λ)))
          = (e : Sym2 ↑Λ).toFinset := by
      ext v
      simp [Sym2.mem_toFinset]
    rw [hfilter]
    exact Current.edgeSet_toFinset_card_eq_two G Λ e
  simp_rw [key]
  rw [← Finset.mul_sum]

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **Sum of parities over all vertices is zero in `ZMod 2`**: an
immediate `ZMod 2` consequence of the handshake identity, since
`2 * X` casts to zero. This is the mod-2 form of "the number of
odd-degree vertices is even", used in the next step to establish
`Even (sources).card` (switching-lemma prerequisite). -/
theorem Current.sum_parity_eq_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) :
    ∑ v : ↑Λ, n.parity G Λ v = (0 : ZMod 2) := by
  simp only [Current.parity_eq_degreeAt]
  rw [← Nat.cast_sum, Current.sum_degreeAt_eq_two_mul_total]
  push_cast
  rw [show (2 : ZMod 2) = 0 from by decide]
  ring

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **Indicator cast to `ZMod 2` equals parity**: since `parity v`
takes values only in `{0, 1} ⊆ ZMod 2`, the ℕ-valued indicator
`if parity v ≠ 0 then 1 else 0` casts back to `parity v`. -/
theorem Current.cast_indicator_parity
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (v : ↑Λ) :
    ((if n.parity G Λ v ≠ 0 then 1 else 0 : ℕ) : ZMod 2) = n.parity G Λ v := by
  generalize n.parity G Λ v = p
  fin_cases p <;> decide


end Ambient
end IsingModel

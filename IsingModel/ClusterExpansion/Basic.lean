import IsingModel.Conditioning
import IsingModel.PhaseTransition
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.Circulant

/-!
# Cluster expansion basic polymer definitions

Mechanical child split from `ClusterExpansion.lean`.
-/

namespace IsingModel

open Finset

/-- **Even subgraph predicate**: `X ⊆ G.edgeFinset` such that every
vertex has an even number of incident edges in `X`. The set of even
subgraphs is the cycle space of `G` (over `F_2`); it is the natural
domain for the FV (3.45) sum
`∑_{X ⊆ E, even-degree} tanh(β·J)^|X|`. -/
structure IsEvenSubgraph {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (X : Finset (Sym2 ι)) : Prop where
  /-- `X` is contained in the edge set of `G`. -/
  subset : X ⊆ G.edgeFinset
  /-- Every vertex `v` has an even number of incident edges in `X`. -/
  even_degree : ∀ v : ι, Even ((X.filter (v ∈ ·)).card)

/-- **The empty edge set is an even subgraph**: vacuously, every vertex
has zero (and zero is even) incident edges. -/
theorem IsEvenSubgraph.empty {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    IsEvenSubgraph G (∅ : Finset (Sym2 ι)) where
  subset := empty_subset _
  even_degree v := by simp

/-- **Even-subgraph predicate is decidable** (it is a conjunction of two
decidable conditions). -/
instance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (X : Finset (Sym2 ι)) :
    Decidable (IsEvenSubgraph G X) := by
  refine decidable_of_iff
    (X ⊆ G.edgeFinset ∧ ∀ v : ι, Even ((X.filter (v ∈ ·)).card)) ?_
  exact ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩⟩

/-- **Union of disjoint even subgraphs is an even subgraph**: when two
even subgraphs `X, Y ⊆ G.edgeFinset` are edge-disjoint, their union is
also an even subgraph.

This is the key building block for the cluster decomposition: a
compatible polymer family unions to an even subgraph. -/
theorem IsEvenSubgraph.union_disjoint {ι : Type*} [DecidableEq ι]
    {G : SimpleGraph ι} [Fintype G.edgeSet]
    {X Y : Finset (Sym2 ι)}
    (hX : IsEvenSubgraph G X) (hY : IsEvenSubgraph G Y)
    (hd : Disjoint X Y) :
    IsEvenSubgraph G (X ∪ Y) where
  subset := by
    intro e he
    rcases Finset.mem_union.mp he with he | he
    · exact hX.subset he
    · exact hY.subset he
  even_degree v := by
    have hX' := hX.even_degree v
    have hY' := hY.even_degree v
    have hfilter : (X ∪ Y).filter (v ∈ ·) =
        X.filter (v ∈ ·) ∪ Y.filter (v ∈ ·) :=
      Finset.filter_union _ _ _
    have hd' : Disjoint (X.filter (v ∈ ·)) (Y.filter (v ∈ ·)) :=
      hd.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    rw [hfilter, Finset.card_union_of_disjoint hd']
    exact hX'.add hY'

/-- **Bridging lemma**: an `X ⊆ G.edgeFinset` is an `IsEvenSubgraph G X`
iff every vertex has even incidence in `X`. This relates the new
predicate to the inline form used by FV (3.45)
`partitionFunction_high_temp_expansion_h_zero_closed`. -/
theorem isEvenSubgraph_iff {ι : Type*} [DecidableEq ι]
    {G : SimpleGraph ι} [Fintype G.edgeSet]
    {X : Finset (Sym2 ι)} (hX : X ⊆ G.edgeFinset) :
    IsEvenSubgraph G X ↔ ∀ v : ι, Even ((X.filter (v ∈ ·)).card) :=
  ⟨fun h => h.even_degree, fun h => ⟨hX, h⟩⟩

/-- **Edge-adjacency relation in an edge subset**: two edges in `X` are
adjacent if they share a vertex. Used to define edge-connectedness of
an edge subset. -/
def edgeAdjacentIn {ι : Type*} (X : Finset (Sym2 ι))
    (e f : Sym2 ι) : Prop :=
  e ∈ X ∧ f ∈ X ∧ ∃ v : ι, v ∈ e ∧ v ∈ f

/-- **Edge-adjacency is symmetric**: `edgeAdjacentIn X e f ↔
edgeAdjacentIn X f e` (since "share a vertex" is a symmetric relation
on edges). -/
theorem edgeAdjacentIn_symm {ι : Type*} {X : Finset (Sym2 ι)}
    {e f : Sym2 ι} :
    edgeAdjacentIn X e f → edgeAdjacentIn X f e := by
  rintro ⟨he, hf, v, hve, hvf⟩
  exact ⟨hf, he, v, hvf, hve⟩

/-- **`Relation.ReflTransGen edgeAdjacentIn` is symmetric**:
follows from `edgeAdjacentIn` being symmetric and the fact that the
reflexive-transitive closure of a symmetric relation is symmetric. -/
theorem reflTransGen_edgeAdjacentIn_symmetric {ι : Type*}
    (X : Finset (Sym2 ι)) :
    Symmetric (Relation.ReflTransGen (edgeAdjacentIn X)) :=
  Relation.ReflTransGen.symmetric fun {_ _} h => edgeAdjacentIn_symm h

/-- **Edge-connectedness of an edge subset**: any two edges in `X` are
connected by a chain of edge-adjacency steps within `X`. The empty set
is vacuously edge-connected, and a single edge is also trivially
edge-connected (the reflexive case). -/
def IsEdgeConnected {ι : Type*} (X : Finset (Sym2 ι)) : Prop :=
  ∀ e₁ ∈ X, ∀ e₂ ∈ X,
    Relation.ReflTransGen (edgeAdjacentIn X) e₁ e₂

/-- **Edge-connected component of `e` in `X`**: the set of edges in `X`
reachable from `e` by chains of edge-adjacency steps within `X`. This
is the building block for the connected-components decomposition of an
even subgraph into polymers. -/
noncomputable def edgeComponent {ι : Type*} (X : Finset (Sym2 ι))
    (e : Sym2 ι) : Finset (Sym2 ι) := by
  classical
  exact X.filter (fun f => Relation.ReflTransGen (edgeAdjacentIn X) e f)

/-- **`edgeComponent X e ⊆ X`**: components are sub-finsets. -/
theorem edgeComponent_subset {ι : Type*} (X : Finset (Sym2 ι))
    (e : Sym2 ι) :
    edgeComponent X e ⊆ X := by
  classical
  unfold edgeComponent
  exact Finset.filter_subset _ _

/-- **Membership in `edgeComponent`**: `f ∈ edgeComponent X e ↔
f ∈ X ∧ ReflTransGen (edgeAdjacentIn X) e f`. -/
theorem mem_edgeComponent {ι : Type*} {X : Finset (Sym2 ι)}
    {e f : Sym2 ι} :
    f ∈ edgeComponent X e ↔
      f ∈ X ∧ Relation.ReflTransGen (edgeAdjacentIn X) e f := by
  classical
  unfold edgeComponent
  rw [Finset.mem_filter]

/-- **`e ∈ edgeComponent X e` whenever `e ∈ X`**: components contain
their basepoint. -/
theorem self_mem_edgeComponent {ι : Type*} {X : Finset (Sym2 ι)}
    {e : Sym2 ι} (he : e ∈ X) :
    e ∈ edgeComponent X e :=
  mem_edgeComponent.mpr ⟨he, Relation.ReflTransGen.refl⟩

/-- **`edgeComponent` consistency under reachability**: if `f` is in
`edgeComponent X e`, then `edgeComponent X f ⊆ edgeComponent X e`.
Anything reachable from `f` is, by transitivity, also reachable from
`e`. -/
theorem edgeComponent_subset_of_mem {ι : Type*} {X : Finset (Sym2 ι)}
    {e f : Sym2 ι} (hf : f ∈ edgeComponent X e) :
    edgeComponent X f ⊆ edgeComponent X e := by
  intro g hg
  rw [mem_edgeComponent] at hf hg ⊢
  exact ⟨hg.1, hf.2.trans hg.2⟩

/-- **`edgeComponent` symmetric consistency**: if `f ∈ edgeComponent X e`,
then `edgeComponent X e ⊆ edgeComponent X f`. Combined with
`edgeComponent_subset_of_mem`, the components are equal. -/
theorem edgeComponent_subset_of_mem_symm {ι : Type*} {X : Finset (Sym2 ι)}
    {e f : Sym2 ι} (hf : f ∈ edgeComponent X e) :
    edgeComponent X e ⊆ edgeComponent X f := by
  intro g hg
  rw [mem_edgeComponent] at hf hg ⊢
  refine ⟨hg.1, ?_⟩
  -- Use symmetry: e and f are connected, so f and e are connected.
  have hef_symm := reflTransGen_edgeAdjacentIn_symmetric X hf.2
  exact hef_symm.trans hg.2

/-- **`edgeComponent` equality from membership**: if `f ∈ edgeComponent X e`,
then `edgeComponent X e = edgeComponent X f`. -/
theorem edgeComponent_eq_of_mem {ι : Type*} {X : Finset (Sym2 ι)}
    {e f : Sym2 ι} (hf : f ∈ edgeComponent X e) :
    edgeComponent X e = edgeComponent X f :=
  Finset.Subset.antisymm
    (edgeComponent_subset_of_mem_symm hf)
    (edgeComponent_subset_of_mem hf)

/-- **Two `edgeComponent`s are either equal or disjoint**: any
intersection forces equality, since shared elements give equal
components (via `edgeComponent_eq_of_mem`). -/
theorem edgeComponent_eq_or_disjoint {ι : Type*} {X : Finset (Sym2 ι)}
    (e f : Sym2 ι) :
    edgeComponent X e = edgeComponent X f ∨
      Disjoint (edgeComponent X e) (edgeComponent X f) := by
  classical
  by_cases h : Disjoint (edgeComponent X e) (edgeComponent X f)
  · exact Or.inr h
  · refine Or.inl ?_
    rw [Finset.not_disjoint_iff] at h
    obtain ⟨g, hge, hgf⟩ := h
    -- `g ∈ both ⇒ edgeComponent X e = edgeComponent X g = edgeComponent X f`.
    rw [edgeComponent_eq_of_mem hge, ← edgeComponent_eq_of_mem hgf]

/-- **Polymer**: a non-empty connected even subgraph. In the
high-temperature cluster expansion of the lattice Ising model, the FV
(3.45) sum `∑_{X ⊆ E even} tanh(β·J)^|X|` decomposes into a sum over
edge-disjoint families of polymers via the connected-component
decomposition of `X`. -/
structure IsPolymer {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (P : Finset (Sym2 ι)) : Prop where
  /-- `P` is an even subgraph of `G`. -/
  isEven : IsEvenSubgraph G P
  /-- `P` is non-empty (the empty even subgraph is excluded). -/
  nonempty : P.Nonempty
  /-- `P` is edge-connected. -/
  connected : IsEdgeConnected P

/-- **Edge-connectedness is reflexive on its singletons**: a single
edge `{e}` is edge-connected. -/
theorem isEdgeConnected_singleton {ι : Type*} (e : Sym2 ι) :
    IsEdgeConnected ({e} : Finset (Sym2 ι)) := by
  intro e₁ he₁ e₂ he₂
  rw [Finset.mem_singleton] at he₁ he₂
  subst he₁; subst he₂
  exact Relation.ReflTransGen.refl

/-- **Polymer support**: the set of vertices touched by some edge of
`P`. For polymers in the cluster expansion of the lattice Ising model,
the support is the natural "geometric" set on which the polymer lives. -/
def polymerSupport {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Finset (Sym2 ι)) : Finset ι :=
  Finset.univ.filter (fun v => ∃ e ∈ P, v ∈ e)

/-- **Membership in `polymerSupport`**: `v ∈ polymerSupport P` iff `v`
is contained in some edge of `P`. -/
theorem mem_polymerSupport {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P : Finset (Sym2 ι)} {v : ι} :
    v ∈ polymerSupport P ↔ ∃ e ∈ P, v ∈ e := by
  unfold polymerSupport
  simp [Finset.mem_filter]

/-- **`polymerSupport ∅ = ∅`**. -/
@[simp]
theorem polymerSupport_empty {ι : Type*} [Fintype ι] [DecidableEq ι] :
    polymerSupport (∅ : Finset (Sym2 ι)) = ∅ := by
  ext v
  simp [mem_polymerSupport]

/-- **`polymerSupport (Γ.biUnion id) = Γ.biUnion polymerSupport`**:
support of a biUnion equals biUnion of supports. -/
theorem polymerSupport_biUnion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Γ : Finset (Finset (Sym2 ι))) :
    polymerSupport (Γ.biUnion id) = Γ.biUnion polymerSupport := by
  ext v
  rw [mem_polymerSupport, Finset.mem_biUnion]
  refine ⟨?_, ?_⟩
  · rintro ⟨e, he, hv⟩
    rw [Finset.mem_biUnion] at he
    obtain ⟨P, hP, hePid⟩ := he
    refine ⟨P, hP, ?_⟩
    rw [mem_polymerSupport]
    exact ⟨e, hePid, hv⟩
  · rintro ⟨P, hP, hvP⟩
    rw [mem_polymerSupport] at hvP
    obtain ⟨e, heP, hv⟩ := hvP
    refine ⟨e, ?_, hv⟩
    rw [Finset.mem_biUnion]
    exact ⟨P, hP, heP⟩

/-- **`polymerSupport (P ∪ Q) = polymerSupport P ∪ polymerSupport Q`**:
support is union-distributive. -/
theorem polymerSupport_union {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P Q : Finset (Sym2 ι)) :
    polymerSupport (P ∪ Q) = polymerSupport P ∪ polymerSupport Q := by
  ext v
  rw [Finset.mem_union, mem_polymerSupport, mem_polymerSupport,
      mem_polymerSupport]
  refine ⟨?_, ?_⟩
  · rintro ⟨e, he, hv⟩
    rcases Finset.mem_union.mp he with he | he
    · exact Or.inl ⟨e, he, hv⟩
    · exact Or.inr ⟨e, he, hv⟩
  · rintro (⟨e, he, hv⟩ | ⟨e, he, hv⟩)
    · exact ⟨e, Finset.mem_union_left _ he, hv⟩
    · exact ⟨e, Finset.mem_union_right _ he, hv⟩

/-- **`edgeComponent` absorbs incident edges**: if some edge `f` of the
component contains `v`, then every `X`-edge `e'` containing `v` is also
in the component. This is the closure-under-incidence property that
ensures connected components have well-defined vertex degrees.

Proof: edge-adjacency through the shared vertex `v` extends the
reach-relation by one step. -/
theorem edgeComponent_absorbs_incident
    {ι : Type*}
    {X : Finset (Sym2 ι)} {e f : Sym2 ι} {v : ι}
    (hf : f ∈ edgeComponent X e) (hvf : v ∈ f)
    {e' : Sym2 ι} (he' : e' ∈ X) (hv' : v ∈ e') :
    e' ∈ edgeComponent X e := by
  rw [mem_edgeComponent] at hf
  obtain ⟨hfX, hef⟩ := hf
  rw [mem_edgeComponent]
  refine ⟨he', ?_⟩
  have h_step : edgeAdjacentIn X f e' := ⟨hfX, he', v, hvf, hv'⟩
  exact hef.tail h_step

/-- **edgeComponent of an even subgraph is even**: if `X` is an even
subgraph of `G`, then so is `edgeComponent X e` for every `e`.

Proof per vertex `v`:
- Case `v ∈ polymerSupport (edgeComponent X e)`: by
  `edgeComponent_absorbs_incident`, every `X`-edge at `v` is in the
  component, so the component-degree at `v` equals the `X`-degree at
  `v`, which is even.
- Case `v ∉ polymerSupport (edgeComponent X e)`: then no edge of the
  component contains `v`, so component-degree at `v` is zero, even. -/
theorem IsEvenSubgraph.toEdgeComponent
    {ι : Type*} [DecidableEq ι]
    {G : SimpleGraph ι} [Fintype G.edgeSet]
    {X : Finset (Sym2 ι)} (hX : IsEvenSubgraph G X) (e : Sym2 ι) :
    IsEvenSubgraph G (edgeComponent X e) where
  subset := (edgeComponent_subset X e).trans hX.subset
  even_degree v := by
    by_cases hv : ∃ f ∈ edgeComponent X e, v ∈ f
    · -- The component-incident set at v equals X-incident set at v.
      obtain ⟨f, hf, hvf⟩ := hv
      have h_filter_eq :
          (edgeComponent X e).filter (v ∈ ·) = X.filter (v ∈ ·) := by
        apply Finset.Subset.antisymm
        · intro g hg
          rw [Finset.mem_filter] at hg ⊢
          exact ⟨(edgeComponent_subset X e) hg.1, hg.2⟩
        · intro g hg
          rw [Finset.mem_filter] at hg ⊢
          exact ⟨edgeComponent_absorbs_incident hf hvf hg.1 hg.2, hg.2⟩
      rw [h_filter_eq]
      exact hX.even_degree v
    · -- Component has no incidence at v, so count is zero.
      have hv' : ∀ f ∈ edgeComponent X e, v ∉ f := by
        intro f hf hvf
        exact hv ⟨f, hf, hvf⟩
      have h_filter_empty :
          (edgeComponent X e).filter (v ∈ ·) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro f hf
        rw [Finset.mem_filter] at hf
        exact hv' f hf.1 hf.2
      rw [h_filter_empty, Finset.card_empty]
      exact ⟨0, rfl⟩

/-- **Lifting reachability to the component**: if `f ∈ edgeComponent X e`,
then there is a chain in `edgeAdjacentIn (edgeComponent X e)` from `e`
to `f` (not just in the larger relation `edgeAdjacentIn X`). -/
theorem reflTransGen_edgeAdjacentIn_within_component
    {ι : Type*} {X : Finset (Sym2 ι)} {e f : Sym2 ι}
    (h : Relation.ReflTransGen (edgeAdjacentIn X) e f) :
    Relation.ReflTransGen (edgeAdjacentIn (edgeComponent X e)) e f := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail h_chain h_step ih =>
    rename_i a b
    have ha_comp : a ∈ edgeComponent X e :=
      mem_edgeComponent.mpr ⟨h_step.1, h_chain⟩
    have hb_comp : b ∈ edgeComponent X e :=
      mem_edgeComponent.mpr ⟨h_step.2.1,
        Relation.ReflTransGen.tail h_chain h_step⟩
    have h_step' : edgeAdjacentIn (edgeComponent X e) a b :=
      ⟨ha_comp, hb_comp, h_step.2.2⟩
    exact Relation.ReflTransGen.tail ih h_step'

/-- **`edgeComponent X e` is edge-connected**: any two edges in the
component are linked by a chain of edge-adjacency steps within the
component. -/
theorem isEdgeConnected_edgeComponent
    {ι : Type*} {X : Finset (Sym2 ι)} (e : Sym2 ι) :
    IsEdgeConnected (edgeComponent X e) := by
  intro f hf g hg
  -- Use lift-to-component for both f and g, then symmetry + transitivity.
  rw [mem_edgeComponent] at hf hg
  have hef := reflTransGen_edgeAdjacentIn_within_component hf.2
  have heg := reflTransGen_edgeAdjacentIn_within_component hg.2
  have hfe := reflTransGen_edgeAdjacentIn_symmetric (edgeComponent X e) hef
  exact hfe.trans heg

/-- **`edgeComponent X e` is a polymer when `X` is even and `e ∈ X`**:
combines all the previous component lemmas — non-empty (contains `e`),
even-degree (Step 536), and edge-connected (Step 537). -/
theorem IsEvenSubgraph.edgeComponent_isPolymer
    {ι : Type*} [DecidableEq ι]
    {G : SimpleGraph ι} [Fintype G.edgeSet]
    {X : Finset (Sym2 ι)} (hX : IsEvenSubgraph G X)
    {e : Sym2 ι} (he : e ∈ X) :
    IsPolymer G (edgeComponent X e) where
  isEven := hX.toEdgeComponent e
  nonempty := ⟨e, self_mem_edgeComponent he⟩
  connected := isEdgeConnected_edgeComponent e

/-- **Polymer decomposition of an edge subset**: the (deduplicated)
collection of edge components of `X`, indexed by representative
edges in `X`.

For an even subgraph `X`, this is the set of polymers in the canonical
decomposition `X = Γ.biUnion id` where `Γ` is vertex-disjoint
compatible (proved in subsequent PRs). -/
noncomputable def polymerDecomposition {ι : Type*} [DecidableEq ι]
    (X : Finset (Sym2 ι)) : Finset (Finset (Sym2 ι)) := by
  classical
  exact X.image (fun e => edgeComponent X e)

/-- **Membership in `polymerDecomposition`**: a `C` is in the
decomposition iff there exists `e ∈ X` with `C = edgeComponent X e`. -/
theorem mem_polymerDecomposition {ι : Type*} [DecidableEq ι]
    {X : Finset (Sym2 ι)} {C : Finset (Sym2 ι)} :
    C ∈ polymerDecomposition X ↔ ∃ e ∈ X, edgeComponent X e = C := by
  classical
  unfold polymerDecomposition
  rw [Finset.mem_image]

/-- **`polymerDecomposition X` covers `X`**:
`(polymerDecomposition X).biUnion id = X`.

Forward: every element of the biUnion is in some component, which is
a subset of `X`. Backward: every `e ∈ X` is in `edgeComponent X e`
(Step 532), which is a member of the decomposition. -/
theorem polymerDecomposition_biUnion_id {ι : Type*} [DecidableEq ι]
    (X : Finset (Sym2 ι)) :
    (polymerDecomposition X).biUnion id = X := by
  ext e
  rw [Finset.mem_biUnion]
  refine ⟨?_, ?_⟩
  · rintro ⟨C, hC, heC⟩
    rw [mem_polymerDecomposition] at hC
    obtain ⟨f, _hf, hCf⟩ := hC
    rw [show (id C : Finset (Sym2 ι)) = C from rfl] at heC
    rw [← hCf] at heC
    exact (edgeComponent_subset X f) heC
  · intro he
    refine ⟨edgeComponent X e, ?_, ?_⟩
    · rw [mem_polymerDecomposition]; exact ⟨e, he, rfl⟩
    · exact self_mem_edgeComponent he

/-- **Members of `polymerDecomposition X` are polymers when `X` is
even**: every component in the decomposition of an even subgraph is a
polymer (non-empty + connected + even-degree). -/
theorem IsEvenSubgraph.polymerDecomposition_isPolymer
    {ι : Type*} [DecidableEq ι]
    {G : SimpleGraph ι} [Fintype G.edgeSet]
    {X : Finset (Sym2 ι)} (hX : IsEvenSubgraph G X)
    {C : Finset (Sym2 ι)} (hC : C ∈ polymerDecomposition X) :
    IsPolymer G C := by
  rw [mem_polymerDecomposition] at hC
  obtain ⟨e, he, rfl⟩ := hC
  exact hX.edgeComponent_isPolymer he

/-- **Polymer edge-disjointness**: two polymers `P, Q` are *edge-disjoint*
if they share no edge. This is a *weak* compatibility relation that
suffices for the multiplicative weight identity but does not give a
unique connected-component decomposition (counter-example: figure-eight
of two triangles edge-disjoint but vertex-sharing). -/
def IsPolymerCompatible {ι : Type*} [DecidableEq ι]
    (P Q : Finset (Sym2 ι)) : Prop :=
  Disjoint P Q

/-- **Polymer vertex-disjointness**: two polymers `P, Q` are *vertex-
disjoint* if they share no vertex (i.e. their supports are disjoint).
This is the *strong* compatibility relation needed for the bijection
between even subgraphs and their connected-component decomposition. -/
def IsPolymerVertexDisjoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P Q : Finset (Sym2 ι)) : Prop :=
  Disjoint (polymerSupport P) (polymerSupport Q)

/-- **Vertex-disjointness is symmetric**. -/
theorem isPolymerVertexDisjoint_symm
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P Q : Finset (Sym2 ι)} :
    IsPolymerVertexDisjoint P Q → IsPolymerVertexDisjoint Q P :=
  fun h => h.symm

/-- **Vertex-disjointness is irreflexive on polymers** (which are
non-empty by definition): a polymer cannot be vertex-disjoint from
itself. -/
theorem not_isPolymerVertexDisjoint_self_of_isPolymer
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : SimpleGraph ι} [Fintype G.edgeSet]
    {P : Finset (Sym2 ι)} (hP : IsPolymer G P) :
    ¬ IsPolymerVertexDisjoint P P := by
  intro h
  unfold IsPolymerVertexDisjoint at h
  have h_inf : polymerSupport P ⊓ polymerSupport P = ⊥ := h.eq_bot
  rw [inf_idem] at h_inf
  obtain ⟨e, heP⟩ := hP.nonempty
  -- Pick a vertex of `e` to derive `polymerSupport P ≠ ∅`.
  induction e using Sym2.ind with
  | h a b =>
    have ha : a ∈ (s(a, b) : Sym2 ι) := Sym2.mem_mk_left a b
    have hvP : a ∈ polymerSupport P :=
      mem_polymerSupport.mpr ⟨s(a, b), heP, ha⟩
    rw [h_inf] at hvP
    exact (Finset.notMem_empty _) hvP

/-- **Vertex-disjointness implies edge-disjointness**: if `P, Q` are
vertex-disjoint, then they are also edge-disjoint. (The converse fails
in general — see the figure-eight example.) -/
theorem IsPolymerVertexDisjoint.toEdgeDisjoint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P Q : Finset (Sym2 ι)}
    (h : IsPolymerVertexDisjoint P Q) :
    IsPolymerCompatible P Q := by
  unfold IsPolymerVertexDisjoint at h
  unfold IsPolymerCompatible
  rw [Finset.disjoint_left]
  intro e heP heQ
  -- An edge `e` has two endpoints; pick one to derive a contradiction.
  induction e using Sym2.ind with
  | h a b =>
    have ha : a ∈ (s(a, b) : Sym2 ι) := Sym2.mem_mk_left a b
    have hvP : a ∈ polymerSupport P :=
      mem_polymerSupport.mpr ⟨s(a, b), heP, ha⟩
    have hvQ : a ∈ polymerSupport Q :=
      mem_polymerSupport.mpr ⟨s(a, b), heQ, ha⟩
    exact (Finset.disjoint_left.mp h) hvP hvQ

/-- **Polymer compatibility is symmetric**. -/
theorem isPolymerCompatible_symm {ι : Type*} [DecidableEq ι]
    {P Q : Finset (Sym2 ι)} :
    IsPolymerCompatible P Q → IsPolymerCompatible Q P :=
  fun h => h.symm

/-- **Polymer compatibility is irreflexive on non-empty sets**: a
non-empty polymer is not compatible with itself (since it shares all
its edges with itself). -/
theorem not_isPolymerCompatible_self_of_nonempty {ι : Type*} [DecidableEq ι]
    {P : Finset (Sym2 ι)} (hP : P.Nonempty) :
    ¬ IsPolymerCompatible P P := by
  intro h
  have h_inf : P ⊓ P = ⊥ := h.eq_bot
  rw [inf_idem] at h_inf
  exact hP.ne_empty h_inf


end IsingModel

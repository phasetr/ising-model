import IsingModel.Conditioning

/-!
# Cluster (polymer) expansion for the lattice Ising model

This file develops the cluster / polymer expansion that underlies
Glimm–Jaffe §18.4–§18.7, specialised to the lattice Ising model at
zero magnetic field.

The starting point is the FV (3.45) closed form already established
in `IsingModel/Conditioning.lean`:
`Z(J, 0, β) = 2^|ι| · cosh(β·J)^|E| · ∑_{X ⊆ E, even-degree} tanh(β·J)^|X|`.

The cluster expansion organises the sum
`∑_{X ⊆ E, even-degree} tanh(β·J)^|X|`
by decomposing each even subgraph into edge-disjoint connected components
(*polymers*), then expressing `log Z - |ι|·log 2 - |E|·log cosh(β·J)`
as a sum over *clusters* of polymers via the Mayer/Ursell coefficient.

## Main definitions

* `IsEvenSubgraph G X` — `X ⊆ G.edgeFinset` such that every vertex of
  `ι` has an even number of incident edges in `X`. Equivalently, the
  cycle space of the underlying graph (over `F_2`).

## Main results

* `IsEvenSubgraph.empty` — the empty edge set is an even subgraph.
* `IsEvenSubgraph.symmDiff` — the symmetric difference of two even
  subgraphs is an even subgraph (cycle space is closed under XOR).
* `isEvenSubgraph_iff` — characterises the even-subgraph predicate as
  the sum-form used by `partitionFunction_high_temp_expansion_h_zero_closed`.

## References

* Glimm–Jaffe, *Quantum Physics*, §18.4–§18.7
* Friedli–Velenik, *Statistical Mechanics of Lattice Systems*, §3.7
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
  letI : DecidablePred fun S : Finset (Sym2 V) =>
      (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 V))).Connected :=
    fun _ => Classical.dec _
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
  letI : DecidablePred fun S : Finset (Sym2 V) =>
      (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 V))).Connected :=
    fun _ => Classical.dec _
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

/-- **Cluster polymer set** (Step 578, Mayer expansion foundation):
a finite set of polymers `Γ` is a *cluster set* iff `Γ` is non-empty,
every element is a polymer of `G`, and the induced subgraph of
`incompatibilityGraph` on `↑Γ` is `Connected`. This is the set-level
notion of cluster (no multiplicity); multi-set / sequence versions
follow in subsequent steps. The Mayer expansion expresses `log Ξ` as
a sum over clusters (with multiplicity) weighted by the Ursell
coefficient. -/
def IsClusterPolymerSet {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (Γ : Finset (Finset (Sym2 ι))) : Prop :=
  Γ.Nonempty ∧
  (∀ P ∈ Γ, IsPolymer G P) ∧
  ((incompatibilityGraph (ι := ι)).induce (↑Γ : Set (Finset (Sym2 ι)))).Connected

/-- **Singleton cluster set**: for any polymer `P`, the singleton
`{P}` is a cluster set. The induced subgraph on a singleton vertex
set is `Preconnected` vacuously (every two equal vertices are reachable
via the empty walk), and `Nonempty` is immediate. -/
theorem IsClusterPolymerSet.singleton
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {P : Finset (Sym2 ι)} (hP : IsPolymer G P) :
    IsClusterPolymerSet G {P} := by
  refine ⟨Finset.singleton_nonempty P, ?_, ?_⟩
  · intro Q hQ
    rw [Finset.mem_singleton] at hQ
    exact hQ ▸ hP
  · have hne :
        Nonempty ↑(↑({P} : Finset (Finset (Sym2 ι))) : Set (Finset (Sym2 ι))) :=
      ⟨⟨P, by simp⟩⟩
    refine { preconnected := ?_, nonempty := hne }
    intro u v
    have hu : (u : Finset (Sym2 ι)) ∈ ({P} : Finset (Finset (Sym2 ι))) := u.2
    have hv : (v : Finset (Sym2 ι)) ∈ ({P} : Finset (Finset (Sym2 ι))) := v.2
    rw [Finset.mem_singleton] at hu hv
    have huv : u = v := Subtype.ext (hu.trans hv.symm)
    exact huv ▸ SimpleGraph.Reachable.refl u

/-- **Compatible polymer family**: a `Finset` of polymers such that
the polymers are pairwise compatible (i.e. pairwise edge-disjoint).
This is the natural input to the polymer partition function:
`Ξ = ∑_{compatible Γ} ∏_{P ∈ Γ} z(P)`. -/
def IsCompatiblePolymerFamily {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (Γ : Finset (Finset (Sym2 ι))) : Prop :=
  (∀ P ∈ Γ, IsPolymer G P) ∧
  (Γ : Set (Finset (Sym2 ι))).Pairwise IsPolymerCompatible

/-- **Empty polymer family is compatible**: the empty family vacuously
satisfies both clauses. -/
theorem IsCompatiblePolymerFamily.empty {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    IsCompatiblePolymerFamily G (∅ : Finset (Finset (Sym2 ι))) := by
  refine ⟨?_, ?_⟩
  · intro P hP
    exact absurd hP (Finset.notMem_empty P)
  · simp

/-- **Vertex-disjoint compatible polymer family**: a `Finset` of
polymers such that the polymers are pairwise vertex-disjoint. This is
the *strong* family compatibility needed for the bijection between
even subgraphs and their connected-component decomposition. -/
def IsCompatiblePolymerFamilyVertexDisjoint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (Γ : Finset (Finset (Sym2 ι))) : Prop :=
  (∀ P ∈ Γ, IsPolymer G P) ∧
  (Γ : Set (Finset (Sym2 ι))).Pairwise IsPolymerVertexDisjoint

/-- **Vertex-disjoint family implies edge-disjoint family**: a vertex-
disjoint compatible polymer family is also an edge-disjoint compatible
polymer family. -/
theorem IsCompatiblePolymerFamilyVertexDisjoint.toCompatible
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : SimpleGraph ι} [Fintype G.edgeSet]
    {Γ : Finset (Finset (Sym2 ι))}
    (hΓ : IsCompatiblePolymerFamilyVertexDisjoint G Γ) :
    IsCompatiblePolymerFamily G Γ := by
  refine ⟨hΓ.1, ?_⟩
  intro P hP Q hQ hPQ
  exact (hΓ.2 hP hQ hPQ).toEdgeDisjoint

/-- **Empty vertex-disjoint polymer family is compatible**. -/
theorem IsCompatiblePolymerFamilyVertexDisjoint.empty
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    IsCompatiblePolymerFamilyVertexDisjoint G
      (∅ : Finset (Finset (Sym2 ι))) := by
  refine ⟨?_, ?_⟩
  · intro P hP
    exact absurd hP (Finset.notMem_empty P)
  · simp

/-- **Distinct components share no vertex**: if `C, C'` are different
members of `polymerDecomposition X`, then they are vertex-disjoint.

Proof: a shared support vertex `v` would force, via
`edgeComponent_absorbs_incident`, an edge of `C` to also be in `C'`,
violating the equal-or-disjoint property of distinct components. -/
theorem polymerDecomposition_pairwise_vertexDisjoint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : Finset (Sym2 ι)} :
    (polymerDecomposition X : Set (Finset (Sym2 ι))).Pairwise
      IsPolymerVertexDisjoint := by
  intro C hC C' hC' hCC'
  rw [Finset.mem_coe, mem_polymerDecomposition] at hC hC'
  obtain ⟨e, _he, rfl⟩ := hC
  obtain ⟨e', _he', rfl⟩ := hC'
  have h_neq : edgeComponent X e ≠ edgeComponent X e' := hCC'
  have h_disj := edgeComponent_eq_or_disjoint (X := X) e e'
  rcases h_disj with heq | hdisj
  · exact absurd heq h_neq
  unfold IsPolymerVertexDisjoint
  rw [Finset.disjoint_left]
  intro v hv hv'
  rw [mem_polymerSupport] at hv hv'
  obtain ⟨f, hfC, hvf⟩ := hv
  obtain ⟨g, hgC', hvg⟩ := hv'
  have hgX : g ∈ X := (edgeComponent_subset X e') hgC'
  have hg_in_e : g ∈ edgeComponent X e :=
    edgeComponent_absorbs_incident hfC hvf hgX hvg
  exact (Finset.disjoint_left.mp hdisj) hg_in_e hgC'

/-- **`polymerDecomposition` is a vertex-disjoint compatible polymer
family when `X` is even**. -/
theorem IsEvenSubgraph.polymerDecomposition_isCompatibleVertexDisjoint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : SimpleGraph ι} [Fintype G.edgeSet]
    {X : Finset (Sym2 ι)} (hX : IsEvenSubgraph G X) :
    IsCompatiblePolymerFamilyVertexDisjoint G (polymerDecomposition X) :=
  ⟨fun _ hC => hX.polymerDecomposition_isPolymer hC,
   polymerDecomposition_pairwise_vertexDisjoint⟩

/-- **Union over a compatible polymer family is an even subgraph**:
the `Finset.biUnion` of a compatible polymer family is an even subgraph
of `G`. Proved by induction on the family. -/
theorem IsCompatiblePolymerFamily.biUnion_isEvenSubgraph
    {ι : Type*} [DecidableEq ι]
    {G : SimpleGraph ι} [Fintype G.edgeSet]
    {Γ : Finset (Finset (Sym2 ι))}
    (hΓ : IsCompatiblePolymerFamily G Γ) :
    IsEvenSubgraph G (Γ.biUnion id) := by
  classical
  induction Γ using Finset.induction with
  | empty =>
    simpa using IsEvenSubgraph.empty (ι := ι) G
  | insert P Γ' hP_notin ih =>
    obtain ⟨h_polymer, h_pairwise⟩ := hΓ
    have h_polymer_P : IsPolymer G P := h_polymer P (Finset.mem_insert_self _ _)
    have h_polymer' : ∀ Q ∈ Γ', IsPolymer G Q := by
      intro Q hQ
      exact h_polymer Q (Finset.mem_insert_of_mem hQ)
    have h_pairwise' :
        (Γ' : Set (Finset (Sym2 ι))).Pairwise IsPolymerCompatible := by
      intro Q hQ R hR hne
      exact h_pairwise (Finset.mem_coe.mpr (Finset.mem_insert_of_mem
        (Finset.mem_coe.mp hQ))) (Finset.mem_coe.mpr (Finset.mem_insert_of_mem
        (Finset.mem_coe.mp hR))) hne
    have hΓ' : IsCompatiblePolymerFamily G Γ' := ⟨h_polymer', h_pairwise'⟩
    have h_disjoint : Disjoint P (Γ'.biUnion id) := by
      rw [Finset.disjoint_biUnion_right]
      intro Q hQ
      have hPQ : P ≠ Q := by
        intro heq
        rw [heq] at hP_notin
        exact hP_notin hQ
      have h_compat : IsPolymerCompatible P Q :=
        h_pairwise (Finset.mem_coe.mpr (Finset.mem_insert_self _ _))
          (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hQ)) hPQ
      simpa [id] using h_compat
    rw [Finset.biUnion_insert]
    simp only [id]
    exact h_polymer_P.isEven.union_disjoint (ih hΓ') h_disjoint

/-- **Insertion preserves vertex-disjoint compatibility**: if `Γ` is
vertex-disjoint compatible and `P` is a polymer vertex-disjoint from
every member of `Γ`, then `insert P Γ` is vertex-disjoint compatible. -/
theorem IsCompatiblePolymerFamilyVertexDisjoint.insert
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : SimpleGraph ι} [Fintype G.edgeSet]
    {Γ : Finset (Finset (Sym2 ι))} {P : Finset (Sym2 ι)}
    (hP : IsPolymer G P)
    (hPΓ : ∀ Q ∈ Γ, IsPolymerVertexDisjoint P Q)
    (hPnotIn : P ∉ Γ)
    (hΓ : IsCompatiblePolymerFamilyVertexDisjoint G Γ) :
    IsCompatiblePolymerFamilyVertexDisjoint G (insert P Γ) := by
  refine ⟨?_, ?_⟩
  · intro Q hQ
    rcases Finset.mem_insert.mp hQ with hQ | hQ
    · subst hQ; exact hP
    · exact hΓ.1 Q hQ
  · intro Q hQ R hR hne
    rcases Finset.mem_insert.mp (Finset.mem_coe.mp hQ) with hQ' | hQ' <;>
        rcases Finset.mem_insert.mp (Finset.mem_coe.mp hR) with hR' | hR'
    · subst hQ'; subst hR'; exact absurd rfl hne
    · subst hQ'
      exact hPΓ R hR'
    · subst hR'
      exact (hPΓ Q hQ').symm
    · exact hΓ.2 (Finset.mem_coe.mpr hQ') (Finset.mem_coe.mpr hR') hne

/-- **Vertex-disjoint family unions to an even subgraph**: corollary
of \`IsCompatiblePolymerFamily.biUnion_isEvenSubgraph\` via downgrade
to edge-disjoint compatibility. -/
theorem IsCompatiblePolymerFamilyVertexDisjoint.biUnion_isEvenSubgraph
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : SimpleGraph ι} [Fintype G.edgeSet]
    {Γ : Finset (Finset (Sym2 ι))}
    (hΓ : IsCompatiblePolymerFamilyVertexDisjoint G Γ) :
    IsEvenSubgraph G (Γ.biUnion id) :=
  hΓ.toCompatible.biUnion_isEvenSubgraph

/-- **Cardinality additivity over a compatible polymer family**: the
size of `Γ.biUnion id` equals `∑_{P ∈ Γ} |P|` when `Γ` is compatible
(pairwise edge-disjoint). This is the key combinatorial identity that
turns `t^|X|` into `∏_{P ∈ Γ} t^|P|` in the cluster expansion. -/
theorem IsCompatiblePolymerFamily.card_biUnion
    {ι : Type*} [DecidableEq ι]
    {G : SimpleGraph ι} [Fintype G.edgeSet]
    {Γ : Finset (Finset (Sym2 ι))}
    (hΓ : IsCompatiblePolymerFamily G Γ) :
    (Γ.biUnion id).card = ∑ P ∈ Γ, P.card := by
  refine Finset.card_biUnion ?_
  intro P hP Q hQ hPQ
  exact hΓ.2 hP hQ hPQ

/-- **Weight multiplicativity over a compatible polymer family**:
`t^|Γ.biUnion| = ∏ t^|P|` for any base `t`. Combines Step 509 card
additivity with the algebraic identity `t^(∑ aᵢ) = ∏ t^aᵢ`.

This identity converts the FV (3.45) summand `tanh(βJ)^|X|` into the
multiplicative form `∏_{P ∈ Γ} tanh(βJ)^|P|` once `X = Γ.biUnion id`. -/
theorem IsCompatiblePolymerFamily.pow_card_biUnion
    {ι : Type*} [DecidableEq ι]
    {G : SimpleGraph ι} [Fintype G.edgeSet]
    (t : ℝ) {Γ : Finset (Finset (Sym2 ι))}
    (hΓ : IsCompatiblePolymerFamily G Γ) :
    t ^ (Γ.biUnion id).card = ∏ P ∈ Γ, t ^ P.card := by
  rw [hΓ.card_biUnion, ← Finset.prod_pow_eq_pow_sum]

/-- **Vertex-disjoint family support card additivity**: for a vertex-
disjoint compatible polymer family,
`|polymerSupport (Γ.biUnion id)| = ∑ |polymerSupport P|`. -/
theorem IsCompatiblePolymerFamilyVertexDisjoint.support_card_biUnion
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : SimpleGraph ι} [Fintype G.edgeSet]
    {Γ : Finset (Finset (Sym2 ι))}
    (hΓ : IsCompatiblePolymerFamilyVertexDisjoint G Γ) :
    (polymerSupport (Γ.biUnion id)).card =
      ∑ P ∈ Γ, (polymerSupport P).card := by
  rw [polymerSupport_biUnion]
  apply Finset.card_biUnion
  intro P hP Q hQ hPQ
  exact hΓ.2 hP hQ hPQ

/-- **Vertex-disjoint family card additivity**. -/
theorem IsCompatiblePolymerFamilyVertexDisjoint.card_biUnion
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : SimpleGraph ι} [Fintype G.edgeSet]
    {Γ : Finset (Finset (Sym2 ι))}
    (hΓ : IsCompatiblePolymerFamilyVertexDisjoint G Γ) :
    (Γ.biUnion id).card = ∑ P ∈ Γ, P.card :=
  hΓ.toCompatible.card_biUnion

/-- **Vertex-disjoint family weight multiplicativity**:
`t^|biUnion| = ∏ t^|P|` for vertex-disjoint families. -/
theorem IsCompatiblePolymerFamilyVertexDisjoint.pow_card_biUnion
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : SimpleGraph ι} [Fintype G.edgeSet]
    (t : ℝ) {Γ : Finset (Finset (Sym2 ι))}
    (hΓ : IsCompatiblePolymerFamilyVertexDisjoint G Γ) :
    t ^ (Γ.biUnion id).card = ∏ P ∈ Γ, t ^ P.card :=
  hΓ.toCompatible.pow_card_biUnion t

/-- **Singleton vertex-disjoint family is compatible iff polymer**: a
one-element family `{P}` is vertex-disjoint compatible iff `IsPolymer G P`. -/
theorem isCompatiblePolymerFamilyVertexDisjoint_singleton
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (P : Finset (Sym2 ι)) :
    IsCompatiblePolymerFamilyVertexDisjoint G
        ({P} : Finset (Finset (Sym2 ι))) ↔
      IsPolymer G P := by
  refine ⟨fun ⟨h₁, _⟩ => h₁ P (Finset.mem_singleton.mpr rfl), ?_⟩
  intro hP
  refine ⟨?_, ?_⟩
  · intro Q hQ
    rw [Finset.mem_singleton] at hQ
    subst hQ; exact hP
  · intro P₁ hP₁ P₂ hP₂ hne
    rw [Finset.coe_singleton, Set.mem_singleton_iff] at hP₁ hP₂
    subst hP₁; subst hP₂
    exact absurd rfl hne

/-- **Monotonicity of vertex-disjoint compatible polymer family**: any
subset of a vertex-disjoint compatible polymer family is again vertex-
disjoint compatible. -/
theorem IsCompatiblePolymerFamilyVertexDisjoint.mono
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : SimpleGraph ι} [Fintype G.edgeSet]
    {Γ Γ' : Finset (Finset (Sym2 ι))} (hsub : Γ' ⊆ Γ)
    (hΓ : IsCompatiblePolymerFamilyVertexDisjoint G Γ) :
    IsCompatiblePolymerFamilyVertexDisjoint G Γ' := by
  refine ⟨?_, ?_⟩
  · intro P hP
    exact hΓ.1 P (hsub hP)
  · intro P hP Q hQ hPQ
    have hP' : P ∈ Γ := hsub (Finset.mem_coe.mp hP)
    have hQ' : Q ∈ Γ := hsub (Finset.mem_coe.mp hQ)
    exact hΓ.2 (Finset.mem_coe.mpr hP') (Finset.mem_coe.mpr hQ') hPQ

/-- **Singleton polymer family is compatible iff the polymer is a polymer**:
a one-element family `{P}` is compatible iff `IsPolymer G P`. -/
theorem isCompatiblePolymerFamily_singleton {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (P : Finset (Sym2 ι)) :
    IsCompatiblePolymerFamily G ({P} : Finset (Finset (Sym2 ι))) ↔
      IsPolymer G P := by
  refine ⟨fun ⟨h₁, _⟩ => h₁ P (Finset.mem_singleton.mpr rfl), ?_⟩
  intro hP
  refine ⟨?_, ?_⟩
  · intro Q hQ
    rw [Finset.mem_singleton] at hQ
    subst hQ; exact hP
  · intro P₁ hP₁ P₂ hP₂ hne
    rw [Finset.coe_singleton, Set.mem_singleton_iff] at hP₁ hP₂
    subst hP₁; subst hP₂
    exact absurd rfl hne

/-- **Monotonicity of compatible polymer family**: any subset of a
compatible polymer family is again compatible. -/
theorem IsCompatiblePolymerFamily.mono {ι : Type*} [DecidableEq ι]
    {G : SimpleGraph ι} [Fintype G.edgeSet]
    {Γ Γ' : Finset (Finset (Sym2 ι))} (hsub : Γ' ⊆ Γ)
    (hΓ : IsCompatiblePolymerFamily G Γ) :
    IsCompatiblePolymerFamily G Γ' := by
  refine ⟨?_, ?_⟩
  · intro P hP
    exact hΓ.1 P (hsub hP)
  · intro P hP Q hQ hPQ
    have hP' : P ∈ Γ := hsub (Finset.mem_coe.mp hP)
    have hQ' : Q ∈ Γ := hsub (Finset.mem_coe.mp hQ)
    exact hΓ.2 (Finset.mem_coe.mpr hP') (Finset.mem_coe.mpr hQ') hPQ

/-- **All even subgraphs of `G`**: the `Finset` of edge subsets that
satisfy `IsEvenSubgraph G`. -/
def evenSubgraphs {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    Finset (Finset (Sym2 ι)) :=
  G.edgeFinset.powerset.filter (fun X => IsEvenSubgraph G X)

/-- **Membership in `evenSubgraphs` characterisation**: `X ∈ evenSubgraphs G`
iff `IsEvenSubgraph G X`. -/
theorem mem_evenSubgraphs {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : SimpleGraph ι} [Fintype G.edgeSet]
    {X : Finset (Sym2 ι)} :
    X ∈ evenSubgraphs G ↔ IsEvenSubgraph G X := by
  unfold evenSubgraphs
  rw [Finset.mem_filter, Finset.mem_powerset]
  refine ⟨fun ⟨_, h⟩ => h, fun h => ⟨h.subset, h⟩⟩

/-- **Bridge to the inline FV (3.45) filter**: `evenSubgraphs G` equals
the inline form `G.edgeFinset.powerset.filter (∀ v, Even ((·.filter
(v ∈ ·)).card))` used by `partitionFunction_high_temp_expansion_h_zero_closed`. -/
theorem evenSubgraphs_eq_inline_filter {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    evenSubgraphs G =
      G.edgeFinset.powerset.filter
        (fun X : Finset (Sym2 ι) =>
          ∀ v : ι, Even ((X.filter (v ∈ ·)).card)) := by
  unfold evenSubgraphs
  apply Finset.filter_congr
  intro X hX
  rw [Finset.mem_powerset] at hX
  exact ⟨fun h => h.even_degree, fun h => ⟨hX, h⟩⟩

/-- **All polymers in a graph**: the natural reference universe of
polymers in `G`, defined noncomputably as the filter of polymers in
`G.edgeFinset.powerset`. -/
noncomputable def allPolymers {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    Finset (Finset (Sym2 ι)) := by
  classical
  exact G.edgeFinset.powerset.filter (fun P => IsPolymer G P)

/-- **Membership in `allPolymers` characterisation**: `P ∈ allPolymers G`
iff `IsPolymer G P` (since `IsPolymer` already implies the subset
condition). -/
theorem mem_allPolymers {ι : Type*} [DecidableEq ι]
    {G : SimpleGraph ι} [Fintype G.edgeSet]
    {P : Finset (Sym2 ι)} :
    P ∈ allPolymers G ↔ IsPolymer G P := by
  classical
  unfold allPolymers
  rw [Finset.mem_filter, Finset.mem_powerset]
  refine ⟨fun ⟨_, h⟩ => h, fun h => ⟨h.isEven.subset, h⟩⟩

/-- **Even subgraph polymer decomposition (main statement)**: every even
subgraph `X ⊆ G.edgeFinset` has a canonical decomposition into a
vertex-disjoint compatible polymer family `polymerDecomposition X` whose
biUnion recovers `X`.

This is the heart of GJ §18.4 cluster expansion at the lattice Ising
level: `evenSubgraphs G` is in bijection with the vertex-disjoint
compatible polymer families with `biUnion ⊆ G.edgeFinset`. -/
theorem IsEvenSubgraph.polymerDecomposition_main
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : SimpleGraph ι} [Fintype G.edgeSet]
    {X : Finset (Sym2 ι)} (hX : IsEvenSubgraph G X) :
    IsCompatiblePolymerFamilyVertexDisjoint G (polymerDecomposition X) ∧
    (polymerDecomposition X).biUnion id = X :=
  ⟨hX.polymerDecomposition_isCompatibleVertexDisjoint,
   polymerDecomposition_biUnion_id X⟩

/-- **Polymer's edge component is itself**: if `P` is a polymer and
`e ∈ P`, then `edgeComponent P e = P`. -/
theorem IsPolymer.edgeComponent_eq_self
    {ι : Type*} [DecidableEq ι]
    {G : SimpleGraph ι} [Fintype G.edgeSet]
    {P : Finset (Sym2 ι)} (hP : IsPolymer G P)
    {e : Sym2 ι} (he : e ∈ P) :
    edgeComponent P e = P := by
  apply Finset.Subset.antisymm (edgeComponent_subset P e)
  intro f hf
  rw [mem_edgeComponent]
  exact ⟨hf, hP.connected e he f hf⟩

/-- **Polymer's decomposition is itself**: if `P` is a polymer, then
`polymerDecomposition P = {P}`. -/
theorem IsPolymer.polymerDecomposition_eq_singleton
    {ι : Type*} [DecidableEq ι]
    {G : SimpleGraph ι} [Fintype G.edgeSet]
    {P : Finset (Sym2 ι)} (hP : IsPolymer G P) :
    polymerDecomposition P = {P} := by
  classical
  unfold polymerDecomposition
  have h_image_eq : P.image (fun e => edgeComponent P e) =
      P.image (fun _ => P) := by
    apply Finset.image_congr
    intro e he
    exact hP.edgeComponent_eq_self he
  rw [h_image_eq]
  exact Finset.image_const hP.nonempty P

/-- **Reachability in a VD-compatible biUnion stays within a polymer**:
if `Γ` is vertex-disjoint compatible and `P ∈ Γ`, then any chain in
`edgeAdjacentIn (Γ.biUnion id)` starting from an edge of `P` ends at
an edge of `P`. -/
private theorem reflTransGen_in_polymer_of_VD
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : SimpleGraph ι} [Fintype G.edgeSet]
    {Γ : Finset (Finset (Sym2 ι))}
    (hΓ : IsCompatiblePolymerFamilyVertexDisjoint G Γ)
    {P : Finset (Sym2 ι)} (hP : P ∈ Γ)
    {e f : Sym2 ι} (he : e ∈ P)
    (h_chain : Relation.ReflTransGen (edgeAdjacentIn (Γ.biUnion id)) e f) :
    f ∈ P := by
  induction h_chain with
  | refl => exact he
  | tail _h_chain h_step ih =>
    rename_i a b
    -- ih : a ∈ P
    -- h_step : edgeAdjacentIn biUnion a b
    obtain ⟨_, hb_biU, v, hva, hvb⟩ := h_step
    -- b ∈ biUnion ⇒ ∃ Q ∈ Γ, b ∈ Q
    rw [Finset.mem_biUnion] at hb_biU
    obtain ⟨Q, hQ, hbQ⟩ := hb_biU
    -- v ∈ a ∈ P ⇒ v ∈ polymerSupport P
    have hvP : v ∈ polymerSupport P :=
      mem_polymerSupport.mpr ⟨a, ih, hva⟩
    -- v ∈ b ∈ Q ⇒ v ∈ polymerSupport Q
    have hvQ : v ∈ polymerSupport Q :=
      mem_polymerSupport.mpr ⟨b, hbQ, hvb⟩
    -- By VD: P, Q must be equal (else supports disjoint)
    by_cases hPQ : P = Q
    · exact hPQ ▸ hbQ
    · exfalso
      have h_disj : Disjoint (polymerSupport P) (polymerSupport Q) :=
        hΓ.2 (Finset.mem_coe.mpr hP) (Finset.mem_coe.mpr hQ) hPQ
      exact (Finset.disjoint_left.mp h_disj) hvP hvQ

/-- **Lift edge-adjacency reachability from a subgraph to a superset**:
if `P ⊆ Y`, any chain in `edgeAdjacentIn P` lifts to a chain in
`edgeAdjacentIn Y`. -/
private theorem reflTransGen_edgeAdjacentIn_mono
    {ι : Type*} {P Y : Finset (Sym2 ι)} (hPY : P ⊆ Y) {e f : Sym2 ι}
    (h : Relation.ReflTransGen (edgeAdjacentIn P) e f) :
    Relation.ReflTransGen (edgeAdjacentIn Y) e f := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _h h_step ih =>
    rename_i a b
    have h_step' : edgeAdjacentIn Y a b :=
      ⟨hPY h_step.1, hPY h_step.2.1, h_step.2.2⟩
    exact Relation.ReflTransGen.tail ih h_step'

/-- **Each VD-family polymer is its own biUnion component**: if `Γ` is
vertex-disjoint compatible and `P ∈ Γ` with `e ∈ P`, then
`edgeComponent (Γ.biUnion id) e = P`. -/
theorem IsCompatiblePolymerFamilyVertexDisjoint.edgeComponent_biUnion_eq_polymer
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : SimpleGraph ι} [Fintype G.edgeSet]
    {Γ : Finset (Finset (Sym2 ι))}
    (hΓ : IsCompatiblePolymerFamilyVertexDisjoint G Γ)
    {P : Finset (Sym2 ι)} (hP_mem : P ∈ Γ)
    {e : Sym2 ι} (he : e ∈ P) :
    edgeComponent (Γ.biUnion id) e = P := by
  apply Finset.Subset.antisymm
  · -- ⊆: chain stays in P
    intro f hf
    rw [mem_edgeComponent] at hf
    exact reflTransGen_in_polymer_of_VD hΓ hP_mem he hf.2
  · -- ⊇: P connected ⇒ chain in P → chain in biUnion
    intro f hf
    have hP_polymer := hΓ.1 P hP_mem
    have h_in_biU : f ∈ Γ.biUnion id := by
      rw [Finset.mem_biUnion]; exact ⟨P, hP_mem, hf⟩
    rw [mem_edgeComponent]
    refine ⟨h_in_biU, ?_⟩
    have h_chain_in_P : Relation.ReflTransGen (edgeAdjacentIn P) e f :=
      hP_polymer.connected e he f hf
    have hP_sub : P ⊆ Γ.biUnion id := by
      intro x hx
      rw [Finset.mem_biUnion]; exact ⟨P, hP_mem, hx⟩
    exact reflTransGen_edgeAdjacentIn_mono hP_sub h_chain_in_P

/-- **`polymerDecomposition (Γ.biUnion id) = Γ`** for VD-compatible Γ:
the polymer decomposition of the biUnion of a vertex-disjoint
compatible polymer family recovers the family. -/
theorem IsCompatiblePolymerFamilyVertexDisjoint.polymerDecomposition_biUnion
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : SimpleGraph ι} [Fintype G.edgeSet]
    {Γ : Finset (Finset (Sym2 ι))}
    (hΓ : IsCompatiblePolymerFamilyVertexDisjoint G Γ) :
    polymerDecomposition (Γ.biUnion id) = Γ := by
  ext C
  rw [mem_polymerDecomposition]
  refine ⟨?_, ?_⟩
  · -- C ∈ image: ∃ e ∈ biUnion, edgeComponent biUnion e = C
    rintro ⟨e, he, rfl⟩
    rw [Finset.mem_biUnion] at he
    obtain ⟨P, hP_mem, heP⟩ := he
    -- edgeComponent biUnion e = P (Step 544)
    rw [hΓ.edgeComponent_biUnion_eq_polymer hP_mem heP]
    exact hP_mem
  · -- C ∈ Γ ⇒ C ∈ image (pick any edge of C)
    intro hC
    have hC_polymer := hΓ.1 C hC
    obtain ⟨e, heC⟩ := hC_polymer.nonempty
    refine ⟨e, ?_, ?_⟩
    · rw [Finset.mem_biUnion]
      exact ⟨C, hC, heC⟩
    · exact hΓ.edgeComponent_biUnion_eq_polymer hC heC

/-- **Set of vertex-disjoint compatible polymer families** in `G`:
the universe used for the polymer-model identity. Defined as
sub-families of `allPolymers G` that are pairwise vertex-disjoint. -/
noncomputable def vdCompatiblePolymerFamilies
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    Finset (Finset (Finset (Sym2 ι))) := by
  classical
  exact (allPolymers G).powerset.filter
    (fun Γ => IsCompatiblePolymerFamilyVertexDisjoint G Γ)

/-- **Membership in `vdCompatiblePolymerFamilies`**:
`Γ ∈ vdCompatiblePolymerFamilies G ↔ Γ ⊆ allPolymers G ∧
IsCompatiblePolymerFamilyVertexDisjoint G Γ`. -/
theorem mem_vdCompatiblePolymerFamilies
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : SimpleGraph ι} [Fintype G.edgeSet]
    {Γ : Finset (Finset (Sym2 ι))} :
    Γ ∈ vdCompatiblePolymerFamilies G ↔
      Γ ⊆ allPolymers G ∧
        IsCompatiblePolymerFamilyVertexDisjoint G Γ := by
  classical
  unfold vdCompatiblePolymerFamilies
  rw [Finset.mem_filter, Finset.mem_powerset]

/-- **`polymerDecomposition` lands in `vdCompatiblePolymerFamilies`**:
for any even subgraph `X`, the canonical decomposition is a member of
`vdCompatiblePolymerFamilies G`. -/
theorem IsEvenSubgraph.polymerDecomposition_mem_vdCompatiblePolymerFamilies
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : SimpleGraph ι} [Fintype G.edgeSet]
    {X : Finset (Sym2 ι)} (hX : IsEvenSubgraph G X) :
    polymerDecomposition X ∈ vdCompatiblePolymerFamilies G := by
  rw [mem_vdCompatiblePolymerFamilies]
  refine ⟨?_, hX.polymerDecomposition_isCompatibleVertexDisjoint⟩
  intro C hC
  rw [mem_allPolymers]
  exact hX.polymerDecomposition_isPolymer hC

/-- **FV (3.45) sum equals VD-polymer sum**: under no further hypotheses,
`∑_{X ∈ evenSubgraphs G} t^|X| = ∑_{Γ ∈ vdCompatiblePolymerFamilies G,
  ∏_{P ∈ Γ} t^|P|}`.

Proved by `Finset.sum_bij` along the bijection `X ↔ polymerDecomposition X`
between `evenSubgraphs G` and `vdCompatiblePolymerFamilies G`. The
weight identity uses `pow_card_biUnion` (Step 521) plus
`polymerDecomposition_biUnion_id = X` (Step 539). -/
theorem evenSubgraphs_sum_eq_vdPolymerFamilies_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ) :
    (∑ X ∈ evenSubgraphs G, t ^ X.card) =
      ∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card := by
  classical
  apply Finset.sum_bij
    (fun X (_ : X ∈ evenSubgraphs G) => polymerDecomposition X)
  · -- Membership: polymerDecomposition X ∈ vdCompatiblePolymerFamilies G.
    intro X hX
    rw [mem_evenSubgraphs] at hX
    exact hX.polymerDecomposition_mem_vdCompatiblePolymerFamilies
  · -- Injectivity: polymerDecomposition X = polymerDecomposition X' ⇒ X = X'.
    intro X hX X' hX' h_eq
    have h₁ : (polymerDecomposition X).biUnion id = X :=
      polymerDecomposition_biUnion_id X
    have h₂ : (polymerDecomposition X').biUnion id = X' :=
      polymerDecomposition_biUnion_id X'
    rw [← h₁, ← h₂, h_eq]
  · -- Surjectivity: given Γ, find X with polymerDecomposition X = Γ.
    intro Γ hΓ
    rw [mem_vdCompatiblePolymerFamilies] at hΓ
    refine ⟨Γ.biUnion id, ?_, ?_⟩
    · rw [mem_evenSubgraphs]
      exact hΓ.2.biUnion_isEvenSubgraph
    · exact hΓ.2.polymerDecomposition_biUnion
  · -- Weight match: t^|X| = ∏ t^|P|.
    intro X hX
    rw [mem_evenSubgraphs] at hX
    have h_biU : (polymerDecomposition X).biUnion id = X :=
      polymerDecomposition_biUnion_id X
    have h_pow := hX.polymerDecomposition_isCompatibleVertexDisjoint.pow_card_biUnion t
    rw [h_biU] at h_pow
    exact h_pow

/-- **Polymer model partition function (abstract)**: given a reference
finite universe of polymer candidates `Ω : Finset (Finset (Sym2 ι))`
and a weight function `z : Finset (Sym2 ι) → ℝ`, the polymer model
partition function is
`Ξ(Ω, z) = ∑_{Γ ⊆ Ω, Γ compatible} ∏_{P ∈ Γ} z(P)`,
where compatibility is pairwise edge-disjointness.

`Classical.dec` is used to decide compatibility of arbitrary
sub-families because `IsPolymer` (involving edge-connectedness via
`Relation.ReflTransGen`) is not constructively decidable. -/
noncomputable def polymerPartition {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (Ω : Finset (Finset (Sym2 ι))) (z : Finset (Sym2 ι) → ℝ) : ℝ := by
  classical
  exact ∑ Γ ∈ Ω.powerset.filter (fun Γ => IsCompatiblePolymerFamily G Γ),
    ∏ P ∈ Γ, z P

/-- **Polymer partition function on a single polymer**: when the
universe is `{P}` for a single polymer `P`, the partition function
equals `1 + z(P)` (the empty family contributes `1`, the singleton
family contributes `z(P)`). -/
theorem polymerPartition_singleton {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {P : Finset (Sym2 ι)} (hP : IsPolymer G P)
    (z : Finset (Sym2 ι) → ℝ) :
    polymerPartition G ({P} : Finset (Finset (Sym2 ι))) z = 1 + z P := by
  classical
  unfold polymerPartition
  -- powerset of `{P}` is `{∅, {P}}`; both are compatible.
  have hpow : ({P} : Finset (Finset (Sym2 ι))).powerset =
      ({∅, {P}} : Finset (Finset (Finset (Sym2 ι)))) := by
    ext Γ
    simp [Finset.mem_powerset, Finset.subset_singleton_iff]
  rw [hpow]
  rw [show ({∅, {P}} : Finset (Finset (Finset (Sym2 ι)))).filter
      (fun Γ => IsCompatiblePolymerFamily G Γ) = {∅, {P}} from ?_]
  · rw [Finset.sum_pair (a := (∅ : Finset (Finset (Sym2 ι))))
        (b := ({P} : Finset (Finset (Sym2 ι))))
        (by simp)]
    simp
  · ext Γ
    rw [Finset.mem_filter]
    refine ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, ?_⟩⟩
    rcases Finset.mem_insert.mp h with h | h
    · subst h; exact IsCompatiblePolymerFamily.empty G
    · rw [Finset.mem_singleton] at h
      subst h
      exact (isCompatiblePolymerFamily_singleton G P).mpr hP

/-- **Polymer partition function is at least 1 under non-negative
weights**: if `z(P) ≥ 0` for every `P ∈ Ω`, then
`polymerPartition G Ω z ≥ 1`. The empty sub-family always contributes
exactly 1 to the sum. -/
theorem polymerPartition_ge_one {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (Ω : Finset (Finset (Sym2 ι))) {z : Finset (Sym2 ι) → ℝ}
    (hz : ∀ Q ∈ Ω, 0 ≤ z Q) :
    1 ≤ polymerPartition G Ω z := by
  classical
  unfold polymerPartition
  -- Split off the empty sub-family: contributes 1 to the sum.
  have h_empty_in : (∅ : Finset (Finset (Sym2 ι))) ∈
      Ω.powerset.filter (fun Γ => IsCompatiblePolymerFamily G Γ) := by
    rw [Finset.mem_filter]
    exact ⟨Finset.empty_mem_powerset _,
      IsCompatiblePolymerFamily.empty G⟩
  have h_split := Finset.add_sum_erase _ (fun Γ => ∏ P ∈ Γ, z P) h_empty_in
  simp only [Finset.prod_empty] at h_split
  have h_other_nn : 0 ≤ ∑ Γ ∈ (Ω.powerset.filter
        (fun Γ => IsCompatiblePolymerFamily G Γ)).erase ∅,
        ∏ P ∈ Γ, z P := by
    apply Finset.sum_nonneg
    intro Γ hΓ
    rw [Finset.mem_erase, Finset.mem_filter, Finset.mem_powerset] at hΓ
    obtain ⟨_, hsub, _⟩ := hΓ
    apply Finset.prod_nonneg
    intro P hPΓ
    exact hz P (hsub hPΓ)
  linarith

/-- **Polymer partition function on an empty universe equals 1**: the
only sub-family is `∅`, which is compatible with empty product `1`. -/
theorem polymerPartition_empty {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (z : Finset (Sym2 ι) → ℝ) :
    polymerPartition G (∅ : Finset (Finset (Sym2 ι))) z = 1 := by
  classical
  unfold polymerPartition
  rw [Finset.powerset_empty,
      Finset.filter_eq_self.mpr fun Γ hΓ => by
        rw [Finset.mem_singleton] at hΓ
        subst hΓ
        exact IsCompatiblePolymerFamily.empty G]
  simp

/-- **FV (3.45) closed form via `evenSubgraphs G`**: under no further
hypotheses, the FV (3.45) closed form may be rewritten as
`Z(J,0,β) = 2^|ι| · cosh(β·J)^|E| · ∑ X ∈ evenSubgraphs G, tanh(β·J)^|X|`.

Direct corollary of `partitionFunction_high_temp_expansion_h_zero_closed`
(Step 283) plus `evenSubgraphs_eq_inline_filter` (Step 516). -/
theorem partitionFunction_high_temp_expansion_h_zero_closed_evenSubgraphs
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ) :
    partitionFunction G ⟨J, 0, β⟩ =
      (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card *
      ∑ X ∈ evenSubgraphs G, Real.tanh (β * J) ^ X.card := by
  rw [partitionFunction_high_temp_expansion_h_zero_closed G J β,
      evenSubgraphs_eq_inline_filter]

/-- **Z FV (3.45) polymer-family form**: under no further hypotheses,
`Z(J,0,β) = 2^|ι| · cosh(β·J)^|E| · ∑_{Γ ∈ vdCompatiblePolymerFamilies G,
∏_{P ∈ Γ} tanh(β·J)^|P|}`.

Combines Step 517 (FV (3.45) via `evenSubgraphs G`) with Step 547
(`evenSubgraphs_sum_eq_vdPolymerFamilies_sum`). -/
theorem partitionFunction_high_temp_expansion_h_zero_polymer_family
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ) :
    partitionFunction G ⟨J, 0, β⟩ =
      (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card *
      ∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card := by
  rw [partitionFunction_high_temp_expansion_h_zero_closed_evenSubgraphs G J β,
      evenSubgraphs_sum_eq_vdPolymerFamilies_sum G (Real.tanh (β * J))]

/-- **Sum of polymer cardinalities is bounded by `|E|`**: in a
vertex-disjoint compatible polymer family, the total edge count is at
most `G.edgeFinset.card` since the biUnion is a subset of the edge set. -/
theorem IsCompatiblePolymerFamilyVertexDisjoint.sum_card_le_edgeFinset_card
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : SimpleGraph ι} [Fintype G.edgeSet]
    {Γ : Finset (Finset (Sym2 ι))}
    (hΓ : IsCompatiblePolymerFamilyVertexDisjoint G Γ) :
    ∑ P ∈ Γ, P.card ≤ G.edgeFinset.card := by
  rw [← hΓ.card_biUnion]
  apply Finset.card_le_card
  intro e he
  rw [Finset.mem_biUnion] at he
  obtain ⟨P, hP, heP⟩ := he
  exact (hΓ.1 P hP).isEven.subset heP

/-- **VD polymer-family sum ≤ 2^|E|**: under `0 ≤ β·J`,
`∑_{Γ ∈ vdCompatiblePolymerFamilies G} ∏ tanh(β·J)^|P| ≤ 2^|E|`.

Direct via the bijection (Step 547) plus the existing even-subgraph
upper bound `sum_pow_tanh_even_subgraph_le_two_pow` (Step 319). -/
theorem vdPolymerFamilies_sum_le_two_pow
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    (∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (2 : ℝ) ^ G.edgeFinset.card := by
  rw [← evenSubgraphs_sum_eq_vdPolymerFamilies_sum G (Real.tanh (β * J))]
  rw [evenSubgraphs_eq_inline_filter]
  exact sum_pow_tanh_even_subgraph_le_two_pow G J β hβJ

/-- **VD polymer-family sum ≥ 1**: under `0 ≤ β·J`,
`1 ≤ ∑_{Γ ∈ vdCompatiblePolymerFamilies G} ∏ tanh(β·J)^|P|`.

Direct via the bijection (Step 547) plus `one_le_sum_pow_tanh_even_subgraph`
(Step 318). The empty family contributes 1; non-empty families add
non-negative weights. -/
theorem one_le_vdPolymerFamilies_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    1 ≤ ∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card := by
  rw [← evenSubgraphs_sum_eq_vdPolymerFamilies_sum G (Real.tanh (β * J))]
  rw [evenSubgraphs_eq_inline_filter]
  exact one_le_sum_pow_tanh_even_subgraph G J β hβJ

/-- **Sharper VD polymer-family sum upper bound**: under `0 ≤ β·J`,
`∑_Γ ∏ tanh(β·J)^|P| ≤ (1 + tanh(β·J))^|E|`. Tightens Step 551
(2^|E|) using Step 392 \`sum_pow_tanh_even_subgraph_le_one_plus_tanh_pow\`. -/
theorem vdPolymerFamilies_sum_le_one_plus_tanh_pow
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    (∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (1 + Real.tanh (β * J)) ^ G.edgeFinset.card := by
  rw [← evenSubgraphs_sum_eq_vdPolymerFamilies_sum G (Real.tanh (β * J))]
  rw [evenSubgraphs_eq_inline_filter]
  exact sum_pow_tanh_even_subgraph_le_one_plus_tanh_pow G J β hβJ

/-- **Sharper VD polymer-family sum sandwich**: under `0 ≤ β·J`,
`1 ≤ ∑_Γ ∏ tanh(β·J)^|P| ≤ (1 + tanh(β·J))^|E|`. Bundles Steps 550
and 553. -/
theorem vdPolymerFamilies_sum_sandwich_sharp
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    1 ≤ (∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) ∧
    (∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (1 + Real.tanh (β * J)) ^ G.edgeFinset.card :=
  ⟨one_le_vdPolymerFamilies_sum G hβJ,
   vdPolymerFamilies_sum_le_one_plus_tanh_pow G hβJ⟩

/-- **VD polymer-family sum sandwich**: under `0 ≤ β·J`,
`1 ≤ ∑_Γ ∏ tanh(β·J)^|P| ≤ 2^|E|`. Bundles Steps 550 and 551. -/
theorem vdPolymerFamilies_sum_sandwich
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    1 ≤ (∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) ∧
    (∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (2 : ℝ) ^ G.edgeFinset.card :=
  ⟨one_le_vdPolymerFamilies_sum G hβJ,
   vdPolymerFamilies_sum_le_two_pow G hβJ⟩

/-- **Polymer activity for the lattice Ising model**: the natural
weight `t^|P|` arising from the FV (3.45) closed form
`Z = 2^|ι|·cosh^|E|·∑_{X ⊆ E, even} tanh(β·J)^|X|`.

Set `t = tanh(β·J)` to recover the FV (3.45) summand. -/
def polymerActivity (t : ℝ) (P : Finset (Sym2 ι)) : ℝ := t ^ P.card

/-- **Lattice Ising polymer partition function**: the polymer model
partition function `polymerPartition` evaluated at the universe of all
polymers in `G` with the canonical activity `tanh(β·J)^|P|`. This is
the polymer-decomposition reformulation of the FV (3.45) sum
`∑_{X ⊆ E, even} tanh(β·J)^|X|` modulo the connected-components
identification (proved in subsequent PRs). -/
noncomputable def latticeIsingPolymerPartition {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β J : ℝ) : ℝ :=
  polymerPartition G (allPolymers G) (polymerActivity (Real.tanh (β * J)))

/-- **Polymer activity at non-negative `t` is non-negative**: with
`t = tanh(β·J)`, this gives `0 ≤ tanh(β·J)^|P|` whenever `0 ≤ β·J`. -/
theorem polymerActivity_nonneg {ι : Type*} {t : ℝ} (ht : 0 ≤ t)
    (P : Finset (Sym2 ι)) : 0 ≤ polymerActivity t P := by
  unfold polymerActivity
  exact pow_nonneg ht _

/-- **Lattice Ising polymer partition function ≥ 1 under `0 ≤ β·J`**:
since `0 ≤ β·J` implies `0 ≤ tanh(β·J)`, the activity is non-negative
and the empty family contributes exactly 1. -/
theorem latticeIsingPolymerPartition_ge_one {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    1 ≤ latticeIsingPolymerPartition G β J := by
  have h_tanh_nn : 0 ≤ Real.tanh (β * J) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hβJ) (Real.cosh_pos _).le
  unfold latticeIsingPolymerPartition
  apply polymerPartition_ge_one G _
  intro P _
  exact polymerActivity_nonneg h_tanh_nn P

/-- **Polymer activity is `1` on the empty edge set** (since `t^0 = 1`). -/
@[simp]
theorem polymerActivity_empty (t : ℝ) :
    polymerActivity t (∅ : Finset (Sym2 ι)) = 1 := by
  unfold polymerActivity
  simp

/-- **VD polymer-family sum is continuous in `t`**: the sum
`∑_{Γ ∈ vdCompatiblePolymerFamilies G} ∏_{P ∈ Γ} t^|P|`
is a finite sum of finite products of monomials `t^|P|`, hence continuous
(and indeed polynomial) in `t : ℝ`. This is the foundation for the §18.6
analyticity of the polymer expansion in `tanh(β·J)`. -/
theorem vdPolymerFamilies_sum_continuous
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    Continuous (fun t : ℝ =>
      ∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card) := by
  refine continuous_finset_sum _ ?_
  intro Γ _
  refine continuous_finset_prod _ ?_
  intro P _
  exact continuous_id.pow _

/-- **VD polymer-family sum is differentiable in `t`**: as a finite sum
of finite products of monomials `t^|P|`, the polymer-family sum is a
polynomial in `t`, hence differentiable on all of `ℝ`. Strengthens
`vdPolymerFamilies_sum_continuous` from `Continuous` to `Differentiable`
and prepares the §18.6 analyticity statement. -/
theorem vdPolymerFamilies_sum_differentiable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    Differentiable ℝ (fun t : ℝ =>
      ∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card) := by
  refine Differentiable.fun_sum (fun Γ _ => ?_)
  refine Differentiable.fun_finset_prod (fun P _ => ?_)
  exact (differentiable_id (𝕜 := ℝ)).pow _

/-- **`Real.tanh` is continuous on `ℝ`** (project-local helper): derived
from `tanh = sinh / cosh` together with `Real.cosh > 0`. Mathlib does
not yet export `Real.continuous_tanh`, so we provide it here. -/
theorem continuous_real_tanh : Continuous Real.tanh := by
  have h_eq : Real.tanh = fun x : ℝ => Real.sinh x / Real.cosh x :=
    funext (fun x => Real.tanh_eq_sinh_div_cosh x)
  rw [h_eq]
  exact Real.continuous_sinh.div Real.continuous_cosh
    (fun x => (Real.cosh_pos x).ne')

/-- **`Real.tanh` is differentiable on `ℝ`** (project-local helper):
derived from `tanh = sinh / cosh` together with `Real.cosh > 0` and
`Differentiable.div`. Mathlib does not yet export `Real.differentiable_tanh`. -/
theorem differentiable_real_tanh : Differentiable ℝ Real.tanh := by
  have h_eq : Real.tanh = fun x : ℝ => Real.sinh x / Real.cosh x :=
    funext (fun x => Real.tanh_eq_sinh_div_cosh x)
  rw [h_eq]
  exact Real.differentiable_sinh.div Real.differentiable_cosh
    (fun x => (Real.cosh_pos x).ne')

/-- **VD polymer-family sum is continuous in `β` (with `J` fixed)**:
composing Step 555 with continuity of `tanh` and multiplication. -/
theorem vdPolymerFamilies_sum_tanh_continuous_beta
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J : ℝ) :
    Continuous (fun β : ℝ =>
      ∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) := by
  have h_mul : Continuous (fun β : ℝ => β * J) :=
    continuous_id.mul continuous_const
  exact (vdPolymerFamilies_sum_continuous G).comp (continuous_real_tanh.comp h_mul)

/-- **VD polymer-family sum is continuous in `J` (with `β` fixed)**:
composing Step 555 with continuity of `tanh` and multiplication. -/
theorem vdPolymerFamilies_sum_tanh_continuous_J
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β : ℝ) :
    Continuous (fun J : ℝ =>
      ∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) := by
  have h_mul : Continuous (fun J : ℝ => β * J) :=
    continuous_const.mul continuous_id
  exact (vdPolymerFamilies_sum_continuous G).comp (continuous_real_tanh.comp h_mul)

/-- **VD polymer-family sum is differentiable in `β` (with `J` fixed)**:
chain-rule composition of Step 558 with `differentiable_real_tanh` and
`Differentiable.mul_const`. -/
theorem vdPolymerFamilies_sum_tanh_differentiable_beta
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J : ℝ) :
    Differentiable ℝ (fun β : ℝ =>
      ∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) := by
  have h_mul : Differentiable ℝ (fun β : ℝ => β * J) :=
    (differentiable_id (𝕜 := ℝ)).mul_const J
  exact (vdPolymerFamilies_sum_differentiable G).comp
    (differentiable_real_tanh.comp h_mul)

/-- **VD polymer-family sum is differentiable in `J` (with `β` fixed)**:
chain-rule composition of Step 558 with `differentiable_real_tanh` and
`Differentiable.const_mul`. -/
theorem vdPolymerFamilies_sum_tanh_differentiable_J
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β : ℝ) :
    Differentiable ℝ (fun J : ℝ =>
      ∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) := by
  have h_mul : Differentiable ℝ (fun J : ℝ => β * J) :=
    (differentiable_id (𝕜 := ℝ)).const_mul β
  exact (vdPolymerFamilies_sum_differentiable G).comp
    (differentiable_real_tanh.comp h_mul)

/-- **Partition function continuous in `β` (at `h = 0`) via polymer
expansion**: combines the §18.4 polymer-family identity (Step 548) with
the polymer-family sum continuity (Step 556) and continuity of
`cosh(β·J)^|E|` to obtain
`Continuous (fun β => partitionFunction G ⟨J, 0, β⟩)`.

The polymer expansion realises `Z(J,0,β) = 2^|ι| · cosh(β·J)^|E| ·
∑_Γ ∏_P tanh(β·J)^|P|` as a product of three β-continuous factors. -/
theorem partitionFunction_continuous_beta_h_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J : ℝ) :
    Continuous (fun β : ℝ => partitionFunction G ⟨J, 0, β⟩) := by
  have h_eq : (fun β : ℝ => partitionFunction G ⟨J, 0, β⟩) =
      fun β : ℝ => (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card *
        ∑ Γ ∈ vdCompatiblePolymerFamilies G,
          ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card :=
    funext (partitionFunction_high_temp_expansion_h_zero_polymer_family G J)
  rw [h_eq]
  have h_mul : Continuous (fun β : ℝ => β * J) :=
    continuous_id.mul continuous_const
  refine Continuous.mul ?_ (vdPolymerFamilies_sum_tanh_continuous_beta G J)
  refine continuous_const.mul ?_
  exact (Real.continuous_cosh.comp h_mul).pow _

/-- **Partition function continuous in `J` (at `h = 0`) via polymer
expansion**: dual of `partitionFunction_continuous_beta_h_zero` for the
coupling variable, again via the polymer-family identity. The general
form for non-zero `h` is `partitionFunction_continuous_J` in
`GibbsMeasure.lean`; this `_h_zero` version goes through the polymer
expansion and so will be the natural place to extend to higher
regularity (e.g. analyticity) in subsequent steps. -/
theorem partitionFunction_continuous_J_h_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β : ℝ) :
    Continuous (fun J : ℝ => partitionFunction G ⟨J, 0, β⟩) := by
  have h_eq : (fun J : ℝ => partitionFunction G ⟨J, 0, β⟩) =
      fun J : ℝ => (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card *
        ∑ Γ ∈ vdCompatiblePolymerFamilies G,
          ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card :=
    funext (fun J => partitionFunction_high_temp_expansion_h_zero_polymer_family G J β)
  rw [h_eq]
  have h_mul : Continuous (fun J : ℝ => β * J) :=
    continuous_const.mul continuous_id
  refine Continuous.mul ?_ (vdPolymerFamilies_sum_tanh_continuous_J G β)
  refine continuous_const.mul ?_
  exact (Real.continuous_cosh.comp h_mul).pow _

/-- **Partition function differentiable in `β` (at `h = 0`) via polymer
expansion**: strengthens `partitionFunction_continuous_beta_h_zero` from
`Continuous` to `Differentiable ℝ`, using Step 559 plus differentiability
of `cosh(β·J)^|E|` (composition of `Real.differentiable_cosh` and
`Differentiable.mul_const`, raised to the power `|E|`).

The polymer expansion realises `Z(J,0,β) = 2^|ι| · cosh(β·J)^|E| ·
∑_Γ ∏_P tanh(β·J)^|P|` as a product of three differentiable factors. -/
theorem partitionFunction_differentiable_beta_h_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J : ℝ) :
    Differentiable ℝ (fun β : ℝ => partitionFunction G ⟨J, 0, β⟩) := by
  have h_eq : (fun β : ℝ => partitionFunction G ⟨J, 0, β⟩) =
      fun β : ℝ => (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card *
        ∑ Γ ∈ vdCompatiblePolymerFamilies G,
          ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card :=
    funext (partitionFunction_high_temp_expansion_h_zero_polymer_family G J)
  rw [h_eq]
  have h_mul : Differentiable ℝ (fun β : ℝ => β * J) :=
    (differentiable_id (𝕜 := ℝ)).mul_const J
  refine Differentiable.mul ?_ (vdPolymerFamilies_sum_tanh_differentiable_beta G J)
  refine (differentiable_const _).mul ?_
  exact (Real.differentiable_cosh.comp h_mul).pow _

/-- **Partition function differentiable in `J` (at `h = 0`) via polymer
expansion**: dual of `partitionFunction_differentiable_beta_h_zero` for
the coupling variable. Strengthens `partitionFunction_continuous_J_h_zero`
from `Continuous` to `Differentiable ℝ`. -/
theorem partitionFunction_differentiable_J_h_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β : ℝ) :
    Differentiable ℝ (fun J : ℝ => partitionFunction G ⟨J, 0, β⟩) := by
  have h_eq : (fun J : ℝ => partitionFunction G ⟨J, 0, β⟩) =
      fun J : ℝ => (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card *
        ∑ Γ ∈ vdCompatiblePolymerFamilies G,
          ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card :=
    funext (fun J => partitionFunction_high_temp_expansion_h_zero_polymer_family G J β)
  rw [h_eq]
  have h_mul : Differentiable ℝ (fun J : ℝ => β * J) :=
    (differentiable_id (𝕜 := ℝ)).const_mul β
  refine Differentiable.mul ?_ (vdPolymerFamilies_sum_tanh_differentiable_J G β)
  refine (differentiable_const _).mul ?_
  exact (Real.differentiable_cosh.comp h_mul).pow _

/-- **Real-analytic version of `Finset.prod` of monomials**: for any
finite set `Γ : Finset (Finset (Sym2 ι))`, the function
`fun t : ℝ => ∏ P ∈ Γ, t ^ P.card` is real-analytic at every point.
Proof by `Finset.induction` on `Γ`. -/
theorem analyticAt_prod_pow
    {ι : Type*} (Γ : Finset (Finset (Sym2 ι))) (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ => ∏ P ∈ Γ, s ^ P.card) t := by
  classical
  induction Γ using Finset.induction_on with
  | empty =>
      simpa using (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ => (1 : ℝ)) t)
  | insert P Γ hP ih =>
      have h_step : (fun s : ℝ => ∏ P' ∈ insert P Γ, s ^ P'.card) =
          (fun s : ℝ => s ^ P.card * ∏ P' ∈ Γ, s ^ P'.card) := by
        funext s
        exact Finset.prod_insert hP
      rw [h_step]
      exact (analyticAt_id.pow P.card).mul ih

/-- **VD polymer-family sum is real-analytic in `t`**: at every `t : ℝ`,
the polymer-family sum is a polynomial in `t` and hence real-analytic.
Proof by `Finset.induction` on `vdCompatiblePolymerFamilies G` using
`analyticAt_prod_pow`. Strengthens Step 558 (`Differentiable`) to
`AnalyticAt ℝ`. -/
theorem vdPolymerFamilies_sum_analyticAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ =>
      ∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, s ^ P.card) t := by
  classical
  induction (vdCompatiblePolymerFamilies G) using Finset.induction_on with
  | empty =>
      simpa using (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ => (0 : ℝ)) t)
  | insert Γ S hΓ ih =>
      have h_step : (fun s : ℝ => ∑ Γ' ∈ insert Γ S, ∏ P ∈ Γ', s ^ P.card) =
          (fun s : ℝ => (∏ P ∈ Γ, s ^ P.card) +
            ∑ Γ' ∈ S, ∏ P ∈ Γ', s ^ P.card) := by
        funext s
        exact Finset.sum_insert hΓ
      rw [h_step]
      exact (analyticAt_prod_pow Γ t).add ih

/-- **`Real.tanh` is real-analytic at every point** (project-local helper):
derived from `tanh = sinh / cosh` together with `Real.cosh > 0` and
`AnalyticAt.div`. Mathlib does not yet export `Real.analyticAt_tanh`. -/
theorem analyticAt_real_tanh (x : ℝ) : AnalyticAt ℝ Real.tanh x := by
  have h_eq : Real.tanh = fun y : ℝ => Real.sinh y / Real.cosh y :=
    funext (fun y => Real.tanh_eq_sinh_div_cosh y)
  rw [h_eq]
  exact AnalyticAt.div Real.analyticAt_sinh Real.analyticAt_cosh
    (Real.cosh_pos x).ne'

/-- **VD polymer-family sum is real-analytic in `β` (with `J` fixed)**:
chain-rule composition of Step 561 with `analyticAt_real_tanh` and the
analytic linear factor `β ↦ β * J`. -/
theorem vdPolymerFamilies_sum_tanh_analyticAt_beta
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ) :
    AnalyticAt ℝ (fun β' : ℝ =>
      ∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, Real.tanh (β' * J) ^ P.card) β := by
  have h_mul : AnalyticAt ℝ (fun β' : ℝ => β' * J) β :=
    analyticAt_id.mul analyticAt_const
  exact (vdPolymerFamilies_sum_analyticAt G _).comp
    ((analyticAt_real_tanh _).comp h_mul)

/-- **VD polymer-family sum is real-analytic in `J` (with `β` fixed)**:
chain-rule composition of Step 561 with `analyticAt_real_tanh` and the
analytic linear factor `J ↦ β * J`. -/
theorem vdPolymerFamilies_sum_tanh_analyticAt_J
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β J : ℝ) :
    AnalyticAt ℝ (fun J' : ℝ =>
      ∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, Real.tanh (β * J') ^ P.card) J := by
  have h_mul : AnalyticAt ℝ (fun J' : ℝ => β * J') J :=
    analyticAt_const.mul analyticAt_id
  exact (vdPolymerFamilies_sum_analyticAt G _).comp
    ((analyticAt_real_tanh _).comp h_mul)

/-- **Partition function `AnalyticAt ℝ` in `β` (at `h = 0`) via polymer
expansion**: combines the §18.4 polymer-family identity (Step 548) with
Step 562 (polymer-family sum `AnalyticAt`) and `Real.analyticAt_cosh` to
obtain `AnalyticAt ℝ (fun β => partitionFunction G ⟨J, 0, β⟩) β`.
Strengthens `partitionFunction_differentiable_beta_h_zero` from
`Differentiable ℝ` to `AnalyticAt ℝ`. -/
theorem partitionFunction_analyticAt_beta_h_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ) :
    AnalyticAt ℝ (fun β' : ℝ => partitionFunction G ⟨J, 0, β'⟩) β := by
  have h_eq : (fun β' : ℝ => partitionFunction G ⟨J, 0, β'⟩) =
      fun β' : ℝ => (2 : ℝ) ^ Fintype.card ι * Real.cosh (β' * J) ^ G.edgeFinset.card *
        ∑ Γ ∈ vdCompatiblePolymerFamilies G,
          ∏ P ∈ Γ, Real.tanh (β' * J) ^ P.card :=
    funext (partitionFunction_high_temp_expansion_h_zero_polymer_family G J)
  rw [h_eq]
  have h_mul : AnalyticAt ℝ (fun β' : ℝ => β' * J) β :=
    analyticAt_id.mul analyticAt_const
  refine AnalyticAt.mul ?_ (vdPolymerFamilies_sum_tanh_analyticAt_beta G J β)
  refine analyticAt_const.mul ?_
  exact ((Real.analyticAt_cosh).comp h_mul).pow _

/-- **Partition function `AnalyticAt ℝ` in `J` (at `h = 0`) via polymer
expansion**: dual of `partitionFunction_analyticAt_beta_h_zero`. -/
theorem partitionFunction_analyticAt_J_h_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β J : ℝ) :
    AnalyticAt ℝ (fun J' : ℝ => partitionFunction G ⟨J', 0, β⟩) J := by
  have h_eq : (fun J' : ℝ => partitionFunction G ⟨J', 0, β⟩) =
      fun J' : ℝ => (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J') ^ G.edgeFinset.card *
        ∑ Γ ∈ vdCompatiblePolymerFamilies G,
          ∏ P ∈ Γ, Real.tanh (β * J') ^ P.card :=
    funext (fun J' => partitionFunction_high_temp_expansion_h_zero_polymer_family G J' β)
  rw [h_eq]
  have h_mul : AnalyticAt ℝ (fun J' : ℝ => β * J') J :=
    analyticAt_const.mul analyticAt_id
  refine AnalyticAt.mul ?_ (vdPolymerFamilies_sum_tanh_analyticAt_J G β J)
  refine analyticAt_const.mul ?_
  exact ((Real.analyticAt_cosh).comp h_mul).pow _

/-- **Free energy `AnalyticAt ℝ` in `β` (at `h = 0`) via polymer
expansion**: composes `partitionFunction_analyticAt_beta_h_zero` (Step 563)
with `AnalyticAt.log` (using `partitionFunction_pos` to discharge the
positivity hypothesis) and the constant `1/|ι|` factor.

The free energy `f = (1/|ι|) · log Z` is therefore real-analytic in `β`
at every point. Completes the §18.6 free-energy analyticity capstone at
`h = 0`. -/
theorem freeEnergy_analyticAt_beta_h_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ) :
    AnalyticAt ℝ (fun β' : ℝ => freeEnergy G ⟨J, 0, β'⟩) β := by
  unfold freeEnergy
  refine analyticAt_const.mul ?_
  exact (partitionFunction_analyticAt_beta_h_zero G J β).log
    (partitionFunction_pos G _)

/-- **Free energy `AnalyticAt ℝ` in `J` (at `h = 0`) via polymer
expansion**: dual of `freeEnergy_analyticAt_beta_h_zero`. -/
theorem freeEnergy_analyticAt_J_h_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β J : ℝ) :
    AnalyticAt ℝ (fun J' : ℝ => freeEnergy G ⟨J', 0, β⟩) J := by
  unfold freeEnergy
  refine analyticAt_const.mul ?_
  exact (partitionFunction_analyticAt_J_h_zero G β J).log
    (partitionFunction_pos G _)

/-- **Partition function `AnalyticOnNhd ℝ _ Set.univ` in `β` (at `h = 0`)**:
strengthens `partitionFunction_analyticAt_beta_h_zero` (Step 563) from
per-point `AnalyticAt` to a global `AnalyticOnNhd ℝ _ Set.univ` statement. -/
theorem partitionFunction_analyticOnNhd_beta_h_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J : ℝ) :
    AnalyticOnNhd ℝ (fun β' : ℝ => partitionFunction G ⟨J, 0, β'⟩) Set.univ :=
  fun β _ => partitionFunction_analyticAt_beta_h_zero G J β

/-- **Partition function `AnalyticOnNhd ℝ _ Set.univ` in `J` (at `h = 0`)**:
dual of `partitionFunction_analyticOnNhd_beta_h_zero`. -/
theorem partitionFunction_analyticOnNhd_J_h_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β : ℝ) :
    AnalyticOnNhd ℝ (fun J' : ℝ => partitionFunction G ⟨J', 0, β⟩) Set.univ :=
  fun J _ => partitionFunction_analyticAt_J_h_zero G β J

/-- **Free energy `AnalyticOnNhd ℝ _ Set.univ` in `β` (at `h = 0`)**:
strengthens `freeEnergy_analyticAt_beta_h_zero` (Step 564) from per-point
`AnalyticAt` to a global `AnalyticOnNhd ℝ _ Set.univ` statement. Completes
the §18.6 capstone in its global form at `h = 0`. -/
theorem freeEnergy_analyticOnNhd_beta_h_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J : ℝ) :
    AnalyticOnNhd ℝ (fun β' : ℝ => freeEnergy G ⟨J, 0, β'⟩) Set.univ :=
  fun β _ => freeEnergy_analyticAt_beta_h_zero G J β

/-- **Free energy `AnalyticOnNhd ℝ _ Set.univ` in `J` (at `h = 0`)**:
dual of `freeEnergy_analyticOnNhd_beta_h_zero`. -/
theorem freeEnergy_analyticOnNhd_J_h_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β : ℝ) :
    AnalyticOnNhd ℝ (fun J' : ℝ => freeEnergy G ⟨J', 0, β⟩) Set.univ :=
  fun J _ => freeEnergy_analyticAt_J_h_zero G β J

/-- **VD polymer-family sum has explicit polynomial derivative** (Step 575):
the polymer-family sum `t ↦ ∑_{Γ} ∏_{P ∈ Γ} t^|P|` has derivative at every
`t : ℝ` given by the explicit polynomial formula obtained from the product
rule. Specifically the derivative equals
`∑_{Γ} ∑_{Q ∈ Γ} (∏_{P ∈ Γ.erase Q} t^|P|) · ((|Q| : ℝ) · t^(|Q|-1))`,
which is itself a polynomial in `t`. Strengthens
`vdPolymerFamilies_sum_differentiable` (Step 558) by providing the
explicit derivative; closes the §18.6 deferred item "HasDerivAt with
explicit polynomial derivative" tracked in #1344. The proof combines
`HasDerivAt.fun_finset_prod` (product rule), `hasDerivAt_pow` (monomial),
and `HasDerivAt.fun_sum` (linearity). -/
theorem vdPolymerFamilies_sum_hasDerivAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ) :
    HasDerivAt (fun s : ℝ =>
        ∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, s ^ P.card)
      (∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∑ Q ∈ Γ, (∏ P ∈ Γ.erase Q, t ^ P.card) *
          ((Q.card : ℝ) * t ^ (Q.card - 1))) t := by
  refine HasDerivAt.fun_sum (fun Γ _ => ?_)
  have h := HasDerivAt.fun_finset_prod (u := Γ)
    (f := fun P : Finset (Sym2 ι) => fun s : ℝ => s ^ P.card)
    (f' := fun P : Finset (Sym2 ι) => (P.card : ℝ) * t ^ (P.card - 1))
    (x := t) (fun P _ => hasDerivAt_pow P.card t)
  simpa [smul_eq_mul] using h

/-- **Mayer expansion n-th term** (Step 587, Mayer expansion):
the contribution of `n`-element polymer sequences to `log Ξ`:
`mayerExpansionTerm G n t = ∑_{ω ∈ piFinset (allPolymers G)} ϕ^T(ω) · z(t, ω)`.
The factor `1/n!` is already absorbed into the Ursell coefficient
(Step 583), so the Mayer expansion is
`log Ξ = ∑_{n ≥ 1} mayerExpansionTerm G n t`. -/
noncomputable def mayerExpansionTerm
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (n : ℕ) (t : ℝ) : ℝ :=
  ∑ ω ∈ Fintype.piFinset (fun _ : Fin n => allPolymers G),
    ursellCoefficient ω * clusterSeqActivity t ω

/-- **n=0 Mayer term vanishes**: `mayerExpansionTerm G 0 t = 0`.
The unique `ω : Fin 0 → polymers` is the empty function;
`connectedSpanningEdgeSubsets` of the empty graph on `Fin 0` is empty
(`Connected` requires `Nonempty`), so `ursellCoefficient empty = 0`. -/
theorem mayerExpansionTerm_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ) :
    mayerExpansionTerm G 0 t = 0 := by
  unfold mayerExpansionTerm
  refine Finset.sum_eq_zero (fun ω _ => ?_)
  refine mul_eq_zero.mpr (Or.inl ?_)
  apply ursellCoefficient_eq_zero_of_disconnected
  intro h
  exact (h.nonempty.elim Fin.elim0)

/-- **n=1 Mayer term equals total polymer activity**:
`mayerExpansionTerm G 1 t = ∑_{P ∈ allPolymers G} t^|P|`.
For `n = 1`, every singleton sequence has `ϕ^T = 1` (Step 583, with
the `1/1!` factor absorbed) and `z(t, ω) = t^|ω 0|` (Step 581). The
sum over `Fin 1 → allPolymers G` reindexes to a sum over `allPolymers G`. -/
theorem mayerExpansionTerm_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ) :
    mayerExpansionTerm G 1 t =
      ∑ P ∈ allPolymers G, t ^ P.card := by
  unfold mayerExpansionTerm
  apply Finset.sum_bij (fun (ω : Fin 1 → Finset (Sym2 ι)) (_ : ω ∈ _) => ω 0)
  · intro ω hω
    rw [Fintype.mem_piFinset] at hω
    exact hω 0
  · intro ω₁ _ ω₂ _ heq
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    rw [hi]
    exact heq
  · intro P hP
    refine ⟨fun _ => P, ?_, rfl⟩
    rw [Fintype.mem_piFinset]
    intro _
    exact hP
  · intro ω _
    rw [ursellCoefficient_singleton, clusterSeqActivity_singleton, one_mul]

/-- **Cluster-sequence activity is continuous in `t`** (Step 588):
the activity factor `clusterSeqActivity t ω = ∏ i, t ^ |ω i|` is a
finite product of monomials, hence continuous in `t`. -/
theorem clusterSeqActivity_continuous
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (ω : Fin n → Finset (Sym2 ι)) :
    Continuous (fun t : ℝ => clusterSeqActivity t ω) := by
  unfold clusterSeqActivity
  refine continuous_finset_prod _ (fun i _ => ?_)
  exact continuous_id.pow _

/-- **Mayer expansion n-th term is continuous in `t`** (Step 588):
each term `mayerExpansionTerm G n t = ∑_ω ϕ^T(ω) · z(t, ω)` is a
finite sum of `(constant) · (continuous in t)`, hence continuous.
First step toward Mayer-expansion regularity matching `log Ξ`. -/
theorem mayerExpansionTerm_continuous
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (n : ℕ) :
    Continuous (fun t : ℝ => mayerExpansionTerm G n t) := by
  unfold mayerExpansionTerm
  refine continuous_finset_sum _ (fun ω _ => ?_)
  exact continuous_const.mul (clusterSeqActivity_continuous ω)

/-- **Cluster-sequence activity is differentiable in `t`** (Step 589):
the activity factor `clusterSeqActivity t ω = ∏ i, t ^ |ω i|` is a
finite product of monomials, hence differentiable in `t` on all of `ℝ`. -/
theorem clusterSeqActivity_differentiable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (ω : Fin n → Finset (Sym2 ι)) :
    Differentiable ℝ (fun t : ℝ => clusterSeqActivity t ω) := by
  unfold clusterSeqActivity
  refine Differentiable.fun_finset_prod (fun i _ => ?_)
  exact (differentiable_id (𝕜 := ℝ)).pow _

/-- **Mayer expansion n-th term is differentiable in `t`** (Step 589):
each term is a polynomial in `t` (constant Ursell coefficients times
monomial activity factors), hence differentiable. Strengthens
`mayerExpansionTerm_continuous` (Step 588) and prepares for analyticity. -/
theorem mayerExpansionTerm_differentiable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (n : ℕ) :
    Differentiable ℝ (fun t : ℝ => mayerExpansionTerm G n t) := by
  unfold mayerExpansionTerm
  refine Differentiable.fun_sum (fun ω _ => ?_)
  exact (clusterSeqActivity_differentiable ω).const_mul _

/-- **Cluster-sequence activity is real-analytic at every `t`** (Step
590): the activity factor `clusterSeqActivity t ω = ∏ i, t ^ |ω i|`
is a finite product of monomials. By induction on the index Finset
`Finset.univ : Finset (Fin n)`, each monomial `s ↦ s^k` is analytic
(`AnalyticAt.pow` of `analyticAt_id`), and analyticity is preserved by
multiplication. -/
theorem clusterSeqActivity_analyticAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (ω : Fin n → Finset (Sym2 ι)) (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ => clusterSeqActivity s ω) t := by
  classical
  unfold clusterSeqActivity
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty =>
      simpa using (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ => (1 : ℝ)) t)
  | insert i I hi ih =>
      have h_step : (fun s : ℝ => ∏ j ∈ insert i I, s ^ (ω j).card) =
          (fun s : ℝ => s ^ (ω i).card * ∏ j ∈ I, s ^ (ω j).card) := by
        funext s
        exact Finset.prod_insert hi
      rw [h_step]
      exact (analyticAt_id.pow _).mul ih

/-- **Mayer expansion n-th term is real-analytic at every `t`** (Step
590): each term is a polynomial in `t`, hence analytic. Strengthens
`mayerExpansionTerm_differentiable` (Step 589) via `AnalyticAt.fun_sum`
plus `AnalyticAt.const_mul`. -/
theorem mayerExpansionTerm_analyticAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (n : ℕ) (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ => mayerExpansionTerm G n s) t := by
  unfold mayerExpansionTerm
  refine Finset.analyticAt_fun_sum _ (fun ω _ => ?_)
  exact analyticAt_const.mul (clusterSeqActivity_analyticAt ω t)

/-- **Mayer expansion n-th term `AnalyticOnNhd ℝ _ Set.univ`** (Step
590): the global form of `mayerExpansionTerm_analyticAt`. -/
theorem mayerExpansionTerm_analyticOnNhd
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (n : ℕ) :
    AnalyticOnNhd ℝ (fun s : ℝ => mayerExpansionTerm G n s) Set.univ :=
  fun t _ => mayerExpansionTerm_analyticAt G n t

/-- **Mayer expansion partial sum** (Step 591): finite truncation of
the Mayer expansion through cluster size `N`,
`mayerPartialSum G N t = ∑_{n = 0..N} mayerExpansionTerm G n t`.
The full Mayer expansion `log Ξ = ∑_{n ≥ 0} mayerExpansionTerm G n t`
is the limit of these partial sums; convergence follows from
Kotecky-Preiss-type bounds (deferred). -/
noncomputable def mayerPartialSum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (N : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), mayerExpansionTerm G n t

/-- **Mayer partial sum is continuous in `t`** (Step 591). -/
theorem mayerPartialSum_continuous
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (N : ℕ) :
    Continuous (fun t : ℝ => mayerPartialSum G N t) := by
  unfold mayerPartialSum
  refine continuous_finset_sum _ (fun n _ => ?_)
  exact mayerExpansionTerm_continuous G n

/-- **Mayer partial sum is differentiable in `t`** (Step 591). -/
theorem mayerPartialSum_differentiable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (N : ℕ) :
    Differentiable ℝ (fun t : ℝ => mayerPartialSum G N t) := by
  unfold mayerPartialSum
  refine Differentiable.fun_sum (fun n _ => ?_)
  exact mayerExpansionTerm_differentiable G n

/-- **Mayer partial sum is real-analytic at every `t`** (Step 591). -/
theorem mayerPartialSum_analyticAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (N : ℕ) (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ => mayerPartialSum G N s) t := by
  unfold mayerPartialSum
  refine Finset.analyticAt_fun_sum _ (fun n _ => ?_)
  exact mayerExpansionTerm_analyticAt G n t

/-- **Mayer partial sum `AnalyticOnNhd ℝ _ Set.univ`** (Step 591). -/
theorem mayerPartialSum_analyticOnNhd
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (N : ℕ) :
    AnalyticOnNhd ℝ (fun s : ℝ => mayerPartialSum G N s) Set.univ :=
  fun t _ => mayerPartialSum_analyticAt G N t

/-- **Mayer partial sum at `N = 0`**: only the `n = 0` term, which
vanishes (`mayerExpansionTerm_zero`). -/
theorem mayerPartialSum_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ) :
    mayerPartialSum G 0 t = 0 := by
  unfold mayerPartialSum
  rw [show ((0 : ℕ) + 1) = 1 from rfl, Finset.sum_range_one]
  exact mayerExpansionTerm_zero G t

/-- **Mayer partial sum at `N = 1`**: the leading non-trivial truncation
equals the total polymer activity. The `n = 0` term vanishes
(`mayerExpansionTerm_zero`) and the `n = 1` term equals
`∑_{P ∈ allPolymers G} t^|P|` (`mayerExpansionTerm_one`). -/
theorem mayerPartialSum_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ) :
    mayerPartialSum G 1 t = ∑ P ∈ allPolymers G, t ^ P.card := by
  unfold mayerPartialSum
  rw [show ((1 : ℕ) + 1) = 2 from rfl, Finset.sum_range_succ, Finset.sum_range_one,
      mayerExpansionTerm_zero, mayerExpansionTerm_one, zero_add]

/-- **Mayer expansion `n = 2` term as explicit pair sum** (Step 593):
under `mayerExpansionTerm G 2 t = ∑_{(P, Q) ∈ allPolymers² with
PolymersIncompatible P Q} (-1/2) · t^|P| · t^|Q|`. The reindexing
`piFinset (Fin 2 → allPolymers G) ↔ allPolymers G ×ˢ allPolymers G`
sends `ω ↦ (ω 0, ω 1)`. The pair Ursell formula (Step 586) reduces
each summand to `(-1/2)` when incompatible and `0` otherwise. -/
theorem mayerExpansionTerm_two
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ) :
    mayerExpansionTerm G 2 t =
      ∑ pq ∈ (allPolymers G) ×ˢ (allPolymers G),
        (if PolymersIncompatible pq.1 pq.2 then (-1/2 : ℝ) else 0) *
          (t ^ pq.1.card * t ^ pq.2.card) := by
  unfold mayerExpansionTerm
  -- Reindex piFinset (Fin 2, allPolymers) ↔ allPolymers ×ˢ allPolymers via ω ↔ (ω 0, ω 1).
  apply Finset.sum_bij
    (fun (ω : Fin 2 → Finset (Sym2 ι)) (_ : ω ∈ _) => (ω 0, ω 1))
  · intro ω hω
    rw [Fintype.mem_piFinset] at hω
    rw [Finset.mem_product]
    exact ⟨hω 0, hω 1⟩
  · intro ω₁ _ ω₂ _ heq
    funext i
    fin_cases i
    · exact (Prod.mk.inj heq).1
    · exact (Prod.mk.inj heq).2
  · intro pq hpq
    rw [Finset.mem_product] at hpq
    refine ⟨fun i => if i = 0 then pq.1 else pq.2, ?_, ?_⟩
    · rw [Fintype.mem_piFinset]
      intro i
      fin_cases i
      · simpa using hpq.1
      · simpa using hpq.2
    · rfl
  · intro ω hω
    rw [Fintype.mem_piFinset] at hω
    rw [ursellCoefficient_pair, clusterSeqActivity]
    simp only [Fin.prod_univ_two]

/-- **Mayer expansion term continuous in `β` (with `J` fixed)** (Step
594): chain composition of `mayerExpansionTerm_continuous` with
`continuous_real_tanh` and `Continuous.mul`. -/
theorem mayerExpansionTerm_tanh_continuous_beta
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (n : ℕ) (J : ℝ) :
    Continuous (fun β : ℝ => mayerExpansionTerm G n (Real.tanh (β * J))) := by
  have h_mul : Continuous (fun β : ℝ => β * J) :=
    continuous_id.mul continuous_const
  exact (mayerExpansionTerm_continuous G n).comp (continuous_real_tanh.comp h_mul)

/-- **Mayer expansion term continuous in `J` (with `β` fixed)** (Step
594). -/
theorem mayerExpansionTerm_tanh_continuous_J
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (n : ℕ) (β : ℝ) :
    Continuous (fun J : ℝ => mayerExpansionTerm G n (Real.tanh (β * J))) := by
  have h_mul : Continuous (fun J : ℝ => β * J) :=
    continuous_const.mul continuous_id
  exact (mayerExpansionTerm_continuous G n).comp (continuous_real_tanh.comp h_mul)

/-- **Mayer partial sum continuous in `β` (with `J` fixed)** (Step
594). -/
theorem mayerPartialSum_tanh_continuous_beta
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (N : ℕ) (J : ℝ) :
    Continuous (fun β : ℝ => mayerPartialSum G N (Real.tanh (β * J))) := by
  have h_mul : Continuous (fun β : ℝ => β * J) :=
    continuous_id.mul continuous_const
  exact (mayerPartialSum_continuous G N).comp (continuous_real_tanh.comp h_mul)

/-- **Mayer partial sum continuous in `J` (with `β` fixed)** (Step
594). -/
theorem mayerPartialSum_tanh_continuous_J
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (N : ℕ) (β : ℝ) :
    Continuous (fun J : ℝ => mayerPartialSum G N (Real.tanh (β * J))) := by
  have h_mul : Continuous (fun J : ℝ => β * J) :=
    continuous_const.mul continuous_id
  exact (mayerPartialSum_continuous G N).comp (continuous_real_tanh.comp h_mul)

/-- **Mayer expansion term differentiable in `β` (with `J` fixed)**
(Step 595): chain rule with `differentiable_real_tanh` and the
linear factor `β ↦ β * J`. -/
theorem mayerExpansionTerm_tanh_differentiable_beta
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (n : ℕ) (J : ℝ) :
    Differentiable ℝ (fun β : ℝ => mayerExpansionTerm G n (Real.tanh (β * J))) := by
  exact (mayerExpansionTerm_differentiable G n).comp
    (differentiable_real_tanh.comp ((differentiable_id (𝕜 := ℝ)).mul_const _))

/-- **Mayer expansion term differentiable in `J` (with `β` fixed)** (Step 595). -/
theorem mayerExpansionTerm_tanh_differentiable_J
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (n : ℕ) (β : ℝ) :
    Differentiable ℝ (fun J : ℝ => mayerExpansionTerm G n (Real.tanh (β * J))) := by
  exact (mayerExpansionTerm_differentiable G n).comp
    (differentiable_real_tanh.comp ((differentiable_id (𝕜 := ℝ)).const_mul _))

/-- **Mayer partial sum differentiable in `β` (with `J` fixed)** (Step 595). -/
theorem mayerPartialSum_tanh_differentiable_beta
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (N : ℕ) (J : ℝ) :
    Differentiable ℝ (fun β : ℝ => mayerPartialSum G N (Real.tanh (β * J))) := by
  exact (mayerPartialSum_differentiable G N).comp
    (differentiable_real_tanh.comp ((differentiable_id (𝕜 := ℝ)).mul_const _))

/-- **Mayer partial sum differentiable in `J` (with `β` fixed)** (Step 595). -/
theorem mayerPartialSum_tanh_differentiable_J
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (N : ℕ) (β : ℝ) :
    Differentiable ℝ (fun J : ℝ => mayerPartialSum G N (Real.tanh (β * J))) := by
  exact (mayerPartialSum_differentiable G N).comp
    (differentiable_real_tanh.comp ((differentiable_id (𝕜 := ℝ)).const_mul _))

/-- **Mayer expansion term real-analytic in `β` (with `J` fixed)**
(Step 596): chain of `mayerExpansionTerm_analyticAt` (Step 590),
`analyticAt_real_tanh`, and the analytic linear factor `β ↦ β·J`. -/
theorem mayerExpansionTerm_tanh_analyticAt_beta
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (n : ℕ) (J β : ℝ) :
    AnalyticAt ℝ (fun β' : ℝ => mayerExpansionTerm G n (Real.tanh (β' * J))) β := by
  have h_lin : AnalyticAt ℝ (fun β' : ℝ => β' * J) β :=
    analyticAt_id.mul analyticAt_const
  exact (mayerExpansionTerm_analyticAt G n _).comp ((analyticAt_real_tanh _).comp h_lin)

/-- **Mayer expansion term real-analytic in `J` (with `β` fixed)** (Step 596). -/
theorem mayerExpansionTerm_tanh_analyticAt_J
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (n : ℕ) (β J : ℝ) :
    AnalyticAt ℝ (fun J' : ℝ => mayerExpansionTerm G n (Real.tanh (β * J'))) J := by
  have h_lin : AnalyticAt ℝ (fun J' : ℝ => β * J') J :=
    analyticAt_const.mul analyticAt_id
  exact (mayerExpansionTerm_analyticAt G n _).comp ((analyticAt_real_tanh _).comp h_lin)

/-- **Mayer partial sum real-analytic in `β` (with `J` fixed)** (Step 596). -/
theorem mayerPartialSum_tanh_analyticAt_beta
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (N : ℕ) (J β : ℝ) :
    AnalyticAt ℝ (fun β' : ℝ => mayerPartialSum G N (Real.tanh (β' * J))) β := by
  have h_lin : AnalyticAt ℝ (fun β' : ℝ => β' * J) β :=
    analyticAt_id.mul analyticAt_const
  exact (mayerPartialSum_analyticAt G N _).comp ((analyticAt_real_tanh _).comp h_lin)

/-- **Mayer partial sum real-analytic in `J` (with `β` fixed)** (Step 596). -/
theorem mayerPartialSum_tanh_analyticAt_J
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (N : ℕ) (β J : ℝ) :
    AnalyticAt ℝ (fun J' : ℝ => mayerPartialSum G N (Real.tanh (β * J'))) J := by
  have h_lin : AnalyticAt ℝ (fun J' : ℝ => β * J') J :=
    analyticAt_const.mul analyticAt_id
  exact (mayerPartialSum_analyticAt G N _).comp ((analyticAt_real_tanh _).comp h_lin)

/-- **Mayer partial sum `AnalyticOnNhd ℝ _ Set.univ` in `β`** (Step 596). -/
theorem mayerPartialSum_tanh_analyticOnNhd_beta
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (N : ℕ) (J : ℝ) :
    AnalyticOnNhd ℝ (fun β' : ℝ => mayerPartialSum G N (Real.tanh (β' * J))) Set.univ :=
  fun β _ => mayerPartialSum_tanh_analyticAt_beta G N J β

/-- **Mayer partial sum `AnalyticOnNhd ℝ _ Set.univ` in `J`** (Step 596). -/
theorem mayerPartialSum_tanh_analyticOnNhd_J
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (N : ℕ) (β : ℝ) :
    AnalyticOnNhd ℝ (fun J' : ℝ => mayerPartialSum G N (Real.tanh (β * J'))) Set.univ :=
  fun J _ => mayerPartialSum_tanh_analyticAt_J G N β J

/-- **Mayer expansion `n = 2` term as filter sum** (Step 597): the
ordered-pair sum from Step 593 reduces to a sum over the incompatible
pairs only,
`mayerExpansionTerm G 2 t = (-1/2) · ∑_{(P, Q) ∈ allPolymers² with
PolymersIncompatible P Q} t^|P| · t^|Q|`.
The if-then-else summand vanishes on compatible pairs, so the sum
restricts to the filter `(allPolymers G ×ˢ allPolymers G).filter
(fun pq => PolymersIncompatible pq.1 pq.2)`. -/
theorem mayerExpansionTerm_two_filter
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ) :
    mayerExpansionTerm G 2 t =
      (-1/2 : ℝ) *
        ∑ pq ∈ ((allPolymers G) ×ˢ (allPolymers G)).filter
            (fun pq => PolymersIncompatible pq.1 pq.2),
          (t ^ pq.1.card * t ^ pq.2.card) := by
  rw [mayerExpansionTerm_two]
  simp_rw [ite_mul, zero_mul]
  rw [← Finset.sum_filter, ← Finset.mul_sum]

/-- **Mayer expansion term vanishes at `t = 0`** (Step 598):
`mayerExpansionTerm G n 0 = 0` for every `n : ℕ`. For `n = 0`,
`ursellCoefficient` already vanishes (Step 587). For `n ≥ 1`, every
polymer `ω i` has `|ω i| ≥ 1`, so `0 ^ |ω i| = 0` and the product
`clusterSeqActivity 0 ω = ∏ i, 0 ^ |ω i|` contains a zero factor. -/
theorem mayerExpansionTerm_at_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (n : ℕ) :
    mayerExpansionTerm G n 0 = 0 := by
  match n with
  | 0 => exact mayerExpansionTerm_zero G 0
  | k + 1 =>
    unfold mayerExpansionTerm
    refine Finset.sum_eq_zero (fun ω hω => ?_)
    rw [Fintype.mem_piFinset] at hω
    have h_polymer : IsPolymer G (ω 0) := mem_allPolymers.mp (hω 0)
    have h_pos : 0 < (ω 0).card := h_polymer.nonempty.card_pos
    have h_zero : (0 : ℝ) ^ (ω 0).card = 0 := zero_pow h_pos.ne'
    have h_prod : clusterSeqActivity (0 : ℝ) ω = 0 := by
      unfold clusterSeqActivity
      exact Finset.prod_eq_zero (Finset.mem_univ 0) h_zero
    rw [h_prod, mul_zero]

/-- **Mayer partial sum vanishes at `t = 0`** (Step 598): consequence
of `mayerExpansionTerm_at_zero` summed over `Finset.range (N + 1)`. -/
theorem mayerPartialSum_at_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (N : ℕ) :
    mayerPartialSum G N 0 = 0 := by
  unfold mayerPartialSum
  refine Finset.sum_eq_zero (fun n _ => ?_)
  exact mayerExpansionTerm_at_zero G n

/-- **Polymer-family sum at `t = 0`** (Step 599):
`∑_{Γ ∈ vdCompatiblePolymerFamilies G} ∏_{P ∈ Γ} 0^|P| = 1`. Only the
empty family `Γ = ∅` contributes (its empty product equals `1`); any
non-empty `Γ` contains a polymer with `|P| ≥ 1`, so `0^|P| = 0` and
the product vanishes. -/
theorem vdPolymerFamilies_sum_at_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    (∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, (0 : ℝ) ^ P.card) = 1 := by
  classical
  have h_empty_in :
      (∅ : Finset (Finset (Sym2 ι))) ∈ vdCompatiblePolymerFamilies G := by
    rw [mem_vdCompatiblePolymerFamilies]
    exact ⟨Finset.empty_subset _, IsCompatiblePolymerFamilyVertexDisjoint.empty G⟩
  have h_nonempty_zero : ∀ Γ ∈ vdCompatiblePolymerFamilies G,
      Γ ≠ ∅ → (∏ P ∈ Γ, (0 : ℝ) ^ P.card) = 0 := by
    intro Γ hΓ hne
    rw [mem_vdCompatiblePolymerFamilies] at hΓ
    obtain ⟨P, hP⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hP_polymer : IsPolymer G P := mem_allPolymers.mp (hΓ.1 hP)
    have hP_pos : 0 < P.card := hP_polymer.nonempty.card_pos
    exact Finset.prod_eq_zero hP (zero_pow hP_pos.ne')
  rw [Finset.sum_eq_single ∅]
  · rw [Finset.prod_empty]
  · intro Γ hΓ hne
    exact h_nonempty_zero Γ hΓ hne
  · intro h
    exact absurd h_empty_in h

/-- **`connectedSpanningEdgeSubsets` cardinality bound** (Step 602):
the connected-spanning edge subsets are a filter of the powerset of
`G.edgeFinset`, hence their count is at most `2^|G.edgeFinset|`. -/
theorem connectedSpanningEdgeSubsets_card_le_pow
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (connectedSpanningEdgeSubsets G).card ≤ 2 ^ G.edgeFinset.card := by
  classical
  unfold connectedSpanningEdgeSubsets
  refine (Finset.card_filter_le _ _).trans ?_
  rw [Finset.card_powerset]

/-- **Ursell coefficient absolute bound** (Step 601): the triangle
inequality on the alternating-sign sum gives
`|ϕ^T(ω)| ≤ |connectedSpanningEdgeSubsets G(ω)| / n!`. Since each
summand `(-1)^|S|` has absolute value `1`, summing `|·|` gives the
cardinality of the index set. Useful for convergence estimates of the
Mayer expansion. -/
theorem ursellCoefficient_abs_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (ω : Fin n → Finset (Sym2 ι)) :
    |ursellCoefficient ω| ≤
      ((connectedSpanningEdgeSubsets (polymerSeqIncompatibilityGraph ω)).card : ℝ)
        / n.factorial := by
  unfold ursellCoefficient
  rw [abs_div]
  have h_fact_abs : |((n.factorial : ℝ))| = n.factorial :=
    abs_of_nonneg (Nat.cast_nonneg _)
  rw [h_fact_abs]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h_each : ∀ S ∈ connectedSpanningEdgeSubsets (polymerSeqIncompatibilityGraph ω),
      |((-1 : ℝ) ^ S.card)| = 1 := by
    intro S _
    rw [abs_pow, abs_neg, abs_one, one_pow]
  rw [Finset.sum_congr rfl h_each, Finset.sum_const, Nat.smul_one_eq_cast]

/-- **Uniform Ursell coefficient bound** (Step 603): combining Step
601 (|ϕ^T| ≤ card / n!) and Step 602 (card ≤ 2^|E|) gives
`|ϕ^T(ω)| ≤ 2^|E(G(ω))| / n!`. The classical Mayer-expansion uniform
bound from connected-spanning subgraphs of the incompatibility graph. -/
theorem ursellCoefficient_abs_le_pow_div_factorial
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (ω : Fin n → Finset (Sym2 ι)) :
    |ursellCoefficient ω| ≤
      (2 ^ (polymerSeqIncompatibilityGraph ω).edgeFinset.card : ℝ)
        / (n.factorial : ℝ) := by
  refine (ursellCoefficient_abs_le ω).trans ?_
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  exact_mod_cast connectedSpanningEdgeSubsets_card_le_pow _

/-- **Polymer-family sum ≥ 1 under `t ≥ 0`** (Step 605): for any
non-negative activity parameter `t`, the empty family `Γ = ∅`
contributes `1` and all other families contribute non-negative
products `∏ P ∈ Γ, t^|P| ≥ 0`. Hence the total is at least `1`.
This generalises `one_le_vdPolymerFamilies_sum` (Step 549) from the
tanh form to a generic non-negative activity. -/
theorem vdPolymerFamilies_sum_ge_one_of_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    1 ≤ ∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card := by
  classical
  have h_empty_in :
      (∅ : Finset (Finset (Sym2 ι))) ∈ vdCompatiblePolymerFamilies G := by
    rw [mem_vdCompatiblePolymerFamilies]
    exact ⟨Finset.empty_subset _, IsCompatiblePolymerFamilyVertexDisjoint.empty G⟩
  have h_nonneg : ∀ Γ ∈ vdCompatiblePolymerFamilies G,
      0 ≤ ∏ P ∈ Γ, t ^ P.card :=
    fun _ _ => Finset.prod_nonneg (fun _ _ => pow_nonneg ht _)
  have h_empty_eq : (1 : ℝ) =
      ∏ P ∈ (∅ : Finset (Finset (Sym2 ι))), t ^ P.card := (Finset.prod_empty).symm
  rw [h_empty_eq]
  exact Finset.single_le_sum h_nonneg h_empty_in

/-- **Polymer-family sum ≤ `(1+t)^|E|` under `t ≥ 0`** (Step 629):
generic upper bound generalising Step 552's tanh-form bound. Proof:
`evenSubgraphs G ⊆ G.edgeFinset.powerset`, so the sum over even
subgraphs of `t^|X|` is at most the sum over all subsets, which equals
`(1+t)^|E|` by binomial expansion (`Finset.prod_one_add`). -/
theorem vdPolymerFamilies_sum_le_one_plus_pow_of_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    (∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card) ≤
      (1 + t) ^ G.edgeFinset.card := by
  classical
  rw [← evenSubgraphs_sum_eq_vdPolymerFamilies_sum G t,
      evenSubgraphs_eq_inline_filter]
  have hpower :
      (1 + t) ^ G.edgeFinset.card =
        ∑ X ∈ G.edgeFinset.powerset, t ^ X.card := by
    rw [← Finset.prod_const, Finset.prod_one_add]
    refine Finset.sum_congr rfl (fun X _ => ?_)
    rw [Finset.prod_const]
  rw [hpower]
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
  intro X _ _
  exact pow_nonneg ht _

/-- **Polymer-family sum > 0 under `t ≥ 0`** (Step 605):
strict positivity follows from `≥ 1` and `0 < 1`. Useful to ensure
`Real.log (vdPolymerFamilies_sum G t)` is well-defined. -/
theorem vdPolymerFamilies_sum_pos_of_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 < ∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card :=
  lt_of_lt_of_le zero_lt_one (vdPolymerFamilies_sum_ge_one_of_nonneg G ht)

/-- **`log (vdPolymerFamilies_sum)` is real-analytic at any `t ≥ 0`**
(Step 606): `AnalyticAt ℝ (Real.log ∘ vdPolymerFamilies_sum G) t` via
`AnalyticAt.log` (Step 561) plus positivity (Step 605). Sets up the
LHS of the Mayer expansion identity as a real-analytic function on
the non-negative axis. -/
theorem log_vdPolymerFamilies_sum_analyticAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    AnalyticAt ℝ
      (fun s : ℝ => Real.log (∑ Γ ∈ vdCompatiblePolymerFamilies G,
                                 ∏ P ∈ Γ, s ^ P.card)) t :=
  (vdPolymerFamilies_sum_analyticAt G t).log
    (vdPolymerFamilies_sum_pos_of_nonneg G ht)

/-- **`log (vdPolymerFamilies_sum)` AnalyticOnNhd over `[0, ∞)`**
(Step 607): global form of Step 606 — at every `t ∈ Set.Ici 0`, the
function is `AnalyticAt`, hence `AnalyticOnNhd ℝ _ (Set.Ici 0)`. -/
theorem log_vdPolymerFamilies_sum_analyticOnNhd_Ici_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    AnalyticOnNhd ℝ
      (fun s : ℝ => Real.log (∑ Γ ∈ vdCompatiblePolymerFamilies G,
                                 ∏ P ∈ Γ, s ^ P.card)) (Set.Ici 0) :=
  fun _ ht => log_vdPolymerFamilies_sum_analyticAt G ht

/-- **`Real.tanh` is non-negative under non-negative argument** (helper
for Step 608): `0 ≤ x → 0 ≤ Real.tanh x`. Uses `Real.sinh_nonneg_iff`
and `Real.cosh_pos`. -/
private theorem real_tanh_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_nonneg (Real.sinh_nonneg_iff.mpr hx) (Real.cosh_pos x).le

/-- **`log (vdPolymerFamilies_sum tanh(β·J))` analyticAt in `β`**
(Step 608): under `0 ≤ β·J`, the function
`β' ↦ Real.log (∑_Γ ∏_{P ∈ Γ} tanh(β'·J)^|P|)` is `AnalyticAt ℝ` at `β`.
Combines Step 562 (vdSum analytic in β via tanh chain) with positivity
of vdSum at `tanh(β·J) ≥ 0` (Steps 605 + helper). -/
theorem log_vdPolymerFamilies_sum_tanh_analyticAt_beta
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ) (hβJ : 0 ≤ β * J) :
    AnalyticAt ℝ
      (fun β' : ℝ => Real.log
        (∑ Γ ∈ vdCompatiblePolymerFamilies G,
          ∏ P ∈ Γ, Real.tanh (β' * J) ^ P.card)) β := by
  refine (vdPolymerFamilies_sum_tanh_analyticAt_beta G J β).log ?_
  exact vdPolymerFamilies_sum_pos_of_nonneg G (real_tanh_nonneg hβJ)

/-- **`log (vdPolymerFamilies_sum tanh(β·J))` analyticAt in `J`**
(Step 608): dual of `_beta`. -/
theorem log_vdPolymerFamilies_sum_tanh_analyticAt_J
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β J : ℝ) (hβJ : 0 ≤ β * J) :
    AnalyticAt ℝ
      (fun J' : ℝ => Real.log
        (∑ Γ ∈ vdCompatiblePolymerFamilies G,
          ∏ P ∈ Γ, Real.tanh (β * J') ^ P.card)) J := by
  refine (vdPolymerFamilies_sum_tanh_analyticAt_J G β J).log ?_
  exact vdPolymerFamilies_sum_pos_of_nonneg G (real_tanh_nonneg hβJ)

/-- **Mayer expansion term absolute bound** (Step 604): the triangle
inequality applied to the Mayer term gives
`|mayerExpansionTerm G n t| ≤ ∑_ω |ϕ^T(ω)| · |z(t, ω)|`. -/
theorem mayerExpansionTerm_abs_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (n : ℕ) (t : ℝ) :
    |mayerExpansionTerm G n t| ≤
      ∑ ω ∈ Fintype.piFinset (fun _ : Fin n => allPolymers G),
        |ursellCoefficient ω| * |clusterSeqActivity t ω| := by
  unfold mayerExpansionTerm
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  exact Finset.sum_congr rfl (fun ω _ => abs_mul _ _)

/-- **Uniform Ursell bound** (Step 615): independent-of-ω bound
`|ϕ^T(ω)| ≤ 2^(n choose 2) / n!`. Combines Step 603 (`2^|E(G(ω))| / n!`)
with Mathlib's `SimpleGraph.card_edgeFinset_le_card_choose_two`
(graph on `Fin n` has at most `n.choose 2` edges). -/
theorem ursellCoefficient_abs_le_choose_pow_div_factorial
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (ω : Fin n → Finset (Sym2 ι)) :
    |ursellCoefficient ω| ≤ (2 ^ (n.choose 2) : ℝ) / (n.factorial : ℝ) := by
  refine (ursellCoefficient_abs_le_pow_div_factorial ω).trans ?_
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  refine pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) ?_
  have h := SimpleGraph.card_edgeFinset_le_card_choose_two
              (G := polymerSeqIncompatibilityGraph ω)
  rw [show Fintype.card (Fin n) = n from Fintype.card_fin n] at h
  exact h

/-- **Mayer identity at `t = 0`** (Step 600, milestone): the first
verified instance of the Mayer expansion identity
`log Ξ = ∑_{n ≥ 0} mayerExpansionTerm G n t`. At `t = 0`,
both sides equal `0`:
- `log (vdPolymerFamilies_sum G 0) = log 1 = 0` via Step 599
- `mayerPartialSum G N 0 = 0` via Step 598

This is a trivial special case symbolically marking the structural
target. The general identity for non-zero `t` requires substantial
combinatorial work (Mayer/Ursell algebraic manipulations of formal
power series); it remains deferred. -/
theorem mayer_identity_at_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (N : ℕ) :
    Real.log (∑ Γ ∈ vdCompatiblePolymerFamilies G,
              ∏ P ∈ Γ, (0 : ℝ) ^ P.card) =
      mayerPartialSum G N 0 := by
  rw [vdPolymerFamilies_sum_at_zero, Real.log_one, mayerPartialSum_at_zero]

/-- **Mayer identity at `β·J = 0`** (Step 609): trivial extension of
Step 600 to the β/J directions. When `β·J = 0`, `tanh(β·J) = 0`,
reducing both sides to the t=0 case. -/
theorem mayer_identity_at_betaJ_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβJ : β * J = 0) (N : ℕ) :
    Real.log (∑ Γ ∈ vdCompatiblePolymerFamilies G,
              ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) =
      mayerPartialSum G N (Real.tanh (β * J)) := by
  rw [hβJ, Real.tanh_zero]
  exact mayer_identity_at_zero G N

/-- **Mayer identity at `β = 0`** (Step 609 specialisation). -/
theorem mayer_identity_at_beta_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J : ℝ) (N : ℕ) :
    Real.log (∑ Γ ∈ vdCompatiblePolymerFamilies G,
              ∏ P ∈ Γ, Real.tanh ((0 : ℝ) * J) ^ P.card) =
      mayerPartialSum G N (Real.tanh ((0 : ℝ) * J)) :=
  mayer_identity_at_betaJ_zero G (zero_mul J) N

/-- **Mayer identity at `J = 0`** (Step 609 specialisation). -/
theorem mayer_identity_at_J_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β : ℝ) (N : ℕ) :
    Real.log (∑ Γ ∈ vdCompatiblePolymerFamilies G,
              ∏ P ∈ Γ, Real.tanh (β * (0 : ℝ)) ^ P.card) =
      mayerPartialSum G N (Real.tanh (β * (0 : ℝ))) :=
  mayer_identity_at_betaJ_zero G (mul_zero β) N


/-- **Polymer free energy** (Step 610): named wrapper for the LHS of
the Mayer expansion identity,
`polymerFreeEnergy G t := Real.log (∑_Γ ∏_{P ∈ Γ} t^|P|)`. The Mayer
identity then reads `polymerFreeEnergy G t = ∑_{n ≥ 0} mayerExpansionTerm G n t`
(general-`t` identity deferred). -/
noncomputable def polymerFreeEnergy
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ) : ℝ :=
  Real.log (∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card)

/-- **`polymerFreeEnergy` at `t = 0`** (Step 610): equals `0` since
`vdPolymerFamilies_sum G 0 = 1`. -/
theorem polymerFreeEnergy_at_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    polymerFreeEnergy G 0 = 0 := by
  unfold polymerFreeEnergy
  rw [vdPolymerFamilies_sum_at_zero, Real.log_one]

/-- **`polymerFreeEnergy` analyticAt for `t ≥ 0`** (Step 610): direct
restatement of Step 606 in the named-wrapper form. -/
theorem polymerFreeEnergy_analyticAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    AnalyticAt ℝ (fun s : ℝ => polymerFreeEnergy G s) t :=
  log_vdPolymerFamilies_sum_analyticAt G ht

/-- **`polymerFreeEnergy` AnalyticOnNhd over `[0, ∞)`** (Step 610). -/
theorem polymerFreeEnergy_analyticOnNhd_Ici_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    AnalyticOnNhd ℝ (fun s : ℝ => polymerFreeEnergy G s) (Set.Ici 0) :=
  log_vdPolymerFamilies_sum_analyticOnNhd_Ici_zero G

/-- **`polymerFreeEnergy` is `ContinuousAt` for `t ≥ 0`** (Step 611):
direct consequence of analyticAt. -/
theorem polymerFreeEnergy_continuousAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    ContinuousAt (fun s : ℝ => polymerFreeEnergy G s) t :=
  (polymerFreeEnergy_analyticAt G ht).continuousAt

/-- **`polymerFreeEnergy` is `DifferentiableAt` for `t ≥ 0`** (Step 611). -/
theorem polymerFreeEnergy_differentiableAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    DifferentiableAt ℝ (fun s : ℝ => polymerFreeEnergy G s) t :=
  (polymerFreeEnergy_analyticAt G ht).differentiableAt

/-- **Mayer identity at `t = 0` in `polymerFreeEnergy` form** (Step 611):
restatement of Step 600 using the named wrapper. -/
theorem polymerFreeEnergy_eq_mayerPartialSum_at_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (N : ℕ) :
    polymerFreeEnergy G 0 = mayerPartialSum G N 0 := by
  rw [polymerFreeEnergy_at_zero, mayerPartialSum_at_zero]

/-- **freeEnergy decomposition with `polymerFreeEnergy`** (Step 612):
under `0 < |ι|` and `0 ≤ β·J`,
  `f = log 2 + (|E|/|ι|) · log cosh(β·J) + polymerFreeEnergy G (tanh(β·J)) / |ι|`.
Restatement of `freeEnergy_high_temp_expansion_h_zero_closed` (Step 317)
using the polymer-family form (Step 547 bijection wraps the
`evenSubgraphs` sum into the `vdCompatiblePolymerFamilies` form). -/
theorem freeEnergy_eq_polymerFreeEnergy
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι) :
    freeEnergy G ⟨J, 0, β⟩ =
      Real.log 2 +
        (G.edgeFinset.card : ℝ) / Fintype.card ι *
          Real.log (Real.cosh (β * J)) +
        polymerFreeEnergy G (Real.tanh (β * J)) / Fintype.card ι := by
  rw [freeEnergy_high_temp_expansion_h_zero_closed G J β hβJ hne]
  unfold polymerFreeEnergy
  rw [← evenSubgraphs_eq_inline_filter,
      evenSubgraphs_sum_eq_vdPolymerFamilies_sum G (Real.tanh (β * J))]

/-- **Ferromagnetic `freeEnergy = log 2 + ... + polymerFreeEnergy/|ι|`**
(Step 616): under `0 ≤ J`, `0 < β`, `0 < |ι|`, the Step 612 decomposition
holds (since `0 ≤ β·J` follows from `mul_nonneg`). -/
theorem freeEnergy_eq_polymerFreeEnergy_ferromagnetic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Fintype.card ι) :
    freeEnergy G ⟨J, 0, β⟩ =
      Real.log 2 +
        (G.edgeFinset.card : ℝ) / Fintype.card ι *
          Real.log (Real.cosh (β * J)) +
        polymerFreeEnergy G (Real.tanh (β * J)) / Fintype.card ι :=
  freeEnergy_eq_polymerFreeEnergy G J β (mul_nonneg hβ.le hJ) hne

/-- **Mayer identity at `β·J = 0` in `polymerFreeEnergy` form** (Step 617):
restate Step 609 using the named wrapper. -/
theorem polymerFreeEnergy_eq_mayerPartialSum_at_betaJ_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβJ : β * J = 0) (N : ℕ) :
    polymerFreeEnergy G (Real.tanh (β * J)) =
      mayerPartialSum G N (Real.tanh (β * J)) := by
  unfold polymerFreeEnergy
  exact mayer_identity_at_betaJ_zero G hβJ N

/-- **Mayer identity at `β = 0` in `polymerFreeEnergy` form** (Step 617). -/
theorem polymerFreeEnergy_eq_mayerPartialSum_at_beta_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J : ℝ) (N : ℕ) :
    polymerFreeEnergy G (Real.tanh ((0 : ℝ) * J)) =
      mayerPartialSum G N (Real.tanh ((0 : ℝ) * J)) :=
  polymerFreeEnergy_eq_mayerPartialSum_at_betaJ_zero G (zero_mul J) N

/-- **Mayer identity at `J = 0` in `polymerFreeEnergy` form** (Step 617). -/
theorem polymerFreeEnergy_eq_mayerPartialSum_at_J_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β : ℝ) (N : ℕ) :
    polymerFreeEnergy G (Real.tanh (β * (0 : ℝ))) =
      mayerPartialSum G N (Real.tanh (β * (0 : ℝ))) :=
  polymerFreeEnergy_eq_mayerPartialSum_at_betaJ_zero G (mul_zero β) N

/-- **`polymerFreeEnergy` analyticAt in `β`** (Step 613): named-wrapper
restatement of Step 608. -/
theorem polymerFreeEnergy_tanh_analyticAt_beta
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ) (hβJ : 0 ≤ β * J) :
    AnalyticAt ℝ
      (fun β' : ℝ => polymerFreeEnergy G (Real.tanh (β' * J))) β :=
  log_vdPolymerFamilies_sum_tanh_analyticAt_beta G J β hβJ

/-- **`polymerFreeEnergy` analyticAt in `J`** (Step 613). -/
theorem polymerFreeEnergy_tanh_analyticAt_J
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β J : ℝ) (hβJ : 0 ≤ β * J) :
    AnalyticAt ℝ
      (fun J' : ℝ => polymerFreeEnergy G (Real.tanh (β * J'))) J :=
  log_vdPolymerFamilies_sum_tanh_analyticAt_J G β J hβJ

/-- **`polymerFreeEnergy` AnalyticOnNhd in `β` over `[0, ∞)` (under
`0 ≤ J`)** (Step 613): for fixed `J ≥ 0`, the function is analytic at
every `β ≥ 0` since `0 ≤ β·J = β·J` follows from `mul_nonneg`. -/
theorem polymerFreeEnergy_tanh_analyticOnNhd_beta_Ici_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) :
    AnalyticOnNhd ℝ
      (fun β' : ℝ => polymerFreeEnergy G (Real.tanh (β' * J))) (Set.Ici 0) :=
  fun β hβ => polymerFreeEnergy_tanh_analyticAt_beta G J β (mul_nonneg hβ hJ)

/-- **`polymerFreeEnergy` AnalyticOnNhd in `J` over `[0, ∞)` (under
`0 ≤ β`)** (Step 613). -/
theorem polymerFreeEnergy_tanh_analyticOnNhd_J_Ici_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β : ℝ} (hβ : 0 ≤ β) :
    AnalyticOnNhd ℝ
      (fun J' : ℝ => polymerFreeEnergy G (Real.tanh (β * J'))) (Set.Ici 0) :=
  fun J hJ => polymerFreeEnergy_tanh_analyticAt_J G β J (mul_nonneg hβ hJ)

/-- **`mayerPartialSum G 2 t` explicit formula** (Step 614):
`mayerPartialSum G 2 t = ∑_{P ∈ allPolymers G} t^|P|
                       - (1/2) ∑_{(P, Q) ∈ allPolymers², PolymersIncompatible P Q}
                          t^|P| · t^|Q|`.
The `N = 2` truncation of the Mayer expansion expressed entirely via
explicit polymer sums. Combines Step 592 (n=1: total polymer activity)
with Step 597 (n=2 filter form). -/
theorem mayerPartialSum_two
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ) :
    mayerPartialSum G 2 t =
      (∑ P ∈ allPolymers G, t ^ P.card) +
        (-1/2 : ℝ) *
          ∑ pq ∈ ((allPolymers G) ×ˢ (allPolymers G)).filter
              (fun pq => PolymersIncompatible pq.1 pq.2),
            (t ^ pq.1.card * t ^ pq.2.card) := by
  unfold mayerPartialSum
  rw [show ((2 : ℕ) + 1) = 3 from rfl,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
      mayerExpansionTerm_zero, mayerExpansionTerm_one,
      mayerExpansionTerm_two_filter, zero_add]

/-- **Mayer identity for empty-polymer graphs** (Step 618): when
`allPolymers G = ∅`, `polymerFreeEnergy G t = mayerPartialSum G N t = 0`
for any `t` and `N`. The polymer-family sum reduces to the empty
family contributing 1, so `log 1 = 0`; on the Mayer side, for `n ≥ 1`
every entry `ω i` would have to be in `allPolymers G = ∅`, an empty
domain, so the piFinset is empty and the sum vanishes. -/
theorem mayer_identity_of_no_polymers
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h_no : allPolymers G = ∅) (t : ℝ) (N : ℕ) :
    polymerFreeEnergy G t = mayerPartialSum G N t := by
  classical
  have h_vd : vdCompatiblePolymerFamilies G = {∅} := by
    apply Finset.ext
    intro Γ
    rw [mem_vdCompatiblePolymerFamilies, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · rintro ⟨h_sub, _⟩
      rw [h_no, Finset.subset_empty] at h_sub
      exact h_sub
    · intro h_eq
      refine ⟨?_, ?_⟩
      · rw [h_eq, h_no]
      · rw [h_eq]
        exact IsCompatiblePolymerFamilyVertexDisjoint.empty G
  have h_lhs : polymerFreeEnergy G t = 0 := by
    unfold polymerFreeEnergy
    rw [h_vd, Finset.sum_singleton, Finset.prod_empty, Real.log_one]
  have h_rhs : mayerPartialSum G N t = 0 := by
    unfold mayerPartialSum
    refine Finset.sum_eq_zero (fun n _ => ?_)
    rcases n with _ | k
    · exact mayerExpansionTerm_zero G t
    · unfold mayerExpansionTerm
      refine Finset.sum_eq_zero (fun ω hω => ?_)
      rw [Fintype.mem_piFinset] at hω
      have h0 : ω 0 ∈ allPolymers G := hω 0
      rw [h_no] at h0
      exact absurd h0 (Finset.notMem_empty _)
  rw [h_lhs, h_rhs]

/-- **Mayer identity tanh form for empty-polymer graphs** (Step 619):
restate Step 618 in `tanh(β·J)` form. -/
theorem mayer_identity_of_no_polymers_tanh
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h_no : allPolymers G = ∅) (β J : ℝ) (N : ℕ) :
    polymerFreeEnergy G (Real.tanh (β * J)) =
      mayerPartialSum G N (Real.tanh (β * J)) :=
  mayer_identity_of_no_polymers G h_no _ N

/-- **`allPolymers G = ∅` when `G` has no edges** (Step 620): an
edgeless graph has no even subgraph other than `∅`, which is excluded
from `IsPolymer` by the non-emptiness clause. -/
theorem allPolymers_eq_empty_of_edgeFinset_empty
    {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h_empty : G.edgeFinset = ∅) :
    allPolymers G = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro P hP
  rw [mem_allPolymers] at hP
  -- IsPolymer G P ⇒ P ⊆ G.edgeFinset (= ∅) and P.Nonempty
  obtain ⟨e, heP⟩ := hP.nonempty
  have h_e : e ∈ G.edgeFinset := hP.isEven.subset heP
  rw [h_empty] at h_e
  exact absurd h_e (Finset.notMem_empty _)

/-- **Mayer identity for edgeless graphs** (Step 620): when
`G.edgeFinset = ∅`, the Mayer identity `polymerFreeEnergy G t =
mayerPartialSum G N t` holds for every `t` and `N`. Combines
Step 620's `allPolymers = ∅` with Step 618. -/
theorem mayer_identity_of_edgeFinset_empty
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h_empty : G.edgeFinset = ∅) (t : ℝ) (N : ℕ) :
    polymerFreeEnergy G t = mayerPartialSum G N t :=
  mayer_identity_of_no_polymers G
    (allPolymers_eq_empty_of_edgeFinset_empty G h_empty) t N

/-- **`polymerFreeEnergy = 0` for empty-polymer graphs** (Step 621):
when `allPolymers G = ∅`, `polymerFreeEnergy G t = 0` for every `t`,
since `vdCompatiblePolymerFamilies G = {∅}` and `log 1 = 0`. -/
theorem polymerFreeEnergy_eq_zero_of_no_polymers
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h_no : allPolymers G = ∅) (t : ℝ) :
    polymerFreeEnergy G t = 0 := by
  rw [mayer_identity_of_no_polymers G h_no t 0, mayerPartialSum_zero]

/-- **`mayerPartialSum = 0` for empty-polymer graphs** (Step 621):
when `allPolymers G = ∅`, every Mayer term vanishes (no polymer
sequences exist for `n ≥ 1`; n=0 vanishes via Step 587). -/
theorem mayerPartialSum_eq_zero_of_no_polymers
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h_no : allPolymers G = ∅) (t : ℝ) (N : ℕ) :
    mayerPartialSum G N t = 0 := by
  rw [← mayer_identity_of_no_polymers G h_no t N,
      polymerFreeEnergy_eq_zero_of_no_polymers G h_no t]

/-- **Edgeless-graph Mayer identity in tanh form** (Step 622): lift
Step 620 to the `tanh(β·J)` argument. -/
theorem mayer_identity_of_edgeFinset_empty_tanh
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h_empty : G.edgeFinset = ∅) (β J : ℝ) (N : ℕ) :
    polymerFreeEnergy G (Real.tanh (β * J)) =
      mayerPartialSum G N (Real.tanh (β * J)) :=
  mayer_identity_of_edgeFinset_empty G h_empty _ N

/-- **`polymerFreeEnergy = 0` for edgeless graphs** (Step 623). -/
theorem polymerFreeEnergy_eq_zero_of_edgeFinset_empty
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h_empty : G.edgeFinset = ∅) (t : ℝ) :
    polymerFreeEnergy G t = 0 :=
  polymerFreeEnergy_eq_zero_of_no_polymers G
    (allPolymers_eq_empty_of_edgeFinset_empty G h_empty) t

/-- **`mayerPartialSum = 0` for edgeless graphs** (Step 623). -/
theorem mayerPartialSum_eq_zero_of_edgeFinset_empty
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h_empty : G.edgeFinset = ∅) (t : ℝ) (N : ℕ) :
    mayerPartialSum G N t = 0 :=
  mayerPartialSum_eq_zero_of_no_polymers G
    (allPolymers_eq_empty_of_edgeFinset_empty G h_empty) t N

/-- **`polymerFreeEnergy` DifferentiableOn `[0, ∞)`** (Step 626):
lift Step 610's per-point AnalyticAt to DifferentiableOn over the
half-line. -/
theorem polymerFreeEnergy_differentiableOn_Ici_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    DifferentiableOn ℝ (fun s : ℝ => polymerFreeEnergy G s) (Set.Ici 0) :=
  fun _ ht =>
    ((polymerFreeEnergy_analyticAt G ht).differentiableAt).differentiableWithinAt

/-- **`polymerFreeEnergy` ContinuousOn `[0, ∞)`** (Step 627). -/
theorem polymerFreeEnergy_continuousOn_Ici_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    ContinuousOn (fun s : ℝ => polymerFreeEnergy G s) (Set.Ici 0) :=
  fun _ ht =>
    ((polymerFreeEnergy_analyticAt G ht).continuousAt).continuousWithinAt

/-- **`mayerPartialSum` ContinuousOn arbitrary set** (Step 628). -/
theorem mayerPartialSum_continuousOn
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (N : ℕ) (s : Set ℝ) :
    ContinuousOn (fun t : ℝ => mayerPartialSum G N t) s :=
  (mayerPartialSum_continuous G N).continuousOn

/-- **`mayerPartialSum` DifferentiableOn arbitrary set** (Step 628). -/
theorem mayerPartialSum_differentiableOn
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (N : ℕ) (s : Set ℝ) :
    DifferentiableOn ℝ (fun t : ℝ => mayerPartialSum G N t) s :=
  (mayerPartialSum_differentiable G N).differentiableOn

/-- **vdPolymerFamilies sum sandwich for `t ≥ 0`** (Step 631):
`1 ≤ vdSum G t ≤ (1+t)^|E|`. Combines Step 605 (≥ 1) with Step 629
(≤ (1+t)^|E|). -/
theorem vdPolymerFamilies_sum_sandwich_of_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    1 ≤ (∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card) ∧
    (∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card) ≤
      (1 + t) ^ G.edgeFinset.card :=
  ⟨vdPolymerFamilies_sum_ge_one_of_nonneg G ht,
   vdPolymerFamilies_sum_le_one_plus_pow_of_nonneg G ht⟩

/-- **`polymerFreeEnergy ≤ |E| · log(1+t)` under `t ≥ 0`** (Step 630):
apply `Real.log_le_log` to Step 629's bound `vdSum ≤ (1+t)^|E|`. The
right-hand side `Real.log ((1+t)^|E|) = |E| · log(1+t)` via `Real.log_pow`. -/
theorem polymerFreeEnergy_le_card_log_one_plus_of_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    polymerFreeEnergy G t ≤ G.edgeFinset.card * Real.log (1 + t) := by
  unfold polymerFreeEnergy
  have h_pos : 0 < ∑ Γ ∈ vdCompatiblePolymerFamilies G,
      ∏ P ∈ Γ, t ^ P.card :=
    vdPolymerFamilies_sum_pos_of_nonneg G ht
  have h_le : (∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card) ≤
      (1 + t) ^ G.edgeFinset.card :=
    vdPolymerFamilies_sum_le_one_plus_pow_of_nonneg G ht
  calc Real.log (∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card)
      ≤ Real.log ((1 + t) ^ G.edgeFinset.card) :=
            Real.log_le_log h_pos h_le
    _ = G.edgeFinset.card * Real.log (1 + t) := by
            rw [Real.log_pow]

/-- **`polymerFreeEnergy ≥ 0` under `t ≥ 0`** (Step 631): direct
consequence of Step 605 (`vdSum ≥ 1`) and `Real.log_nonneg`. -/
theorem polymerFreeEnergy_nonneg_of_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ polymerFreeEnergy G t :=
  Real.log_nonneg (vdPolymerFamilies_sum_ge_one_of_nonneg G ht)

/-- **`polymerFreeEnergy` sandwich for `t ≥ 0`** (Step 631):
`0 ≤ polymerFreeEnergy G t ≤ |E| · log(1 + t)`. -/
theorem polymerFreeEnergy_sandwich_of_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ polymerFreeEnergy G t ∧
    polymerFreeEnergy G t ≤ G.edgeFinset.card * Real.log (1 + t) :=
  ⟨polymerFreeEnergy_nonneg_of_nonneg G ht,
   polymerFreeEnergy_le_card_log_one_plus_of_nonneg G ht⟩

/-- **`polymerFreeEnergy` sandwich at `tanh(β·J)`** (Step 632): tanh-form
restatement of Step 631. Under `0 ≤ β·J`, `0 ≤ Real.tanh (β·J)`, so
the sandwich applies. -/
theorem polymerFreeEnergy_tanh_sandwich
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] {β J : ℝ} (hβJ : 0 ≤ β * J) :
    0 ≤ polymerFreeEnergy G (Real.tanh (β * J)) ∧
    polymerFreeEnergy G (Real.tanh (β * J)) ≤
      G.edgeFinset.card * Real.log (1 + Real.tanh (β * J)) :=
  polymerFreeEnergy_sandwich_of_nonneg G (real_tanh_nonneg hβJ)

/-- **`vdPolymerFamilies_sum` is monotone on `[0, ∞)`** (Step 633):
each term `t^|X|` is monotone in `t` for `t ≥ 0`, so the sum is too. -/
theorem vdPolymerFamilies_sum_monotoneOn_Ici_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    MonotoneOn (fun t : ℝ =>
      ∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card) (Set.Ici 0) := by
  intro t ht s hs hts
  refine Finset.sum_le_sum (fun Γ _ => ?_)
  refine Finset.prod_le_prod (fun P _ => pow_nonneg ht _) (fun P _ => ?_)
  exact pow_le_pow_left₀ ht hts _

/-- **`polymerFreeEnergy` is monotone on `[0, ∞)`** (Step 633): apply
`Real.log_le_log` to `vdSum` monotonicity. -/
theorem polymerFreeEnergy_monotoneOn_Ici_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    MonotoneOn (fun t : ℝ => polymerFreeEnergy G t) (Set.Ici 0) := by
  intro t ht s hs hts
  unfold polymerFreeEnergy
  exact Real.log_le_log (vdPolymerFamilies_sum_pos_of_nonneg G ht)
    (vdPolymerFamilies_sum_monotoneOn_Ici_zero G ht hs hts)

/-- **`polymerFreeEnergy` preserves order on `[0, ∞)`** (Step 649):
direct order-preservation corollary of Step 633 (monotonicity). -/
theorem polymerFreeEnergy_le_of_le_of_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hts : t ≤ s) :
    polymerFreeEnergy G t ≤ polymerFreeEnergy G s :=
  polymerFreeEnergy_monotoneOn_Ici_zero G ht hs hts

/-- **`polymerFreeEnergy ≤ |E| · t` under `t ≥ 0`** (Step 634):
sharpen Step 630 via `Real.log_le_sub_one_of_pos` (i.e. `log(1+t) ≤ t`). -/
theorem polymerFreeEnergy_le_card_mul_of_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    polymerFreeEnergy G t ≤ G.edgeFinset.card * t := by
  refine (polymerFreeEnergy_le_card_log_one_plus_of_nonneg G ht).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  have h_pos : (0 : ℝ) < 1 + t := by linarith
  have := Real.log_le_sub_one_of_pos h_pos
  linarith

/-- **`polymerFreeEnergy ≤ |E|·tanh(β·J)` under `0 ≤ β·J`** (Step 635):
tanh form of Step 634. -/
theorem polymerFreeEnergy_tanh_le_card_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] {β J : ℝ} (hβJ : 0 ≤ β * J) :
    polymerFreeEnergy G (Real.tanh (β * J)) ≤
      G.edgeFinset.card * Real.tanh (β * J) :=
  polymerFreeEnergy_le_card_mul_of_nonneg G (real_tanh_nonneg hβJ)

/-- **Ferromagnetic `polymerFreeEnergy_tanh_sandwich`** (Step 636):
under `0 ≤ J, 0 < β`. -/
theorem polymerFreeEnergy_tanh_sandwich_ferromagnetic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] {β J : ℝ}
    (hJ : 0 ≤ J) (hβ : 0 < β) :
    0 ≤ polymerFreeEnergy G (Real.tanh (β * J)) ∧
    polymerFreeEnergy G (Real.tanh (β * J)) ≤
      G.edgeFinset.card * Real.log (1 + Real.tanh (β * J)) :=
  polymerFreeEnergy_tanh_sandwich G (mul_nonneg hβ.le hJ)

/-- **Ferromagnetic `polymerFreeEnergy_tanh_le_card_mul`** (Step 636). -/
theorem polymerFreeEnergy_tanh_le_card_mul_ferromagnetic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] {β J : ℝ}
    (hJ : 0 ≤ J) (hβ : 0 < β) :
    polymerFreeEnergy G (Real.tanh (β * J)) ≤
      G.edgeFinset.card * Real.tanh (β * J) :=
  polymerFreeEnergy_tanh_le_card_mul G (mul_nonneg hβ.le hJ)

/-- **`mayerExpansionTerm G 1 t ≥ 0` under `t ≥ 0`** (Step 637):
the n=1 Mayer term equals `∑_P t^|P|`, all non-negative. -/
theorem mayerExpansionTerm_one_nonneg_of_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ mayerExpansionTerm G 1 t := by
  rw [mayerExpansionTerm_one]
  exact Finset.sum_nonneg (fun P _ => pow_nonneg ht _)

/-- **`vdPolymerFamilies_sum` at `t = 1`** (Step 639): every product
`∏ 1^|P| = 1`, so the sum collapses to the cardinality of
`vdCompatiblePolymerFamilies G`. -/
theorem vdPolymerFamilies_sum_at_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    (∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, (1 : ℝ) ^ P.card) =
      (vdCompatiblePolymerFamilies G).card := by
  classical
  have h_each : ∀ Γ ∈ vdCompatiblePolymerFamilies G,
      (∏ P ∈ Γ, (1 : ℝ) ^ P.card) = 1 := by
    intro Γ _
    refine Finset.prod_eq_one (fun P _ => ?_)
    exact one_pow _
  rw [Finset.sum_congr rfl h_each, Finset.sum_const, Nat.smul_one_eq_cast]

/-- **`polymerFreeEnergy` at `t = 1`** (Step 640): equals
`log |vdCompatiblePolymerFamilies G|`. Direct via Step 639. -/
theorem polymerFreeEnergy_at_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    polymerFreeEnergy G 1 =
      Real.log (vdCompatiblePolymerFamilies G).card := by
  unfold polymerFreeEnergy
  rw [vdPolymerFamilies_sum_at_one]

/-- **`mayerPartialSum G 1 t = |allPolymers G|` at `t = 1`** (Step 641):
each polymer contributes `1^|P| = 1`, so the sum equals the number of
polymers. -/
theorem mayerPartialSum_one_at_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    mayerPartialSum G 1 1 = (allPolymers G).card := by
  classical
  rw [mayerPartialSum_one]
  have h_each : ∀ P ∈ allPolymers G, (1 : ℝ) ^ P.card = 1 := fun _ _ => one_pow _
  rw [Finset.sum_congr rfl h_each, Finset.sum_const, Nat.smul_one_eq_cast]

/-- **`polymerFreeEnergy ≤ |E| · log 2` for `0 ≤ t ≤ 1`** (Step 642):
under `t ≤ 1`, `log(1+t) ≤ log 2`. -/
theorem polymerFreeEnergy_le_card_log_two_of_le_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    polymerFreeEnergy G t ≤ G.edgeFinset.card * Real.log 2 := by
  refine (polymerFreeEnergy_le_card_log_one_plus_of_nonneg G ht).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  exact Real.log_le_log (by linarith) (by linarith)

/-- **`polymerFreeEnergy_tanh ≤ |E| · log 2` under `0 ≤ β·J`** (Step 643):
since `tanh(β·J) < 1` always, Step 642 applies. -/
theorem polymerFreeEnergy_tanh_le_card_log_two
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] {β J : ℝ} (hβJ : 0 ≤ β * J) :
    polymerFreeEnergy G (Real.tanh (β * J)) ≤
      G.edgeFinset.card * Real.log 2 :=
  polymerFreeEnergy_le_card_log_two_of_le_one G (real_tanh_nonneg hβJ)
    (Real.tanh_lt_one _).le

/-- **Ferromagnetic `polymerFreeEnergy_tanh ≤ |E| · log 2`** (Step 644). -/
theorem polymerFreeEnergy_tanh_le_card_log_two_ferromagnetic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] {β J : ℝ}
    (hJ : 0 ≤ J) (hβ : 0 < β) :
    polymerFreeEnergy G (Real.tanh (β * J)) ≤
      G.edgeFinset.card * Real.log 2 :=
  polymerFreeEnergy_tanh_le_card_log_two G (mul_nonneg hβ.le hJ)

/-- **`polymerFreeEnergy_tanh` double bound** (Step 645): under
`0 ≤ β·J`, both `polymerFreeEnergy_tanh ≤ |E|·tanh(β·J)` (Step 635)
and `≤ |E|·log 2` (Step 643) hold simultaneously. -/
theorem polymerFreeEnergy_tanh_double_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] {β J : ℝ} (hβJ : 0 ≤ β * J) :
    polymerFreeEnergy G (Real.tanh (β * J)) ≤
      G.edgeFinset.card * Real.tanh (β * J) ∧
    polymerFreeEnergy G (Real.tanh (β * J)) ≤
      G.edgeFinset.card * Real.log 2 :=
  ⟨polymerFreeEnergy_tanh_le_card_mul G hβJ,
   polymerFreeEnergy_tanh_le_card_log_two G hβJ⟩

/-- **`mayerPartialSum` recurrence in `N`** (Step 638):
`mayerPartialSum G (N+1) t = mayerPartialSum G N t + mayerExpansionTerm G (N+1) t`. -/
theorem mayerPartialSum_succ
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (N : ℕ) (t : ℝ) :
    mayerPartialSum G (N + 1) t =
      mayerPartialSum G N t + mayerExpansionTerm G (N + 1) t := by
  unfold mayerPartialSum
  rw [show ((N + 1) + 1) = (N + 1) + 1 from rfl, Finset.sum_range_succ]

/-- **`mayerExpansionTerm = mayerPartialSum` diff** (Step 646):
rearrangement of Step 638. -/
theorem mayerExpansionTerm_eq_mayerPartialSum_diff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (N : ℕ) (t : ℝ) :
    mayerExpansionTerm G (N + 1) t =
      mayerPartialSum G (N + 1) t - mayerPartialSum G N t := by
  rw [mayerPartialSum_succ]
  ring

/-- **`mayerExpansionTerm G 2 t ≤ 0` under `t ≥ 0`** (Step 637):
the n=2 Mayer term equals `-1/2 · ∑_{(P,Q) incompat} t^|P|·t^|Q|`,
non-positive. Matches the alternating sign of log(1+x) Taylor
coefficients. -/
theorem mayerExpansionTerm_two_nonpos_of_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    mayerExpansionTerm G 2 t ≤ 0 := by
  rw [mayerExpansionTerm_two_filter]
  refine mul_nonpos_of_nonpos_of_nonneg (by norm_num) ?_
  refine Finset.sum_nonneg (fun pq _ => ?_)
  exact mul_nonneg (pow_nonneg ht _) (pow_nonneg ht _)

/-- **`polymerFreeEnergy` HasDerivAt** (Step 625): explicit derivative
of `polymerFreeEnergy G t = Real.log (vdPolymerFamilies_sum G t)` via
the log-derivative formula `(log f)' = f' / f`. The derivative of
`vdPolymerFamilies_sum G` is given by Step 575 (explicit polynomial
form), and positivity (Step 605) ensures `f t ≠ 0`. -/
theorem polymerFreeEnergy_hasDerivAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s : ℝ => polymerFreeEnergy G s)
      ((∑ Γ ∈ vdCompatiblePolymerFamilies G,
          ∑ Q ∈ Γ, (∏ P ∈ Γ.erase Q, t ^ P.card) *
            ((Q.card : ℝ) * t ^ (Q.card - 1))) /
        (∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card)) t := by
  unfold polymerFreeEnergy
  exact (vdPolymerFamilies_sum_hasDerivAt G t).log
    (vdPolymerFamilies_sum_pos_of_nonneg G ht).ne'

/-- **`freeEnergy = log 2` at `β·J = 0`** (Step 624): when `β·J = 0`,
the Step 612 decomposition reduces to `f = log 2` since
`cosh(0) = 1`, `log 1 = 0`, and `polymerFreeEnergy G (tanh 0) = 0`
(Step 600). Recovers the well-known free-energy value at trivial
slices. -/
theorem freeEnergy_eq_log_two_at_betaJ_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβJ : β * J = 0) (hne : 0 < Fintype.card ι) :
    freeEnergy G ⟨J, 0, β⟩ = Real.log 2 := by
  rw [freeEnergy_eq_polymerFreeEnergy G J β (hβJ.symm ▸ le_refl 0) hne, hβJ,
      Real.cosh_zero, Real.log_one, Real.tanh_zero,
      polymerFreeEnergy_at_zero, mul_zero, zero_div, add_zero, add_zero]

end IsingModel

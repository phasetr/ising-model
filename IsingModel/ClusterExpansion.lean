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

end IsingModel

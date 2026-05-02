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

/-- **Edge-connectedness of an edge subset**: any two edges in `X` are
connected by a chain of edge-adjacency steps within `X`. The empty set
is vacuously edge-connected, and a single edge is also trivially
edge-connected (the reflexive case). -/
def IsEdgeConnected {ι : Type*} (X : Finset (Sym2 ι)) : Prop :=
  ∀ e₁ ∈ X, ∀ e₂ ∈ X,
    Relation.ReflTransGen (edgeAdjacentIn X) e₁ e₂

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

/-- **Polymer activity is `1` on the empty edge set** (since `t^0 = 1`). -/
@[simp]
theorem polymerActivity_empty (t : ℝ) :
    polymerActivity t (∅ : Finset (Sym2 ι)) = 1 := by
  unfold polymerActivity
  simp

end IsingModel

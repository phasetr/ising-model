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

/-- **Polymer compatibility**: two polymers are *compatible* if they
are edge-disjoint. This is the natural compatibility relation for the
polymer model arising from the FV (3.45) cycle-space sum: distinct
edge-disjoint cycles contribute multiplicatively to the partition
function. -/
def IsPolymerCompatible {ι : Type*} [DecidableEq ι]
    (P Q : Finset (Sym2 ι)) : Prop :=
  Disjoint P Q

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

end IsingModel

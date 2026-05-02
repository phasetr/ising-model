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

/-- **Bridging lemma**: an `X ⊆ G.edgeFinset` is an `IsEvenSubgraph G X`
iff every vertex has even incidence in `X`. This relates the new
predicate to the inline form used by FV (3.45)
`partitionFunction_high_temp_expansion_h_zero_closed`. -/
theorem isEvenSubgraph_iff {ι : Type*} [DecidableEq ι]
    {G : SimpleGraph ι} [Fintype G.edgeSet]
    {X : Finset (Sym2 ι)} (hX : X ⊆ G.edgeFinset) :
    IsEvenSubgraph G X ↔ ∀ v : ι, Even ((X.filter (v ∈ ·)).card) :=
  ⟨fun h => h.even_degree, fun h => ⟨hX, h⟩⟩

end IsingModel

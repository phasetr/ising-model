import IsingModel.ClusterExpansion.Families.CompatibleProperties

/-!
# Cluster polymer families split — even subgraphs, all polymers, and polymer decomposition

Part of the split cluster-expansion families layer (Issue #1850).
-/

namespace IsingModel

open Finset

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


end IsingModel

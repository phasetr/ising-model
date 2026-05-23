import IsingModel.ClusterExpansion.Incompatibility
import IsingModel.Conditioning.HighTempClosed

/-!
# Cluster polymer families split — cluster polymer set and compatible family predicates

Part of the split cluster-expansion families layer (Issue #1850).
-/

namespace IsingModel

open Finset

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


end IsingModel

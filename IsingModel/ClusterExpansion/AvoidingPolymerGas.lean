import IsingModel.ClusterExpansion.TwoPointNumeratorEquality
import IsingModel.ClusterExpansion.Families.VertexDisjoint

/-!
# Avoiding polymer gas identities

This file rewrites the even-subgraph sum avoiding a fixed support as the vertex-disjoint polymer
family sum over polymers that avoid the same support, with complex activity.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Generic weight multiplicativity over a vertex-disjoint family**: for any commutative monoid
activity `z`, the power of the cardinality of the biUnion is the product of the powers of the
cardinalities of the polymers. -/
theorem IsCompatiblePolymerFamilyVertexDisjoint.prod_pow_card_biUnion
    {M : Type*} [CommMonoid M]
    {G : SimpleGraph ι} [Fintype G.edgeSet]
    (z : M) {Γ : Finset (Finset (Sym2 ι))}
    (hΓ : IsCompatiblePolymerFamilyVertexDisjoint G Γ) :
    z ^ (Γ.biUnion id).card = ∏ P ∈ Γ, z ^ P.card := by
  rw [hΓ.card_biUnion, ← Finset.prod_pow_eq_pow_sum]

/-- Vertex-disjoint compatible polymer families all of whose polymers avoid the support of `C`. -/
noncomputable def vdCompatiblePolymerFamiliesAvoiding
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (C : Finset (Sym2 ι)) : Finset (Finset (Finset (Sym2 ι))) := by
  classical
  exact (vdCompatiblePolymerFamilies G).filter
    (fun Γ => ∀ P ∈ Γ, IsPolymerVertexDisjoint C P)

/-- Membership characterization for vertex-disjoint compatible polymer families avoiding `C`. -/
theorem mem_vdCompatiblePolymerFamiliesAvoiding
    {G : SimpleGraph ι} [Fintype G.edgeSet]
    {C : Finset (Sym2 ι)} {Γ : Finset (Finset (Sym2 ι))} :
    Γ ∈ vdCompatiblePolymerFamiliesAvoiding G C ↔
      Γ ∈ vdCompatiblePolymerFamilies G ∧
        ∀ P ∈ Γ, IsPolymerVertexDisjoint C P := by
  classical
  unfold vdCompatiblePolymerFamiliesAvoiding
  rw [Finset.mem_filter]

/-- A biUnion avoids `C` exactly when each polymer in the family avoids `C`. -/
theorem vertexDisjoint_biUnion_iff
    {C : Finset (Sym2 ι)} {Γ : Finset (Finset (Sym2 ι))} :
    IsPolymerVertexDisjoint C (Γ.biUnion id) ↔
      ∀ P ∈ Γ, IsPolymerVertexDisjoint C P := by
  unfold IsPolymerVertexDisjoint
  rw [polymerSupport_biUnion, Finset.disjoint_biUnion_right]

/-- **Avoiding even-subgraph sum equals the avoiding vertex-disjoint polymer-family sum**: the
complex high-temperature even-subgraph sum over subgraphs vertex-disjoint from `C` is the polymer
gas sum over vertex-disjoint compatible families whose every polymer avoids `C`. -/
theorem htSubgraphSumAvoiding_eq_vdCompatiblePolymerFamiliesAvoiding_sum
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (C : Finset (Sym2 ι)) (z : ℂ) :
    htSubgraphSumAvoiding G C z =
      ∑ Γ ∈ vdCompatiblePolymerFamiliesAvoiding G C, ∏ P ∈ Γ, z ^ P.card := by
  classical
  unfold htSubgraphSumAvoiding evenSubgraphsAvoiding vdCompatiblePolymerFamiliesAvoiding
  apply Finset.sum_bij
    (fun Y (_ : Y ∈ (evenSubgraphs G).filter (fun Y => IsPolymerVertexDisjoint C Y)) =>
      polymerDecomposition Y)
  · intro Y hY
    rw [Finset.mem_filter] at hY ⊢
    have hY_even : IsEvenSubgraph G Y := mem_evenSubgraphs.mp hY.1
    refine ⟨hY_even.polymerDecomposition_mem_vdCompatiblePolymerFamilies, ?_⟩
    have h_avoid_biUnion :
        IsPolymerVertexDisjoint C ((polymerDecomposition Y).biUnion id) := by
      simpa [polymerDecomposition_biUnion_id Y] using hY.2
    exact (vertexDisjoint_biUnion_iff (C := C) (Γ := polymerDecomposition Y)).mp
      h_avoid_biUnion
  · intro Y _ Y' _ h_eq
    have h₁ : (polymerDecomposition Y).biUnion id = Y :=
      polymerDecomposition_biUnion_id Y
    have h₂ : (polymerDecomposition Y').biUnion id = Y' :=
      polymerDecomposition_biUnion_id Y'
    rw [← h₁, ← h₂, h_eq]
  · intro Γ hΓ
    rw [Finset.mem_filter] at hΓ
    have hΓ_vd : IsCompatiblePolymerFamilyVertexDisjoint G Γ :=
      (mem_vdCompatiblePolymerFamilies.mp hΓ.1).2
    refine ⟨Γ.biUnion id, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [mem_evenSubgraphs]
        exact hΓ_vd.biUnion_isEvenSubgraph
      · exact (vertexDisjoint_biUnion_iff (C := C) (Γ := Γ)).mpr hΓ.2
    · exact hΓ_vd.polymerDecomposition_biUnion
  · intro Y hY
    rw [Finset.mem_filter] at hY
    have hY_even : IsEvenSubgraph G Y := mem_evenSubgraphs.mp hY.1
    have h_biU : (polymerDecomposition Y).biUnion id = Y :=
      polymerDecomposition_biUnion_id Y
    have h_pow :=
      hY_even.polymerDecomposition_isCompatibleVertexDisjoint.prod_pow_card_biUnion z
    rw [h_biU] at h_pow
    exact h_pow

end IsingModel

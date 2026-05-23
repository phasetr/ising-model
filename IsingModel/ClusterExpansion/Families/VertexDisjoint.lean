import IsingModel.ClusterExpansion.Families.EvenSubgraphs

/-!
# Cluster polymer families split — vertex-disjoint compatible polymer families

Part of the split cluster-expansion families layer (Issue #1850).
-/

namespace IsingModel

open Finset

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


end IsingModel

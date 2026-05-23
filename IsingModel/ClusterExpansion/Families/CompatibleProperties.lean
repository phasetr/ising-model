import IsingModel.ClusterExpansion.Families.Predicates

/-!
# Cluster polymer families split — compatible family decomposition and cardinality properties

Part of the split cluster-expansion families layer (Issue #1850).
-/

namespace IsingModel

open Finset

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


end IsingModel

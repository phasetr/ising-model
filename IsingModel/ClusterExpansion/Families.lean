import IsingModel.ClusterExpansion.Incompatibility

/-!
# Cluster expansion compatible families and polymer sums

Mechanical child split from `ClusterExpansion.lean`.
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

/-- **VD polymer-family sum sandwich (ferromagnetic)**: under
`0 ≤ J, 0 < β`, the same `1 ≤ ∑_Γ ∏ tanh(β·J)^|P| ≤ 2^|E|`. -/
theorem vdPolymerFamilies_sum_sandwich_ferromagnetic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) :
    1 ≤ (∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) ∧
    (∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (2 : ℝ) ^ G.edgeFinset.card :=
  vdPolymerFamilies_sum_sandwich G (mul_nonneg hβ.le hJ)

/-- **VD polymer-family sum sharp sandwich (ferromagnetic)**: under
`0 ≤ J, 0 < β`, the same `1 ≤ ∑_Γ ∏ tanh(β·J)^|P| ≤
(1+tanh(β·J))^|E|`. -/
theorem vdPolymerFamilies_sum_sandwich_sharp_ferromagnetic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) :
    1 ≤ (∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) ∧
    (∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (1 + Real.tanh (β * J)) ^ G.edgeFinset.card :=
  vdPolymerFamilies_sum_sandwich_sharp G (mul_nonneg hβ.le hJ)

/-- **Polymer activity for the lattice Ising model**: the natural
weight `t^|P|` arising from the FV (3.45) closed form
`Z = 2^|ι|·cosh^|E|·∑_{X ⊆ E, even} tanh(β·J)^|X|`.

Set `t = tanh(β·J)` to recover the FV (3.45) summand. -/
def polymerActivity (t : ℝ) (P : Finset (Sym2 ι)) : ℝ := t ^ P.card

end IsingModel

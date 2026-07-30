import IsingModel.ClusterExpansion.Families.VertexDisjoint

/-!
# Field-dependent connected polymers and the polymer factorization identity

Brick 2a of the on-book programme toward Glimm–Jaffe (GJ) Theorem 17.6.1
(`∂/∂h` infinite-volume differentiability / `h`-analyticity of the two-point
function in the high-temperature window). The first brick
`partitionFunction_high_temp_expansion_field_closed`
(`Conditioning/HighTempClosed/ClosedFormField.lean`) writes the finite-volume
partition function as
`Z = 2^|ι|·cosh(βJ)^|E|·cosh(βh)^|ι| · ∑_{X ⊆ E} tanh(βJ)^|X|·tanh(βh)^{#odd(X)}`,
where `#odd(X) = |{v : Odd (deg_X v)}|`. Brick 2a factorizes the edge-subset sum
over the edge-connected components (polymers) of `X`, exhibiting `Z/prefactor`
as a hard-core (vertex-disjoint) polymer gas with the field-dependent activity
`w(P) = tanh(βJ)^|P|·tanh(βh)^{#odd(P)}`.

This is the field-dependent generalization of the already-proved `h = 0`
identity `evenSubgraphs_sum_eq_vdPolymerFamilies_sum`
(`Families/VertexDisjoint.lean`): the even-degree restriction is dropped, the
sum runs over *all* edge subsets, and the `tanh(βh)^{#odd}` factor replaces the
even-subgraph indicator. It is a pure finite combinatorial identity carrying no
convergence content (Kotecky–Preiss / activity bounds are brick 2b onward).

References: Friedli–Velenik §3.7.3, eq. (3.45), p. 117, and §5.7.3 give the
zero-field templates; §5.2 gives the abstract polymer model. Exercise 5.8,
p. 238, with its solution in Appendix C, p. 531, gives the exact magnetic-field
weight. The connected-family factorization used here is a project extension.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Connected polymer**: a non-empty, edge-connected subset of `G.edgeFinset`.
This is exactly `IsPolymer` with the even-degree clause dropped; in the
field-dependent cluster expansion the polymers arising from the connected-
component decomposition of an edge subset need not be even. -/
structure IsConnectedPolymer {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (P : Finset (Sym2 ι)) : Prop where
  /-- `P` is non-empty. -/
  nonempty : P.Nonempty
  /-- `P` is contained in the edge set of `G`. -/
  subset : P ⊆ G.edgeFinset
  /-- `P` is edge-connected. -/
  connected : IsEdgeConnected P

/-- **`edgeComponent` of an edge subset is a connected polymer**: for
`X ⊆ G.edgeFinset` and `e ∈ X`, the edge-connected component `edgeComponent X e`
is non-empty (contains `e`), contained in `G.edgeFinset`, and edge-connected.
The field-dependent analogue of `IsEvenSubgraph.edgeComponent_isPolymer`, with
no even-degree hypothesis. -/
theorem edgeComponent_isConnectedPolymer {ι : Type*} [DecidableEq ι]
    {G : SimpleGraph ι} [Fintype G.edgeSet]
    {X : Finset (Sym2 ι)} (hX : X ⊆ G.edgeFinset)
    {e : Sym2 ι} (he : e ∈ X) :
    IsConnectedPolymer G (edgeComponent X e) where
  nonempty := ⟨e, self_mem_edgeComponent he⟩
  subset := (edgeComponent_subset X e).trans hX
  connected := isEdgeConnected_edgeComponent e

/-- **Field-dependent polymer activity** `w_{a,b}(P) = tanh(a)^|P|·
tanh(b)^{#odd(P)}`, where `#odd(P) = |{v : Odd (deg_P v)}|` counts the vertices
of odd `P`-degree. Applied with `a = βJ`, `b = βh`, this is the polymer weight
of the field-dependent cluster gas. At `b = 0` it reduces to `tanh(a)^|P|` on
even polymers (and vanishes on polymers with an odd vertex). -/
noncomputable def fieldPolymerWeight (a b : ℝ) (P : Finset (Sym2 ι)) : ℝ :=
  Real.tanh a ^ P.card *
    Real.tanh b ^
      (Finset.univ.filter (fun v => Odd ((P.filter (v ∈ ·)).card))).card

/-- **All connected polymers of `G`**: the reference universe of connected
polymers, defined as the filter of `IsConnectedPolymer G` in
`G.edgeFinset.powerset`. Field-dependent analogue of `allPolymers`. -/
noncomputable def allConnectedPolymers {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    Finset (Finset (Sym2 ι)) := by
  classical
  exact G.edgeFinset.powerset.filter (fun P => IsConnectedPolymer G P)

/-- **Membership in `allConnectedPolymers`**: `P ∈ allConnectedPolymers G ↔
IsConnectedPolymer G P` (the subset clause is already part of the predicate). -/
theorem mem_allConnectedPolymers {ι : Type*} [DecidableEq ι]
    {G : SimpleGraph ι} [Fintype G.edgeSet]
    {P : Finset (Sym2 ι)} :
    P ∈ allConnectedPolymers G ↔ IsConnectedPolymer G P := by
  classical
  unfold allConnectedPolymers
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨h.subset, h⟩⟩

/-- **Vertex-disjoint connected polymer families of `G`**: sub-families of
`allConnectedPolymers G` whose members are pairwise vertex-disjoint. This is
the index set of the field-dependent hard-core polymer gas, mirroring
`vdCompatiblePolymerFamilies` with `IsPolymer ⤳ IsConnectedPolymer`. -/
noncomputable def vdConnectedPolymerFamilies {ι : Type*} [Fintype ι]
    [DecidableEq ι] (G : SimpleGraph ι) [Fintype G.edgeSet] :
    Finset (Finset (Finset (Sym2 ι))) := by
  classical
  exact (allConnectedPolymers G).powerset.filter
    (fun Γ => (↑Γ : Set (Finset (Sym2 ι))).Pairwise IsPolymerVertexDisjoint)

/-- **Membership in `vdConnectedPolymerFamilies`**:
`Γ ∈ vdConnectedPolymerFamilies G ↔ Γ ⊆ allConnectedPolymers G ∧
(↑Γ).Pairwise IsPolymerVertexDisjoint`. -/
theorem mem_vdConnectedPolymerFamilies {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : SimpleGraph ι} [Fintype G.edgeSet]
    {Γ : Finset (Finset (Sym2 ι))} :
    Γ ∈ vdConnectedPolymerFamilies G ↔
      Γ ⊆ allConnectedPolymers G ∧
        (↑Γ : Set (Finset (Sym2 ι))).Pairwise IsPolymerVertexDisjoint := by
  classical
  unfold vdConnectedPolymerFamilies
  rw [Finset.mem_filter, Finset.mem_powerset]

/-- **Odd-degree vertex-count additivity over a vertex-disjoint family**: for a
pairwise vertex-disjoint family `Γ` with `X = Γ.biUnion id`, the number of
odd-degree vertices of `X` equals the sum over `P ∈ Γ` of the odd-degree
vertex counts of `P`. This is the one genuinely new combinatorial step of
brick 2a; its proof mirrors `support_card_biUnion`. Numerically: two disjoint
edges give `4 = 2 + 2`, a triangle gives `0`, a two-edge path gives `2`, and
the empty family gives `0`. -/
theorem oddCard_biUnion_of_vd {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Γ : Finset (Finset (Sym2 ι))}
    (hpair : (↑Γ : Set (Finset (Sym2 ι))).Pairwise IsPolymerVertexDisjoint) :
    (Finset.univ.filter
        (fun v => Odd (((Γ.biUnion id).filter (v ∈ ·)).card))).card =
      ∑ P ∈ Γ, (Finset.univ.filter
        (fun v => Odd ((P.filter (v ∈ ·)).card))).card := by
  classical
  -- `Odd n → n ≠ 0`.
  have odd_ne : ∀ n : ℕ, Odd n → n ≠ 0 := by
    rintro n hn rfl
    exact (by decide : ¬ Odd 0) hn
  -- A vertex of positive degree in `R` lies in `polymerSupport R`.
  have hvsupp : ∀ (R : Finset (Sym2 ι)) (v : ι),
      (R.filter (v ∈ ·)).Nonempty → v ∈ polymerSupport R := by
    rintro R v ⟨e, he⟩
    rw [Finset.mem_filter] at he
    exact mem_polymerSupport.mpr ⟨e, he.1, he.2⟩
  -- The `X`-degree of a vertex is the sum of its degrees inside each member.
  have hdeg : ∀ v : ι,
      ((Γ.biUnion id).filter (v ∈ ·)).card =
        ∑ P ∈ Γ, (P.filter (v ∈ ·)).card := by
    intro v
    have hfb : (Γ.biUnion id).filter (v ∈ ·) =
        Γ.biUnion (fun P => P.filter (v ∈ ·)) := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_biUnion, id_eq]
      tauto
    rw [hfb]
    apply Finset.card_biUnion
    intro P hP Q hQ hPQ
    have hd : Disjoint P Q :=
      (hpair (Finset.mem_coe.mpr hP) (Finset.mem_coe.mpr hQ) hPQ).toEdgeDisjoint
    exact hd.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  -- The odd-vertex set of `X` is the disjoint biUnion of member odd-vertex sets.
  have hset :
      Finset.univ.filter
          (fun v => Odd (((Γ.biUnion id).filter (v ∈ ·)).card)) =
        Γ.biUnion (fun P =>
          Finset.univ.filter (fun v => Odd ((P.filter (v ∈ ·)).card))) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    -- Others-zero: for a member touching `v`, all distinct members miss `v`.
    have hzero : ∀ P₀ ∈ Γ, v ∈ polymerSupport P₀ →
        ∀ Q ∈ Γ, Q ≠ P₀ → (Q.filter (v ∈ ·)).card = 0 := by
      intro P₀ hP₀ hvP₀ Q hQ hQP₀
      by_contra hcard
      have hvQ : v ∈ polymerSupport Q :=
        hvsupp Q v (Finset.card_ne_zero.mp hcard)
      have hvd : IsPolymerVertexDisjoint Q P₀ :=
        hpair (Finset.mem_coe.mpr hQ) (Finset.mem_coe.mpr hP₀) hQP₀
      exact (Finset.disjoint_left.mp hvd hvQ) hvP₀
    constructor
    · intro hv
      rw [hdeg v] at hv
      have hne : (∑ P ∈ Γ, (P.filter (v ∈ ·)).card) ≠ 0 := odd_ne _ hv
      obtain ⟨P₀, hP₀, hfne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
      have hvP₀ : v ∈ polymerSupport P₀ :=
        hvsupp P₀ v (Finset.card_ne_zero.mp hfne)
      have hsum : (∑ P ∈ Γ, (P.filter (v ∈ ·)).card) =
          (P₀.filter (v ∈ ·)).card :=
        Finset.sum_eq_single_of_mem P₀ hP₀
          (fun Q hQ hQP₀ => hzero P₀ hP₀ hvP₀ Q hQ hQP₀)
      rw [hsum] at hv
      exact ⟨P₀, hP₀, hv⟩
    · rintro ⟨P₀, hP₀, hvodd⟩
      rw [hdeg v]
      have hvP₀ : v ∈ polymerSupport P₀ :=
        hvsupp P₀ v (Finset.card_ne_zero.mp (odd_ne _ hvodd))
      have hsum : (∑ P ∈ Γ, (P.filter (v ∈ ·)).card) =
          (P₀.filter (v ∈ ·)).card :=
        Finset.sum_eq_single_of_mem P₀ hP₀
          (fun Q hQ hQP₀ => hzero P₀ hP₀ hvP₀ Q hQ hQP₀)
      rw [hsum]
      exact hvodd
  rw [hset]
  apply Finset.card_biUnion
  -- Member odd-vertex sets are pairwise disjoint (they sit in disjoint supports).
  intro P hP Q hQ hPQ
  simp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro v hvP hvQ
  rw [Finset.mem_filter] at hvP hvQ
  have hsuppP : v ∈ polymerSupport P := by
    have h0 : ∀ n : ℕ, Odd n → n ≠ 0 := by
      rintro n hn rfl; exact (by decide : ¬ Odd 0) hn
    exact hvsupp P v (Finset.card_ne_zero.mp (h0 _ hvP.2))
  have hsuppQ : v ∈ polymerSupport Q := by
    have h0 : ∀ n : ℕ, Odd n → n ≠ 0 := by
      rintro n hn rfl; exact (by decide : ¬ Odd 0) hn
    exact hvsupp Q v (Finset.card_ne_zero.mp (h0 _ hvQ.2))
  have hvd : IsPolymerVertexDisjoint P Q :=
    hpair (Finset.mem_coe.mpr hP) (Finset.mem_coe.mpr hQ) hPQ
  exact (Finset.disjoint_left.mp hvd hsuppP) hsuppQ

/-- **Field-weight factorization over a vertex-disjoint family**: for a pairwise
vertex-disjoint family `Γ` with `X = Γ.biUnion id`,
`fieldPolymerWeight a b X = ∏_{P ∈ Γ} fieldPolymerWeight a b P`. The
`tanh(a)^|·|` factor uses cardinality additivity (`Finset.card_biUnion` via
edge-disjointness), the `tanh(b)^{#odd(·)}` factor uses `oddCard_biUnion_of_vd`. -/
theorem fieldPolymerWeight_biUnion_of_vd {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Γ : Finset (Finset (Sym2 ι))}
    (hpair : (↑Γ : Set (Finset (Sym2 ι))).Pairwise IsPolymerVertexDisjoint)
    (a b : ℝ) :
    fieldPolymerWeight a b (Γ.biUnion id) = ∏ P ∈ Γ, fieldPolymerWeight a b P := by
  classical
  have hcard : (Γ.biUnion id).card = ∑ P ∈ Γ, P.card := by
    apply Finset.card_biUnion
    intro P hP Q hQ hPQ
    exact (hpair (Finset.mem_coe.mpr hP) (Finset.mem_coe.mpr hQ) hPQ).toEdgeDisjoint
  unfold fieldPolymerWeight
  rw [hcard, oddCard_biUnion_of_vd hpair, ← Finset.prod_pow_eq_pow_sum,
      ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]

/-- **Field-dependent polymer factorization identity** (GJ §17.6.1, brick 2a):
for all `a, b : ℝ`,
`∑_{X ⊆ E} tanh(a)^|X|·tanh(b)^{#odd(X)} =
  ∑_{Γ ∈ vdConnectedPolymerFamilies G} ∏_{P ∈ Γ} fieldPolymerWeight a b P`.

The edge-subset sum factorizes over the edge-connected components (polymers) of
`X`, exhibiting the field-dependent hard-core polymer gas. Proved by
`Finset.sum_bij` along the bijection `X ↔ polymerDecomposition X` between
`G.edgeFinset.powerset` and `vdConnectedPolymerFamilies G`, the parity-free
mirror of `evenSubgraphs_sum_eq_vdPolymerFamilies_sum`. The weight identity is
`fieldPolymerWeight_biUnion_of_vd`.

References: Friedli–Velenik §3.7.3, eq. (3.45), p. 117, and §5.7.3 give the
`h = 0` templates; §5.2 gives the abstract polymer model. Exercise 5.8, p. 238,
with its Appendix C solution, p. 531, gives the exact field weight. The
connected-family identity is a project extension. -/
theorem allSubgraphs_sum_eq_vdConnectedPolymerFamilies_sum
    (G : SimpleGraph ι) [Fintype G.edgeSet] (a b : ℝ) :
    (∑ X ∈ G.edgeFinset.powerset,
        Real.tanh a ^ X.card *
          Real.tanh b ^
            (Finset.univ.filter
              (fun v => Odd ((X.filter (v ∈ ·)).card))).card) =
      ∑ Γ ∈ vdConnectedPolymerFamilies G, ∏ P ∈ Γ, fieldPolymerWeight a b P := by
  classical
  apply Finset.sum_bij
    (fun X (_ : X ∈ G.edgeFinset.powerset) => polymerDecomposition X)
  · -- Membership: polymerDecomposition X ∈ vdConnectedPolymerFamilies G.
    intro X hX
    rw [Finset.mem_powerset] at hX
    rw [mem_vdConnectedPolymerFamilies]
    refine ⟨?_, polymerDecomposition_pairwise_vertexDisjoint⟩
    intro C hC
    rw [mem_allConnectedPolymers]
    rw [mem_polymerDecomposition] at hC
    obtain ⟨e, he, rfl⟩ := hC
    exact edgeComponent_isConnectedPolymer hX he
  · -- Injectivity via polymerDecomposition_biUnion_id.
    intro X _ X' _ h_eq
    have h₁ : (polymerDecomposition X).biUnion id = X :=
      polymerDecomposition_biUnion_id X
    have h₂ : (polymerDecomposition X').biUnion id = X' :=
      polymerDecomposition_biUnion_id X'
    rw [← h₁, ← h₂, h_eq]
  · -- Surjectivity: given Γ, take X = Γ.biUnion id.
    intro Γ hΓ
    rw [mem_vdConnectedPolymerFamilies] at hΓ
    obtain ⟨hsub, hpair⟩ := hΓ
    have hconn : ∀ P ∈ Γ, IsEdgeConnected P := fun P hP =>
      (mem_allConnectedPolymers.mp (hsub hP)).connected
    have hne : ∀ P ∈ Γ, P.Nonempty := fun P hP =>
      (mem_allConnectedPolymers.mp (hsub hP)).nonempty
    refine ⟨Γ.biUnion id, ?_, ?_⟩
    · rw [Finset.mem_powerset]
      intro e he
      rw [Finset.mem_biUnion] at he
      obtain ⟨P, hP, heP⟩ := he
      exact (mem_allConnectedPolymers.mp (hsub hP)).subset heP
    · exact polymerDecomposition_biUnion_of_pairwiseVertexDisjoint hpair hconn
        hne
  · -- Weight match via fieldPolymerWeight_biUnion_of_vd.
    intro X _
    have h_biU : (polymerDecomposition X).biUnion id = X :=
      polymerDecomposition_biUnion_id X
    have hw := fieldPolymerWeight_biUnion_of_vd
      (polymerDecomposition_pairwise_vertexDisjoint (X := X)) a b
    rw [h_biU] at hw
    exact hw


end IsingModel

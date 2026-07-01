import IsingModel.ClusterExpansion.TwoPointNumeratorEquality

/-!
# Anchored one-component peel of the high-temperature-expansion numerator (K1)

This file proves the first unconditional combinatorial brick ("K1") in the chain that generalizes
the two-point-only infinite-volume `β`-derivative to a general-observable correlation on the
Kotecký–Preiss high-temperature window, toward Glimm–Jaffe (GJ) Theorem 17.6.1 (p.313).  K1 is a
pure algebraic/combinatorial **identity** on the subgraph-activity numerator
`Q_A(t) = htSubgraphSum G A t = ∑_{X : ∂X = A} t^{|X|}`: an **anchored one-component peel**.

Fix a nonempty even boundary set `A`, an anchor `a ∈ A`, and a complex activity `t`.  Every edge
subset `X` with odd boundary `∂X = A` decomposes into pairwise **vertex-disjoint** connected
components (`polymerDecomposition X`), and the odd boundary distributes disjointly over that
decomposition (`oddBoundary_biUnion_polymerDecomposition`, the union being disjoint as *vertex*
sets).  Since `a ∈ ∂X = A`, the anchor lies in the boundary of a **unique** component `C_a`
(`existsUnique_component_mem_oddBoundary`).  Setting `B := ∂C_a`, the remainder `Y := X ∖ C_a` is
vertex-disjoint from `C_a` with `∂Y = A ∖ B` and `t^{|X|} = t^{|C_a|} · t^{|Y|}`.  Reorganizing the
defining sum by the value of the anchored component yields, with

* `evenSubsetsThrough A a` — even subsets `B ⊆ A` through the anchor (`a ∈ B`, `Even |B|`),
* `connectedComponentsWithBoundary G B` — nonempty edge-connected `C ⊆ G.edgeFinset` with `∂C = B`,
* `htSubgraphSumAvoiding' G C A'` — the boundary-`A'` remainder sum `∑_{Y ⊥ C, ∂Y = A'} t^{|Y|}`,

the identity (`htSubgraphSum_anchored_peel`)
`Q_A(t) = ∑_{B ∈ evenSubsetsThrough A a} ∑_{C ∈ connectedComponentsWithBoundary G B}
  t^{|C|} · htSubgraphSumAvoiding' G C (A ∖ B) t`.
The remainder boundary is the honest set difference `A ∖ B` (the components' boundaries never
overlap, so no symmetric-difference cancellation occurs), and `a ∈ B` forces `B ≠ ∅`, hence
`|A ∖ B| < |A|` — the strict decrease that later powers the induction on `|A|`.

The `|A| = 2` case (`A = {i,j}`, anchor `a = i`) recovers the existing pair-only factorization
`htSubgraphSum_pair_eq_sum_connectingComponent` (via `htSubgraphSum_anchored_peel_pair`), the
correctness cross-check.

This is brick K1 of the general-observable `β`-derivative chain (Issue #4404); K2/K3 (the analytic
ratio bounds) build on it.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), Theorem 17.6.1 (p.313),
§17.5–17.6 (pp.311–314), Chapter 18 cluster expansion (§18.4–18.7, p.321 ff); Friedli–Velenik,
*Statistical Mechanics of Lattice Systems* (CUP, 2017), §3.7.3.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Boundary-`A'` avoiding remainder sum -/

/-- Edge subsets of `G` vertex-disjoint from `C` whose odd boundary is `A'`. -/
noncomputable def subgraphsAvoidingBoundary (G : SimpleGraph ι) [Fintype G.edgeSet]
    (C : Finset (Sym2 ι)) (A' : Finset ι) : Finset (Finset (Sym2 ι)) := by
  classical
  exact G.edgeFinset.powerset.filter (fun Y => IsPolymerVertexDisjoint C Y ∧ oddBoundary Y = A')

/-- **Boundary-`A'` avoiding remainder sum** `Q^{av}_{C,A'}(t) = ∑_{Y ⊥ C, ∂Y = A'} t^{|Y|}`: the
generalization of `htSubgraphSumAvoiding` to a prescribed remainder boundary `A'` (recovered at
`A' = ∅`).  Used to peel one connected component off the numerator `htSubgraphSum`. -/
noncomputable def htSubgraphSumAvoiding' (G : SimpleGraph ι) [Fintype G.edgeSet]
    (C : Finset (Sym2 ι)) (A' : Finset ι) (t : ℂ) : ℂ :=
  ∑ Y ∈ subgraphsAvoidingBoundary G C A', t ^ Y.card

/-- **Reduction to the empty-boundary remainder**: `Q^{av}_{C,∅} = Q^{av}_C`, since an edge subset
has empty odd boundary iff it is an even subgraph. -/
theorem htSubgraphSumAvoiding'_boundary_empty (G : SimpleGraph ι) [Fintype G.edgeSet]
    (C : Finset (Sym2 ι)) (t : ℂ) :
    htSubgraphSumAvoiding' G C ∅ t = htSubgraphSumAvoiding G C t := by
  classical
  unfold htSubgraphSumAvoiding' htSubgraphSumAvoiding
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  unfold subgraphsAvoidingBoundary evenSubgraphsAvoiding
  ext Y
  simp only [Finset.mem_filter, mem_evenSubgraphs, Finset.mem_powerset]
  constructor
  · rintro ⟨hYpow, hdisj, hYbd⟩
    refine ⟨⟨hYpow, fun v => ?_⟩, hdisj⟩
    have hvnot : ¬ Odd ((Y.filter (v ∈ ·)).card) := by
      intro hvodd
      have hvbd : v ∈ oddBoundary Y := by
        rw [oddBoundary, Finset.mem_filter]
        exact ⟨Finset.mem_univ v, hvodd⟩
      rw [hYbd] at hvbd
      exact (Finset.notMem_empty v) hvbd
    exact Nat.not_odd_iff_even.mp hvnot
  · rintro ⟨hYeven, hdisj⟩
    exact ⟨hYeven.subset, hdisj, oddBoundary_eq_empty_of_isEvenSubgraph G hYeven⟩

/-! ### The unique anchored component -/

/-- **Unique anchored component** (general-`A` analogue of
`existsUnique_component_oddBoundary_pair`):
if the anchor `a` lies in the odd boundary of `X`, then `a` lies in the odd boundary of a *unique*
component `C ∈ polymerDecomposition X`.  Existence is the boundary distribution
`∂X = ⊔_C ∂C`; uniqueness is vertex-disjointness of the components (a second such component would
also support `a`). -/
theorem existsUnique_component_mem_oddBoundary (X : Finset (Sym2 ι)) {a : ι}
    (ha : a ∈ oddBoundary X) :
    ∃! C, C ∈ polymerDecomposition X ∧ a ∈ oddBoundary C := by
  classical
  rw [oddBoundary_biUnion_polymerDecomposition X, Finset.mem_biUnion] at ha
  obtain ⟨C, hC, haC⟩ := ha
  refine ⟨C, ⟨hC, haC⟩, ?_⟩
  rintro C' ⟨hC'mem, haC'⟩
  by_contra hne
  have hpairwise := polymerDecomposition_pairwise_vertexDisjoint (X := X)
  have hdisj : IsPolymerVertexDisjoint C' C :=
    hpairwise (Finset.mem_coe.mpr hC'mem) (Finset.mem_coe.mpr hC) hne
  unfold IsPolymerVertexDisjoint at hdisj
  have haC'sup : a ∈ polymerSupport C' := oddBoundary_subset_polymerSupport C' haC'
  have haCsup : a ∈ polymerSupport C := oddBoundary_subset_polymerSupport C haC
  exact (Finset.disjoint_left.mp hdisj) haC'sup haCsup

/-- The unique component of `X` whose odd boundary contains the anchor `a`. -/
noncomputable def anchoredComponentOf (X : Finset (Sym2 ι)) {a : ι}
    (ha : a ∈ oddBoundary X) : Finset (Sym2 ι) :=
  Classical.choose (existsUnique_component_mem_oddBoundary X ha)

/-- The anchored component lies in the component decomposition. -/
theorem anchoredComponentOf_mem (X : Finset (Sym2 ι)) {a : ι} (ha : a ∈ oddBoundary X) :
    anchoredComponentOf X ha ∈ polymerDecomposition X :=
  (Classical.choose_spec (existsUnique_component_mem_oddBoundary X ha)).1.1

/-- The anchor lies in the odd boundary of the anchored component. -/
theorem anchoredComponentOf_mem_oddBoundary (X : Finset (Sym2 ι)) {a : ι}
    (ha : a ∈ oddBoundary X) :
    a ∈ oddBoundary (anchoredComponentOf X ha) :=
  (Classical.choose_spec (existsUnique_component_mem_oddBoundary X ha)).1.2

/-- The anchored component is the unique component whose odd boundary contains the anchor. -/
theorem anchoredComponentOf_unique (X : Finset (Sym2 ι)) {a : ι} (ha : a ∈ oddBoundary X)
    {C : Finset (Sym2 ι)} (hC : C ∈ polymerDecomposition X ∧ a ∈ oddBoundary C) :
    C = anchoredComponentOf X ha :=
  (Classical.choose_spec (existsUnique_component_mem_oddBoundary X ha)).2 C hC

/-- Total version of the anchored component (junk value `∅` off its domain), used as the forward map
of the peel bijection. -/
noncomputable def anchoredComponentAt (a : ι) (X : Finset (Sym2 ι)) : Finset (Sym2 ι) := by
  classical
  exact if ha : a ∈ oddBoundary X then anchoredComponentOf X ha else ∅

/-- The total anchored component unfolds on its domain. -/
theorem anchoredComponentAt_eq {a : ι} {X : Finset (Sym2 ι)} (ha : a ∈ oddBoundary X) :
    anchoredComponentAt a X = anchoredComponentOf X ha := by
  unfold anchoredComponentAt
  rw [dif_pos ha]

/-! ### Supporting distribution/disjointness lemmas -/

omit [Fintype ι] in
/-- A decomposition component is nonempty. -/
theorem nonempty_of_mem_polymerDecomposition {X C : Finset (Sym2 ι)}
    (hC : C ∈ polymerDecomposition X) : C.Nonempty := by
  rw [mem_polymerDecomposition] at hC
  obtain ⟨e, he, rfl⟩ := hC
  exact ⟨e, self_mem_edgeComponent he⟩

omit [Fintype ι] in
/-- A decomposition component is edge-connected. -/
theorem isEdgeConnected_of_mem_polymerDecomposition {X C : Finset (Sym2 ι)}
    (hC : C ∈ polymerDecomposition X) : IsEdgeConnected C := by
  rw [mem_polymerDecomposition] at hC
  obtain ⟨e, _he, rfl⟩ := hC
  exact isEdgeConnected_edgeComponent e

/-- The odd boundary of a decomposition component is contained in the odd boundary of the whole
subgraph (one block of the disjoint union `∂X = ⊔_C ∂C`). -/
theorem oddBoundary_component_subset (X : Finset (Sym2 ι)) {C : Finset (Sym2 ι)}
    (hC : C ∈ polymerDecomposition X) :
    oddBoundary C ⊆ oddBoundary X := by
  classical
  intro v hv
  have hvU : v ∈ (polymerDecomposition X).biUnion oddBoundary := by
    rw [Finset.mem_biUnion]
    exact ⟨C, hC, hv⟩
  rwa [← oddBoundary_biUnion_polymerDecomposition X] at hvU

/-- Vertex-disjoint edge sets have disjoint odd boundaries (`∂ ⊆ support`). -/
theorem oddBoundary_disjoint_of_vertexDisjoint {C Y : Finset (Sym2 ι)}
    (h : IsPolymerVertexDisjoint C Y) :
    Disjoint (oddBoundary C) (oddBoundary Y) := by
  unfold IsPolymerVertexDisjoint at h
  rw [Finset.disjoint_left]
  intro v hvC hvY
  exact (Finset.disjoint_left.mp h)
    (oddBoundary_subset_polymerSupport C hvC) (oddBoundary_subset_polymerSupport Y hvY)

/-- A decomposition component is vertex-disjoint from the complementary remainder `X ∖ C`. -/
theorem mem_polymerDecomposition_vertexDisjoint_sdiff
    {X C : Finset (Sym2 ι)} (hC : C ∈ polymerDecomposition X) :
    IsPolymerVertexDisjoint C (X \ C) := by
  classical
  unfold IsPolymerVertexDisjoint
  rw [Finset.disjoint_left]
  intro v hvC hvY
  rw [mem_polymerSupport] at hvC hvY
  obtain ⟨eC, heC, hveC⟩ := hvC
  obtain ⟨eY, heY, hveY⟩ := hvY
  have hbi : ((polymerDecomposition X).erase C).biUnion id = X \ C :=
    biUnion_erase_eq_sdiff_of_mem_polymerDecomposition hC
  have heYΓ : eY ∈ ((polymerDecomposition X).erase C).biUnion id := by
    simpa [hbi] using heY
  rw [Finset.mem_biUnion] at heYΓ
  obtain ⟨D, hD, heYD⟩ := heYΓ
  rw [Finset.mem_erase] at hD
  have hpairwise := polymerDecomposition_pairwise_vertexDisjoint (X := X)
  have hdisj : IsPolymerVertexDisjoint D C :=
    hpairwise (Finset.mem_coe.mpr hD.2) (Finset.mem_coe.mpr hC) hD.1
  unfold IsPolymerVertexDisjoint at hdisj
  have hvD : v ∈ polymerSupport D := mem_polymerSupport.mpr ⟨eY, heYD, hveY⟩
  have hvC' : v ∈ polymerSupport C := mem_polymerSupport.mpr ⟨eC, heC, hveC⟩
  exact (Finset.disjoint_left.mp hdisj) hvD hvC'

/-- **Boundary of the remainder**: peeling a component `C` leaves odd boundary `∂(X ∖ C) = ∂X ∖ ∂C`
(the component boundaries are disjoint, so this is genuine set difference, not symmetric
difference). -/
theorem oddBoundary_sdiff_component
    {X C : Finset (Sym2 ι)} (hC : C ∈ polymerDecomposition X) :
    oddBoundary (X \ C) = oddBoundary X \ oddBoundary C := by
  classical
  have hsub : C ⊆ X := mem_polymerDecomposition_subset hC
  have hdisjV : IsPolymerVertexDisjoint C (X \ C) :=
    mem_polymerDecomposition_vertexDisjoint_sdiff hC
  have hdisjB : Disjoint (oddBoundary C) (oddBoundary (X \ C)) :=
    oddBoundary_disjoint_of_vertexDisjoint hdisjV
  have hbd : oddBoundary X = oddBoundary C ∪ oddBoundary (X \ C) := by
    conv_lhs => rw [← Finset.union_sdiff_of_subset hsub]
    exact oddBoundary_union_of_vertexDisjoint hdisjV
  rw [hbd, Finset.union_sdiff_cancel_left hdisjB]

/-! ### The anchored peel identity -/

/-- Edge subsets of `G` with odd boundary `A` (the summation domain of `htSubgraphSum`). -/
noncomputable def boundarySubgraphs (G : SimpleGraph ι) [Fintype G.edgeSet]
    (A : Finset ι) : Finset (Finset (Sym2 ι)) :=
  G.edgeFinset.powerset.filter (fun X => oddBoundary X = A)

/-- **Even subsets through the anchor**: subsets `B ⊆ A` with `a ∈ B` and `Even |B|` — the outer
index set of the peel. -/
noncomputable def evenSubsetsThrough (A : Finset ι) (a : ι) : Finset (Finset ι) :=
  A.powerset.filter (fun B => a ∈ B ∧ Even B.card)

/-- **Connected components with prescribed boundary `B`**: nonempty edge-connected
`C ⊆ G.edgeFinset` with `∂C = B`.  With `B = {i,j}` this is `connectingComponents G i j`; the anchor
clause `a ∈ supp C` of the note is redundant here since it is enforced by `a ∈ B = ∂C ⊆ supp C` in
the outer index. -/
noncomputable def connectedComponentsWithBoundary (G : SimpleGraph ι) [Fintype G.edgeSet]
    (B : Finset ι) : Finset (Finset (Sym2 ι)) := by
  classical
  exact G.edgeFinset.powerset.filter
    (fun C => C.Nonempty ∧ IsEdgeConnected C ∧ oddBoundary C = B)

/-- **Anchored connected components**: nonempty edge-connected `C ⊆ G.edgeFinset` whose boundary
contains the anchor and is contained in `A` — the single-summation index of the peel. -/
noncomputable def anchoredComponents (G : SimpleGraph ι) [Fintype G.edgeSet]
    (A : Finset ι) (a : ι) : Finset (Finset (Sym2 ι)) := by
  classical
  exact G.edgeFinset.powerset.filter
    (fun C => C.Nonempty ∧ IsEdgeConnected C ∧ a ∈ oddBoundary C ∧ oddBoundary C ⊆ A)

/-- Product-side ambient pair set for the peel bijection: an anchored component and an arbitrary
remainder, vertex-disjoint, with the complementary boundary. -/
noncomputable def anchoredPairs (G : SimpleGraph ι) [Fintype G.edgeSet]
    (A : Finset ι) (a : ι) : Finset (Finset (Sym2 ι) × Finset (Sym2 ι)) := by
  classical
  exact (anchoredComponents G A a ×ˢ G.edgeFinset.powerset).filter
    (fun p => IsPolymerVertexDisjoint p.1 p.2 ∧ oddBoundary p.2 = A \ oddBoundary p.1)

/-- The anchored-pair sum factors into the outer anchored-component sum and the boundary-`(A ∖ ∂C)`
avoiding remainder sum. -/
theorem anchoredPairs_sum_eq_complex (G : SimpleGraph ι) [Fintype G.edgeSet]
    (A : Finset ι) (a : ι) (t : ℂ) :
    (∑ p ∈ anchoredPairs G A a, t ^ p.1.card * t ^ p.2.card) =
      ∑ C ∈ anchoredComponents G A a,
        t ^ C.card * htSubgraphSumAvoiding' G C (A \ oddBoundary C) t := by
  classical
  unfold anchoredPairs htSubgraphSumAvoiding' subgraphsAvoidingBoundary
  rw [Finset.sum_filter, Finset.sum_product]
  simp_rw [Finset.mul_sum, Finset.sum_filter]

/-- **Single-summation anchored peel**: the numerator groups by its unique anchored component,
`Q_A(t) = ∑_{C anchored} t^{|C|} · Q^{av}_{C, A ∖ ∂C}(t)`. -/
theorem htSubgraphSum_anchored_peel_component (G : SimpleGraph ι) [Fintype G.edgeSet]
    {A : Finset ι} {a : ι} (ha : a ∈ A) (t : ℂ) :
    htSubgraphSum G A t =
      ∑ C ∈ anchoredComponents G A a,
        t ^ C.card * htSubgraphSumAvoiding' G C (A \ oddBoundary C) t := by
  classical
  rw [← anchoredPairs_sum_eq_complex G A a t]
  have hsum : htSubgraphSum G A t = ∑ X ∈ boundarySubgraphs G A, t ^ X.card := rfl
  rw [hsum]
  refine Finset.sum_bij'
    (fun X _ => (anchoredComponentAt a X, X \ anchoredComponentAt a X))
    (fun p _ => p.1 ∪ p.2)
    ?_ ?_ ?_ ?_ ?_
  · -- forward map lands in `anchoredPairs`
    intro X hX
    obtain ⟨hXpow, hXbd⟩ := Finset.mem_filter.mp hX
    have haX : a ∈ oddBoundary X := by rw [hXbd]; exact ha
    have hCmem : anchoredComponentOf X haX ∈ polymerDecomposition X :=
      anchoredComponentOf_mem X haX
    change (anchoredComponentAt a X, X \ anchoredComponentAt a X) ∈ anchoredPairs G A a
    rw [anchoredComponentAt_eq haX, anchoredPairs, Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [anchoredComponents, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.mem_powerset.mp (polymerDecomposition_subset_edgeFinset G hXpow hCmem),
        nonempty_of_mem_polymerDecomposition hCmem,
        isEdgeConnected_of_mem_polymerDecomposition hCmem,
        anchoredComponentOf_mem_oddBoundary X haX, ?_⟩
      exact hXbd ▸ oddBoundary_component_subset X hCmem
    · exact Finset.mem_powerset.mpr
        (Finset.sdiff_subset.trans (Finset.mem_powerset.mp hXpow))
    · exact mem_polymerDecomposition_vertexDisjoint_sdiff hCmem
    · rw [oddBoundary_sdiff_component hCmem, hXbd]
  · -- inverse map lands in `boundarySubgraphs`
    intro p hp
    rw [anchoredPairs, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨hp1, hp2⟩, hdisj, hbd2⟩ := hp
    rw [anchoredComponents, Finset.mem_filter, Finset.mem_powerset] at hp1
    obtain ⟨hp1pow, _, _, _, hp1subA⟩ := hp1
    rw [boundarySubgraphs, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.union_subset hp1pow (Finset.mem_powerset.mp hp2), ?_⟩
    rw [oddBoundary_union_of_vertexDisjoint hdisj, hbd2, Finset.union_sdiff_of_subset hp1subA]
  · -- left inverse `j (i X) = X`
    intro X hX
    obtain ⟨_, hXbd⟩ := Finset.mem_filter.mp hX
    have haX : a ∈ oddBoundary X := by rw [hXbd]; exact ha
    have hsub : anchoredComponentOf X haX ⊆ X :=
      mem_polymerDecomposition_subset (anchoredComponentOf_mem X haX)
    change anchoredComponentAt a X ∪ (X \ anchoredComponentAt a X) = X
    rw [anchoredComponentAt_eq haX]
    exact Finset.union_sdiff_of_subset hsub
  · -- right inverse `i (j p) = p`
    intro p hp
    rw [anchoredPairs, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨hp1, hp2⟩, hdisj, _⟩ := hp
    rw [anchoredComponents, Finset.mem_filter, Finset.mem_powerset] at hp1
    obtain ⟨_, hp1ne, hp1conn, hp1anchor, _⟩ := hp1
    have haU : a ∈ oddBoundary (p.1 ∪ p.2) := by
      rw [oddBoundary_union_of_vertexDisjoint hdisj, Finset.mem_union]
      exact Or.inl hp1anchor
    have hp1decomp : p.1 ∈ polymerDecomposition (p.1 ∪ p.2) :=
      mem_polymerDecomposition_of_isEdgeConnected_vertexDisjoint hp1ne hp1conn hdisj
    have hCeq : anchoredComponentOf (p.1 ∪ p.2) haU = p.1 :=
      (anchoredComponentOf_unique (p.1 ∪ p.2) haU ⟨hp1decomp, hp1anchor⟩).symm
    have hedge : Disjoint p.1 p.2 := by
      simpa [IsPolymerCompatible] using hdisj.toEdgeDisjoint
    change (anchoredComponentAt a (p.1 ∪ p.2),
      (p.1 ∪ p.2) \ anchoredComponentAt a (p.1 ∪ p.2)) = p
    rw [anchoredComponentAt_eq haU, hCeq, Finset.union_sdiff_cancel_left hedge]
  · -- forward-map weight `t^{|X|} = t^{|C|} · t^{|X ∖ C|}`
    intro X hX
    obtain ⟨_, hXbd⟩ := Finset.mem_filter.mp hX
    have haX : a ∈ oddBoundary X := by rw [hXbd]; exact ha
    have hsub : anchoredComponentOf X haX ⊆ X :=
      mem_polymerDecomposition_subset (anchoredComponentOf_mem X haX)
    change t ^ X.card =
      t ^ (anchoredComponentAt a X).card * t ^ (X \ anchoredComponentAt a X).card
    rw [anchoredComponentAt_eq haX]
    have hcard : X.card =
        (anchoredComponentOf X haX).card + (X \ anchoredComponentOf X haX).card := by
      have h := Finset.card_sdiff_add_card_eq_card hsub
      omega
    rw [hcard, pow_add]

/-- **K1 — the anchored one-component peel identity** (GJ Theorem 17.6.1, p.313; §18 cluster
expansion, §18.4–18.7; FV §3.7.3).  Brick K1 of the general-observable `β`-derivative chain
(Issue #4404).  For a nonempty even boundary set `A` and anchor `a ∈ A`, the numerator groups by the
unique anchored component and its even block `B = ∂C`:
`Q_A(t) = ∑_{B ∈ evenSubsetsThrough A a} ∑_{C ∈ connectedComponentsWithBoundary G B}
  t^{|C|} · Q^{av}_{C, A ∖ B}(t)`.
The remainder boundary is the genuine set difference `A ∖ B` (component boundaries never overlap),
and `a ∈ B` forces `B ≠ ∅`, hence `|A ∖ B| < |A|`. -/
theorem htSubgraphSum_anchored_peel (G : SimpleGraph ι) [Fintype G.edgeSet]
    {A : Finset ι} {a : ι} (ha : a ∈ A) (t : ℂ) :
    htSubgraphSum G A t =
      ∑ B ∈ evenSubsetsThrough A a,
        ∑ C ∈ connectedComponentsWithBoundary G B,
          t ^ C.card * htSubgraphSumAvoiding' G C (A \ B) t := by
  classical
  have hmaps : ∀ C ∈ anchoredComponents G A a, oddBoundary C ∈ evenSubsetsThrough A a := by
    intro C hC
    rw [anchoredComponents, Finset.mem_filter, Finset.mem_powerset] at hC
    obtain ⟨hCpow, _, _, hCanchor, hCsubA⟩ := hC
    rw [evenSubsetsThrough, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hCsubA, hCanchor, oddBoundary_card_even G (Finset.mem_powerset.mpr hCpow)⟩
  rw [htSubgraphSum_anchored_peel_component G ha t,
    ← Finset.sum_fiberwise_of_maps_to hmaps
      (fun C => t ^ C.card * htSubgraphSumAvoiding' G C (A \ oddBoundary C) t)]
  refine Finset.sum_congr rfl (fun B hB => ?_)
  rw [evenSubsetsThrough, Finset.mem_filter, Finset.mem_powerset] at hB
  obtain ⟨hBsubA, hBanchor, _⟩ := hB
  have hfilter : (anchoredComponents G A a).filter (fun C => oddBoundary C = B)
      = connectedComponentsWithBoundary G B := by
    ext C
    rw [Finset.mem_filter, anchoredComponents, connectedComponentsWithBoundary,
      Finset.mem_filter, Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨⟨hCpow, hCne, hCconn, _, _⟩, hCB⟩
      exact ⟨hCpow, hCne, hCconn, hCB⟩
    · rintro ⟨hCpow, hCne, hCconn, hCB⟩
      exact ⟨⟨hCpow, hCne, hCconn, hCB ▸ hBanchor, hCB ▸ hBsubA⟩, hCB⟩
  rw [hfilter]
  refine Finset.sum_congr rfl (fun C hC => ?_)
  rw [connectedComponentsWithBoundary, Finset.mem_filter] at hC
  obtain ⟨_, _, _, hCB⟩ := hC
  rw [hCB]

/-! ### Cross-check: the pair lemma is the `|A| = 2` case -/

/-- The connected components with pair boundary `{i,j}` are exactly the connecting components. -/
theorem connectedComponentsWithBoundary_pair (G : SimpleGraph ι) [Fintype G.edgeSet]
    (i j : ι) :
    connectedComponentsWithBoundary G ({i, j} : Finset ι) = connectingComponents G i j := by
  classical
  ext C
  simp only [connectedComponentsWithBoundary, connectingComponents, Finset.mem_filter]

omit [Fintype ι] in
/-- The even subsets of a pair `{i,j}` through `i` collapse to the single block `{i,j}`. -/
theorem evenSubsetsThrough_pair {i j : ι} (hij : i ≠ j) :
    evenSubsetsThrough ({i, j} : Finset ι) i = {({i, j} : Finset ι)} := by
  classical
  ext B
  rw [evenSubsetsThrough, Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
  constructor
  · rintro ⟨hsub, hi, heven⟩
    rcases finset_subset_pair_of_even_card hij hsub heven with h | h
    · rw [h] at hi; exact absurd hi (Finset.notMem_empty i)
    · exact h
  · rintro rfl
    exact ⟨Finset.Subset.refl _, Finset.mem_insert_self i {j},
      by rw [Finset.card_pair hij]; exact ⟨1, rfl⟩⟩

/-- **Cross-check / pair recovery**: at `A = {i,j}` (anchor `a = i`) the anchored peel collapses to
the existing two-point factorization `htSubgraphSum_pair_eq_sum_connectingComponent` — the only
surviving block is `B = {i,j}`, giving `A ∖ B = ∅` and `Q^{av}_{C,∅} = Q^{av}_C`. -/
theorem htSubgraphSum_anchored_peel_pair (G : SimpleGraph ι) [Fintype G.edgeSet]
    {i j : ι} (hij : i ≠ j) (t : ℂ) :
    htSubgraphSum G ({i, j} : Finset ι) t =
      ∑ C ∈ connectingComponents G i j, t ^ C.card * htSubgraphSumAvoiding G C t := by
  classical
  rw [htSubgraphSum_anchored_peel G (Finset.mem_insert_self i {j}) t,
    evenSubsetsThrough_pair hij, Finset.sum_singleton,
    connectedComponentsWithBoundary_pair G i j, Finset.sdiff_self]
  refine Finset.sum_congr rfl (fun C _ => ?_)
  rw [htSubgraphSumAvoiding'_boundary_empty]

end IsingModel

import IsingModel.ClusterExpansion.TwoPointNumeratorFactorization
import IsingModel.ClusterExpansion.Families.EvenSubgraphs

/-!
# Two-point numerator bound by a connecting component and an even remainder

This file proves the norm-first inequality for the high-temperature two-point numerator.  The proof
uses only the injective forward map sending a two-point subgraph to its unique connecting component
and the remaining even subgraph; it does not prove or use the equality/bijection factorization.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Edge subsets of `G` whose odd boundary is the pair `{i,j}`. -/
noncomputable def twoPointSubgraphs (G : SimpleGraph ι) [Fintype G.edgeSet]
    (i j : ι) : Finset (Finset (Sym2 ι)) :=
  G.edgeFinset.powerset.filter (fun X => oddBoundary X = ({i, j} : Finset ι))

/-- Candidate connecting open components in `G` with odd boundary `{i,j}`. -/
noncomputable def connectingComponents (G : SimpleGraph ι) [Fintype G.edgeSet]
    (i j : ι) : Finset (Finset (Sym2 ι)) := by
  classical
  exact G.edgeFinset.powerset.filter
    (fun C => C.Nonempty ∧ IsEdgeConnected C ∧ oddBoundary C = ({i, j} : Finset ι))

/-- Even subgraphs of `G` whose support is vertex-disjoint from `C`. -/
noncomputable def evenSubgraphsAvoiding (G : SimpleGraph ι) [Fintype G.edgeSet]
    (C : Finset (Sym2 ι)) : Finset (Finset (Sym2 ι)) := by
  classical
  exact (evenSubgraphs G).filter (fun Y => IsPolymerVertexDisjoint C Y)

/-- The product-side ambient pair set for the forward injection. -/
noncomputable def connectingPairs (G : SimpleGraph ι) [Fintype G.edgeSet]
    (i j : ι) : Finset (Finset (Sym2 ι) × Finset (Sym2 ι)) := by
  classical
  exact (connectingComponents G i j ×ˢ evenSubgraphs G).filter
    (fun p => IsPolymerVertexDisjoint p.1 p.2)

/-- The unique component of `X` with odd boundary `{i,j}`. -/
noncomputable def connectingComponentOf (G : SimpleGraph ι) [Fintype G.edgeSet]
    {X : Finset (Sym2 ι)} {i j : ι}
    (hX : X ∈ G.edgeFinset.powerset) (hij : i ≠ j)
    (hbd : oddBoundary X = ({i, j} : Finset ι)) : Finset (Sym2 ι) :=
  Classical.choose (existsUnique_component_oddBoundary_pair G hX hij hbd)

/-- The chosen connecting component lies in the component decomposition. -/
theorem connectingComponentOf_mem (G : SimpleGraph ι) [Fintype G.edgeSet]
    {X : Finset (Sym2 ι)} {i j : ι}
    (hX : X ∈ G.edgeFinset.powerset) (hij : i ≠ j)
    (hbd : oddBoundary X = ({i, j} : Finset ι)) :
    connectingComponentOf G hX hij hbd ∈ polymerDecomposition X := by
  classical
  exact (Classical.choose_spec (existsUnique_component_oddBoundary_pair G hX hij hbd)).1.1

/-- The chosen connecting component has odd boundary `{i,j}`. -/
theorem connectingComponentOf_oddBoundary (G : SimpleGraph ι) [Fintype G.edgeSet]
    {X : Finset (Sym2 ι)} {i j : ι}
    (hX : X ∈ G.edgeFinset.powerset) (hij : i ≠ j)
    (hbd : oddBoundary X = ({i, j} : Finset ι)) :
    oddBoundary (connectingComponentOf G hX hij hbd) = ({i, j} : Finset ι) := by
  classical
  exact (Classical.choose_spec (existsUnique_component_oddBoundary_pair G hX hij hbd)).1.2

/-- The chosen connecting component is unique among components with boundary `{i,j}`. -/
theorem connectingComponentOf_unique (G : SimpleGraph ι) [Fintype G.edgeSet]
    {X C : Finset (Sym2 ι)} {i j : ι}
    (hX : X ∈ G.edgeFinset.powerset) (hij : i ≠ j)
    (hbd : oddBoundary X = ({i, j} : Finset ι))
    (hC : C ∈ polymerDecomposition X ∧ oddBoundary C = ({i, j} : Finset ι)) :
    C = connectingComponentOf G hX hij hbd := by
  classical
  exact (Classical.choose_spec (existsUnique_component_oddBoundary_pair G hX hij hbd)).2 C hC

omit [Fintype ι] in
/-- A component in `polymerDecomposition X` is contained in `X`. -/
theorem mem_polymerDecomposition_subset {X C : Finset (Sym2 ι)}
    (hC : C ∈ polymerDecomposition X) : C ⊆ X := by
  intro e he
  have heU : e ∈ (polymerDecomposition X).biUnion id := by
    rw [Finset.mem_biUnion]
    exact ⟨C, hC, he⟩
  simpa [polymerDecomposition_biUnion_id X] using heU

omit [Fintype ι] in
/-- Erasing one component from the decomposition unions to the edge complement of that component. -/
theorem biUnion_erase_eq_sdiff_of_mem_polymerDecomposition [Finite ι]
    {X C : Finset (Sym2 ι)} (hC : C ∈ polymerDecomposition X) :
    ((polymerDecomposition X).erase C).biUnion id = X \ C := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  ext e
  rw [Finset.mem_biUnion, Finset.mem_sdiff]
  constructor
  · rintro ⟨D, hD, heD⟩
    rw [Finset.mem_erase] at hD
    refine ⟨mem_polymerDecomposition_subset hD.2 heD, ?_⟩
    intro heC
    have hpairwise := polymerDecomposition_pairwise_vertexDisjoint (X := X)
    have hdisj : IsPolymerVertexDisjoint D C :=
      hpairwise (Finset.mem_coe.mpr hD.2) (Finset.mem_coe.mpr hC) hD.1
    unfold IsPolymerVertexDisjoint at hdisj
    let v : ι := e.out.1
    have hv : v ∈ e := Sym2.out_fst_mem e
    have hesD : v ∈ polymerSupport D := by
      rw [mem_polymerSupport]
      exact ⟨e, heD, hv⟩
    have hesC : v ∈ polymerSupport C := by
      rw [mem_polymerSupport]
      exact ⟨e, heC, hv⟩
    exact (Finset.disjoint_left.mp hdisj) hesD hesC
  · rintro ⟨heX, heCnot⟩
    obtain ⟨D, hD, heD⟩ : ∃ D ∈ polymerDecomposition X, e ∈ D := by
      rw [← polymerDecomposition_biUnion_id X, Finset.mem_biUnion] at heX
      exact heX
    refine ⟨D, ?_, heD⟩
    rw [Finset.mem_erase]
    exact ⟨fun h => heCnot (by simpa [h] using heD), hD⟩

/-- A non-connecting component of a two-point subgraph has empty odd boundary. -/
theorem oddBoundary_eq_empty_of_mem_erase_connectingComponent
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {X D : Finset (Sym2 ι)} {i j : ι}
    (hX : X ∈ G.edgeFinset.powerset) (hij : i ≠ j)
    (hbd : oddBoundary X = ({i, j} : Finset ι))
    (hD : D ∈ (polymerDecomposition X).erase (connectingComponentOf G hX hij hbd)) :
    oddBoundary D = ∅ := by
  classical
  rw [Finset.mem_erase] at hD
  have hDmem : D ∈ polymerDecomposition X := hD.2
  have hDsub : oddBoundary D ⊆ ({i, j} : Finset ι) := by
    intro v hv
    have hvU : v ∈ (polymerDecomposition X).biUnion oddBoundary := by
      rw [Finset.mem_biUnion]
      exact ⟨D, hDmem, hv⟩
    rw [← oddBoundary_biUnion_polymerDecomposition X, hbd] at hvU
    exact hvU
  by_contra hne
  have hne' : (oddBoundary D).Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
  obtain ⟨v, hv⟩ := hne'
  have hDpair : oddBoundary D = ({i, j} : Finset ι) :=
    oddBoundary_eq_pair_of_subset_pair_of_mem
      (G := G) (C := D) (i := i) (j := j) (v := v)
      (polymerDecomposition_subset_edgeFinset G hX hDmem) hij hDsub hv
  have huniq : D = connectingComponentOf G hX hij hbd :=
    connectingComponentOf_unique G hX hij hbd ⟨hDmem, hDpair⟩
  exact hD.1 huniq

/-- A component with empty odd boundary is an even subgraph of `G`. -/
theorem isEvenSubgraph_of_mem_polymerDecomposition_of_oddBoundary_empty
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {X D : Finset (Sym2 ι)} (hX : X ∈ G.edgeFinset.powerset)
    (hDmem : D ∈ polymerDecomposition X) (hDbd : oddBoundary D = ∅) :
    IsEvenSubgraph G D where
  subset := Finset.mem_powerset.mp (polymerDecomposition_subset_edgeFinset G hX hDmem)
  even_degree v := by
    have hvnot : ¬ Odd ((D.filter (v ∈ ·)).card) := by
      intro hvodd
      have hvbd : v ∈ oddBoundary D := by
        rw [oddBoundary, Finset.mem_filter]
        exact ⟨Finset.mem_univ v, hvodd⟩
      rw [hDbd] at hvbd
      simp at hvbd
    exact Nat.not_odd_iff_even.mp hvnot

/-- The remainder after removing the chosen connecting component is an even subgraph. -/
theorem sdiff_connectingComponent_isEvenSubgraph
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {X : Finset (Sym2 ι)} {i j : ι}
    (hX : X ∈ G.edgeFinset.powerset) (hij : i ≠ j)
    (hbd : oddBoundary X = ({i, j} : Finset ι)) :
    IsEvenSubgraph G (X \ connectingComponentOf G hX hij hbd) := by
  classical
  let C := connectingComponentOf G hX hij hbd
  let Γ := (polymerDecomposition X).erase C
  have hΓcompat : IsCompatiblePolymerFamilyVertexDisjoint G Γ := by
    refine ⟨?_, ?_⟩
    · intro D hD
      have hDmem : D ∈ polymerDecomposition X := (Finset.mem_erase.mp hD).2
      have hDbd : oddBoundary D = ∅ := by
        simpa [C, Γ] using
          oddBoundary_eq_empty_of_mem_erase_connectingComponent
            (G := G) (X := X) (D := D) (i := i) (j := j) hX hij hbd hD
      refine ⟨?_, ?_, ?_⟩
      · exact isEvenSubgraph_of_mem_polymerDecomposition_of_oddBoundary_empty G hX hDmem hDbd
      · rw [mem_polymerDecomposition] at hDmem
        obtain ⟨e, he, hEq⟩ := hDmem
        rw [← hEq]
        exact ⟨e, self_mem_edgeComponent he⟩
      · rw [mem_polymerDecomposition] at hDmem
        obtain ⟨e, he, hEq⟩ := hDmem
        rw [← hEq]
        exact isEdgeConnected_edgeComponent e
    · intro D hD E hE hDE
      have hpairwise := polymerDecomposition_pairwise_vertexDisjoint (X := X)
      exact hpairwise
        (Finset.mem_coe.mpr ((Finset.mem_erase.mp (Finset.mem_coe.mp hD)).2))
        (Finset.mem_coe.mpr ((Finset.mem_erase.mp (Finset.mem_coe.mp hE)).2)) hDE
  have hbi : Γ.biUnion id = X \ C :=
    biUnion_erase_eq_sdiff_of_mem_polymerDecomposition
      (connectingComponentOf_mem G hX hij hbd)
  simpa [C, Γ, hbi] using hΓcompat.biUnion_isEvenSubgraph

/-- The chosen connecting component is vertex-disjoint from the remaining even subgraph. -/
theorem connectingComponent_vertexDisjoint_sdiff
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {X : Finset (Sym2 ι)} {i j : ι}
    (hX : X ∈ G.edgeFinset.powerset) (hij : i ≠ j)
    (hbd : oddBoundary X = ({i, j} : Finset ι)) :
    IsPolymerVertexDisjoint (connectingComponentOf G hX hij hbd)
      (X \ connectingComponentOf G hX hij hbd) := by
  classical
  let C := connectingComponentOf G hX hij hbd
  unfold IsPolymerVertexDisjoint
  rw [Finset.disjoint_left]
  intro v hvC hvY
  rw [mem_polymerSupport] at hvC hvY
  obtain ⟨eC, heC, hveC⟩ := hvC
  obtain ⟨eY, heY, hveY⟩ := hvY
  have hCmem : C ∈ polymerDecomposition X := connectingComponentOf_mem G hX hij hbd
  have hbi : ((polymerDecomposition X).erase C).biUnion id = X \ C :=
    biUnion_erase_eq_sdiff_of_mem_polymerDecomposition hCmem
  have heYΓ : eY ∈ ((polymerDecomposition X).erase C).biUnion id := by
    simpa [hbi] using heY
  rw [Finset.mem_biUnion] at heYΓ
  obtain ⟨D, hD, heYD⟩ := heYΓ
  rw [Finset.mem_erase] at hD
  have hpairwise := polymerDecomposition_pairwise_vertexDisjoint (X := X)
  have hdisj : IsPolymerVertexDisjoint D C :=
    hpairwise (Finset.mem_coe.mpr hD.2) (Finset.mem_coe.mpr hCmem) hD.1
  unfold IsPolymerVertexDisjoint at hdisj
  have hvD : v ∈ polymerSupport D := by
    rw [mem_polymerSupport]
    exact ⟨eY, heYD, hveY⟩
  have hvC' : v ∈ polymerSupport C := by
    rw [mem_polymerSupport]
    exact ⟨eC, heC, hveC⟩
  exact (Finset.disjoint_left.mp hdisj) hvD hvC'

/-- Forward map from a two-point subgraph to its connecting component and even remainder. -/
noncomputable def connectingForwardMap (G : SimpleGraph ι) [Fintype G.edgeSet]
    {i j : ι} (hij : i ≠ j) (X : Finset (Sym2 ι)) :
    Finset (Sym2 ι) × Finset (Sym2 ι) := by
  classical
  by_cases h : X ∈ twoPointSubgraphs G i j
  · exact
      (connectingComponentOf G (Finset.mem_filter.mp h).1 hij (Finset.mem_filter.mp h).2,
        X \ connectingComponentOf G (Finset.mem_filter.mp h).1 hij (Finset.mem_filter.mp h).2)
  · exact (∅, ∅)

/-- The forward map unfolds on its two-point domain. -/
theorem connectingForwardMap_eq (G : SimpleGraph ι) [Fintype G.edgeSet]
    {X : Finset (Sym2 ι)} {i j : ι} (hij : i ≠ j)
    (h : X ∈ twoPointSubgraphs G i j) :
    connectingForwardMap G hij X =
      (connectingComponentOf G (Finset.mem_filter.mp h).1 hij (Finset.mem_filter.mp h).2,
        X \ connectingComponentOf G (Finset.mem_filter.mp h).1 hij (Finset.mem_filter.mp h).2) := by
  classical
  unfold connectingForwardMap
  simp [h]

/-- The forward map lands in the connecting-pair superset. -/
theorem connectingForwardMap_mem_connectingPairs (G : SimpleGraph ι) [Fintype G.edgeSet]
    {X : Finset (Sym2 ι)} {i j : ι} (hij : i ≠ j)
    (h : X ∈ twoPointSubgraphs G i j) :
    connectingForwardMap G hij X ∈ connectingPairs G i j := by
  classical
  have hX : X ∈ G.edgeFinset.powerset := (Finset.mem_filter.mp h).1
  have hbd : oddBoundary X = ({i, j} : Finset ι) := (Finset.mem_filter.mp h).2
  let C := connectingComponentOf G hX hij hbd
  have hCmem : C ∈ polymerDecomposition X := connectingComponentOf_mem G hX hij hbd
  have hCpowerset : C ∈ G.edgeFinset.powerset := polymerDecomposition_subset_edgeFinset G hX hCmem
  have hCnonempty : C.Nonempty := by
    rw [mem_polymerDecomposition] at hCmem
    obtain ⟨e, he, hEq⟩ := hCmem
    rw [← hEq]
    exact ⟨e, self_mem_edgeComponent he⟩
  have hCconn : IsEdgeConnected C := by
    rw [mem_polymerDecomposition] at hCmem
    obtain ⟨e, he, hEq⟩ := hCmem
    rw [← hEq]
    exact isEdgeConnected_edgeComponent e
  have hCbd : oddBoundary C = ({i, j} : Finset ι) := connectingComponentOf_oddBoundary G hX hij hbd
  have hYeven : X \ C ∈ evenSubgraphs G := by
    rw [mem_evenSubgraphs]
    exact sdiff_connectingComponent_isEvenSubgraph G hX hij hbd
  have hdisj : IsPolymerVertexDisjoint C (X \ C) :=
    connectingComponent_vertexDisjoint_sdiff G hX hij hbd
  unfold connectingPairs connectingComponents
  rw [connectingForwardMap_eq G hij h]
  simp only [Finset.mem_filter, Finset.mem_product]
  exact ⟨⟨⟨hCpowerset, hCnonempty, hCconn, hCbd⟩, hYeven⟩, hdisj⟩

/-- The pair sum expands into an outer connecting-component sum and an avoiding even sum. -/
theorem connectingPairs_sum_eq (G : SimpleGraph ι) [Fintype G.edgeSet]
    (i j : ι) (r : ℝ) :
    (∑ p ∈ connectingPairs G i j, r ^ p.1.card * r ^ p.2.card) =
      ∑ C ∈ connectingComponents G i j,
        r ^ C.card * ∑ Y ∈ evenSubgraphsAvoiding G C, r ^ Y.card := by
  classical
  unfold connectingPairs evenSubgraphsAvoiding
  rw [Finset.sum_filter, Finset.sum_product]
  simp_rw [Finset.mul_sum, Finset.sum_filter]

/-- Norm-first upper bound for the two-point high-temperature numerator. -/
theorem htSubgraphSum_pair_norm_le (G : SimpleGraph ι) [Fintype G.edgeSet]
    {i j : ι} (hij : i ≠ j) (t : ℂ) :
    ‖htSubgraphSum G ({i, j} : Finset ι) t‖
      ≤ ∑ C ∈ connectingComponents G i j,
        ‖t‖ ^ C.card * ∑ Y ∈ evenSubgraphsAvoiding G C, ‖t‖ ^ Y.card := by
  classical
  let S := twoPointSubgraphs G i j
  let w : Finset (Sym2 ι) × Finset (Sym2 ι) → ℝ :=
    fun p => ‖t‖ ^ p.1.card * ‖t‖ ^ p.2.card
  have hnorm : ‖htSubgraphSum G ({i, j} : Finset ι) t‖ ≤ ∑ X ∈ S, ‖t‖ ^ X.card := by
    unfold htSubgraphSum
    change ‖∑ X ∈ S, t ^ X.card‖ ≤ ∑ X ∈ S, ‖t‖ ^ X.card
    calc
      ‖∑ X ∈ S, t ^ X.card‖ ≤ ∑ X ∈ S, ‖t ^ X.card‖ :=
        norm_sum_le S (fun X => t ^ X.card)
      _ = ∑ X ∈ S, ‖t‖ ^ X.card := by
        apply Finset.sum_congr rfl
        intro X hX
        rw [Complex.norm_pow]
  have hF_inj : Set.InjOn (connectingForwardMap G hij) (↑S : Set (Finset (Sym2 ι))) := by
    intro X hXS X' hX'S hEq
    have hX : X ∈ G.edgeFinset.powerset := (Finset.mem_filter.mp hXS).1
    have hbd : oddBoundary X = ({i, j} : Finset ι) := (Finset.mem_filter.mp hXS).2
    have hX' : X' ∈ G.edgeFinset.powerset := (Finset.mem_filter.mp hX'S).1
    have hbd' : oddBoundary X' = ({i, j} : Finset ι) := (Finset.mem_filter.mp hX'S).2
    have hEq' := hEq
    rw [connectingForwardMap_eq G hij hXS, connectingForwardMap_eq G hij hX'S] at hEq'
    have hCeq : connectingComponentOf G hX hij hbd = connectingComponentOf G hX' hij hbd' :=
      congrArg Prod.fst hEq'
    have hYeq : X \ connectingComponentOf G hX hij hbd =
        X' \ connectingComponentOf G hX' hij hbd' := congrArg Prod.snd hEq'
    have hsub : connectingComponentOf G hX hij hbd ⊆ X :=
      mem_polymerDecomposition_subset (connectingComponentOf_mem G hX hij hbd)
    have hsub' : connectingComponentOf G hX' hij hbd' ⊆ X' :=
      mem_polymerDecomposition_subset (connectingComponentOf_mem G hX' hij hbd')
    calc
      X = connectingComponentOf G hX hij hbd ∪ (X \ connectingComponentOf G hX hij hbd) :=
        (Finset.union_sdiff_of_subset hsub).symm
      _ = connectingComponentOf G hX' hij hbd' ∪
          (X' \ connectingComponentOf G hX' hij hbd') := by rw [hYeq, hCeq]
      _ = X' := Finset.union_sdiff_of_subset hsub'
  have hsum_eq : (∑ X ∈ S, ‖t‖ ^ X.card) =
      ∑ p ∈ S.image (connectingForwardMap G hij), w p := by
    rw [Finset.sum_image hF_inj]
    apply Finset.sum_congr rfl
    intro X hXS
    have hX : X ∈ G.edgeFinset.powerset := (Finset.mem_filter.mp hXS).1
    have hbd : oddBoundary X = ({i, j} : Finset ι) := (Finset.mem_filter.mp hXS).2
    have hsub : connectingComponentOf G hX hij hbd ⊆ X :=
      mem_polymerDecomposition_subset (connectingComponentOf_mem G hX hij hbd)
    rw [connectingForwardMap_eq G hij hXS]
    dsimp [w]
    have hcard : X.card = (connectingComponentOf G hX hij hbd).card +
        (X \ connectingComponentOf G hX hij hbd).card := by
      have h := Finset.card_sdiff_add_card_eq_card hsub
      omega
    rw [hcard, pow_add]
  have himage_sub : S.image (connectingForwardMap G hij) ⊆ connectingPairs G i j := by
    intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨X, hXS, rfl⟩ := hp
    exact connectingForwardMap_mem_connectingPairs G hij hXS
  have hsum_le : (∑ p ∈ S.image (connectingForwardMap G hij), w p) ≤
      ∑ p ∈ connectingPairs G i j, w p := by
    apply Finset.sum_le_sum_of_subset_of_nonneg himage_sub
    intro p hp hpnot
    exact mul_nonneg (pow_nonneg (norm_nonneg t) _) (pow_nonneg (norm_nonneg t) _)
  calc
    ‖htSubgraphSum G ({i, j} : Finset ι) t‖ ≤ ∑ X ∈ S, ‖t‖ ^ X.card := hnorm
    _ = ∑ p ∈ S.image (connectingForwardMap G hij), w p := hsum_eq
    _ ≤ ∑ p ∈ connectingPairs G i j, w p := hsum_le
    _ = ∑ C ∈ connectingComponents G i j,
        ‖t‖ ^ C.card * ∑ Y ∈ evenSubgraphsAvoiding G C, ‖t‖ ^ Y.card := by
      exact connectingPairs_sum_eq G i j ‖t‖

end IsingModel

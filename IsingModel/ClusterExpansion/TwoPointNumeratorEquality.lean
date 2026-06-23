import IsingModel.ClusterExpansion.TwoPointNumeratorBound

/-!
# Exact two-point numerator factorization

This file upgrades the injective norm bound for the high-temperature two-point numerator to the
exact complex-valued factorization.  The bijection sends a two-point subgraph `X` to its unique
connecting component `C` and the even remainder `X \ C`; the inverse sends a compatible pair
`(C, Y)` to `C ∪ Y`.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Even-remainder high-temperature subgraph sum avoiding the support of `C`. -/
noncomputable def htSubgraphSumAvoiding (G : SimpleGraph ι) [Fintype G.edgeSet]
    (C : Finset (Sym2 ι)) (t : ℂ) : ℂ :=
  ∑ Y ∈ evenSubgraphsAvoiding G C, t ^ Y.card

/-- Membership in the two-point subgraph finset is exactly the edge-subset condition together with
the odd-boundary equation. -/
theorem mem_twoPointSubgraphs (G : SimpleGraph ι) [Fintype G.edgeSet]
    {X : Finset (Sym2 ι)} {i j : ι} :
    X ∈ twoPointSubgraphs G i j ↔
      X ∈ G.edgeFinset.powerset ∧ oddBoundary X = ({i, j} : Finset ι) := by
  unfold twoPointSubgraphs
  rw [Finset.mem_filter]

omit [Fintype ι] [DecidableEq ι] in
/-- Edge-adjacency reachability is monotone under enlarging the ambient edge set. -/
theorem reflTransGen_edgeAdjacentIn_mono_finset
    {P Q : Finset (Sym2 ι)} (hPQ : P ⊆ Q) {e f : Sym2 ι}
    (h : Relation.ReflTransGen (edgeAdjacentIn P) e f) :
    Relation.ReflTransGen (edgeAdjacentIn Q) e f := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.tail ih
        ⟨hPQ hstep.1, hPQ hstep.2.1, hstep.2.2⟩

/-- A reachability chain in `C ∪ Y` starting from `C` stays in `C` when `C` and `Y` are
vertex-disjoint. -/
theorem reflTransGen_in_left_of_vertexDisjoint_union
    {C Y : Finset (Sym2 ι)} (hCY : IsPolymerVertexDisjoint C Y)
    {e f : Sym2 ι} (he : e ∈ C)
    (hchain : Relation.ReflTransGen (edgeAdjacentIn (C ∪ Y)) e f) :
    f ∈ C := by
  unfold IsPolymerVertexDisjoint at hCY
  induction hchain with
  | refl => exact he
  | tail _ hstep ih =>
      obtain ⟨_, hbU, v, hva, hvb⟩ := hstep
      rcases Finset.mem_union.mp hbU with hbC | hbY
      · exact hbC
      · exfalso
        have hvC : v ∈ polymerSupport C :=
          mem_polymerSupport.mpr ⟨_, ih, hva⟩
        have hvY : v ∈ polymerSupport Y :=
          mem_polymerSupport.mpr ⟨_, hbY, hvb⟩
        exact (Finset.disjoint_left.mp hCY) hvC hvY

/-- A nonempty edge-connected set `C` is a component of `C ∪ Y` when `Y` is vertex-disjoint from
`C`. -/
theorem mem_polymerDecomposition_of_isEdgeConnected_vertexDisjoint
    {C Y : Finset (Sym2 ι)}
    (hCne : C.Nonempty) (hCconn : IsEdgeConnected C)
    (hCY : IsPolymerVertexDisjoint C Y) :
    C ∈ polymerDecomposition (C ∪ Y) := by
  classical
  obtain ⟨e, heC⟩ := hCne
  rw [mem_polymerDecomposition]
  refine ⟨e, Finset.mem_union_left Y heC, ?_⟩
  apply Finset.Subset.antisymm
  · intro f hf
    rw [mem_edgeComponent] at hf
    exact reflTransGen_in_left_of_vertexDisjoint_union hCY heC hf.2
  · intro f hfC
    rw [mem_edgeComponent]
    refine ⟨Finset.mem_union_left Y hfC, ?_⟩
    exact reflTransGen_edgeAdjacentIn_mono_finset
      (fun g hg => Finset.mem_union_left Y hg) (hCconn e heC f hfC)

/-- An even subgraph has empty odd boundary. -/
theorem oddBoundary_eq_empty_of_isEvenSubgraph
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {Y : Finset (Sym2 ι)} (hY : IsEvenSubgraph G Y) :
    oddBoundary Y = ∅ := by
  ext v
  rw [oddBoundary, Finset.mem_filter]
  constructor
  · intro hv
    exact False.elim ((Nat.not_odd_iff_even.mpr (hY.even_degree v)) hv.2)
  · intro hv
    exact False.elim (Finset.notMem_empty v hv)

/-- Vertex-disjoint edge sets have additive odd boundary under union. -/
theorem oddBoundary_union_of_vertexDisjoint
    {C Y : Finset (Sym2 ι)} (hCY : IsPolymerVertexDisjoint C Y) :
    oddBoundary (C ∪ Y) = oddBoundary C ∪ oddBoundary Y := by
  classical
  unfold IsPolymerVertexDisjoint at hCY
  ext v
  by_cases hvC : v ∈ polymerSupport C
  · have hYempty : Y.filter (v ∈ ·) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro e he
      rw [Finset.mem_filter] at he
      have hvY : v ∈ polymerSupport Y :=
        mem_polymerSupport.mpr ⟨e, he.1, he.2⟩
      exact (Finset.disjoint_left.mp hCY) hvC hvY
    have hfilter : (C ∪ Y).filter (v ∈ ·) = C.filter (v ∈ ·) := by
      rw [Finset.filter_union, hYempty, Finset.union_empty]
    have hleft :
        v ∈ oddBoundary (C ∪ Y) ↔ Odd ((C.filter (v ∈ ·)).card) := by
      simp [oddBoundary, hfilter]
    have hright :
        v ∈ oddBoundary C ∪ oddBoundary Y ↔ Odd ((C.filter (v ∈ ·)).card) := by
      simp [oddBoundary, hYempty]
    exact hleft.trans hright.symm
  · have hCempty : C.filter (v ∈ ·) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro e he
      rw [Finset.mem_filter] at he
      exact hvC (mem_polymerSupport.mpr ⟨e, he.1, he.2⟩)
    have hfilter : (C ∪ Y).filter (v ∈ ·) = Y.filter (v ∈ ·) := by
      rw [Finset.filter_union, hCempty, Finset.empty_union]
    have hleft :
        v ∈ oddBoundary (C ∪ Y) ↔ Odd ((Y.filter (v ∈ ·)).card) := by
      simp [oddBoundary, hfilter]
    have hright :
        v ∈ oddBoundary C ∪ oddBoundary Y ↔ Odd ((Y.filter (v ∈ ·)).card) := by
      simp [oddBoundary, hCempty]
    exact hleft.trans hright.symm

/-- The inverse map from a connecting pair, `(C,Y) ↦ C ∪ Y`, lands in the two-point subgraphs. -/
theorem connectingPair_union_mem_twoPointSubgraphs
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {p : Finset (Sym2 ι) × Finset (Sym2 ι)} {i j : ι}
    (hp : p ∈ connectingPairs G i j) :
    p.1 ∪ p.2 ∈ twoPointSubgraphs G i j := by
  classical
  have hp' := hp
  unfold connectingPairs at hp'
  rw [Finset.mem_filter, Finset.mem_product] at hp'
  have hCmem : p.1 ∈ connectingComponents G i j := hp'.1.1
  have hYmem : p.2 ∈ evenSubgraphs G := hp'.1.2
  have hCY : IsPolymerVertexDisjoint p.1 p.2 := hp'.2
  have hCdata := hCmem
  unfold connectingComponents at hCdata
  rw [Finset.mem_filter] at hCdata
  have hYeven : IsEvenSubgraph G p.2 := mem_evenSubgraphs.mp hYmem
  rw [mem_twoPointSubgraphs]
  refine ⟨?_, ?_⟩
  · rw [Finset.mem_powerset]
    intro e he
    rcases Finset.mem_union.mp he with heC | heY
    · exact Finset.mem_powerset.mp hCdata.1 heC
    · exact hYeven.subset heY
  · have hYbd : oddBoundary p.2 = ∅ :=
      oddBoundary_eq_empty_of_isEvenSubgraph G hYeven
    rw [oddBoundary_union_of_vertexDisjoint hCY, hCdata.2.2.2, hYbd,
      Finset.union_empty]

/-- On a connecting pair, the forward map of the inverse union recovers the original pair. -/
theorem connectingForwardMap_union_pair_eq
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {p : Finset (Sym2 ι) × Finset (Sym2 ι)} {i j : ι}
    (hij : i ≠ j) (hp : p ∈ connectingPairs G i j) :
    connectingForwardMap G hij (p.1 ∪ p.2) = p := by
  classical
  have hp' := hp
  unfold connectingPairs at hp'
  rw [Finset.mem_filter, Finset.mem_product] at hp'
  have hCmem : p.1 ∈ connectingComponents G i j := hp'.1.1
  have hCY : IsPolymerVertexDisjoint p.1 p.2 := hp'.2
  have hCdata := hCmem
  unfold connectingComponents at hCdata
  rw [Finset.mem_filter] at hCdata
  have hUmem : p.1 ∪ p.2 ∈ twoPointSubgraphs G i j :=
    connectingPair_union_mem_twoPointSubgraphs G hp
  have hUpow : p.1 ∪ p.2 ∈ G.edgeFinset.powerset :=
    ((mem_twoPointSubgraphs G).mp hUmem).1
  have hUbd : oddBoundary (p.1 ∪ p.2) = ({i, j} : Finset ι) :=
    ((mem_twoPointSubgraphs G).mp hUmem).2
  have hCdecomp : p.1 ∈ polymerDecomposition (p.1 ∪ p.2) :=
    mem_polymerDecomposition_of_isEdgeConnected_vertexDisjoint
      hCdata.2.1 hCdata.2.2.1 hCY
  have huniq :
      p.1 = connectingComponentOf G hUpow hij hUbd :=
    connectingComponentOf_unique G hUpow hij hUbd
      ⟨hCdecomp, hCdata.2.2.2⟩
  have hedge : Disjoint p.1 p.2 := by
    simpa [IsPolymerCompatible] using hCY.toEdgeDisjoint
  rw [connectingForwardMap_eq G hij hUmem]
  rw [← huniq, Finset.union_sdiff_cancel_left hedge]

/-- The exact complex pair sum over two-point subgraphs equals the sum over connecting pairs. -/
theorem twoPointSubgraphs_sum_eq_connectingPairs_complex
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {i j : ι} (hij : i ≠ j) (t : ℂ) :
    (∑ X ∈ twoPointSubgraphs G i j, t ^ X.card) =
      ∑ p ∈ connectingPairs G i j, t ^ p.1.card * t ^ p.2.card := by
  classical
  refine Finset.sum_bij'
    (fun X _ => connectingForwardMap G hij X)
    (fun p _ => p.1 ∪ p.2)
    ?_ ?_ ?_ ?_ ?_
  · intro X hX
    exact connectingForwardMap_mem_connectingPairs G hij hX
  · intro p hp
    exact connectingPair_union_mem_twoPointSubgraphs G hp
  · intro X hX
    have hXpow : X ∈ G.edgeFinset.powerset := ((mem_twoPointSubgraphs G).mp hX).1
    have hXbd : oddBoundary X = ({i, j} : Finset ι) := ((mem_twoPointSubgraphs G).mp hX).2
    have hsub :
        connectingComponentOf G hXpow hij hXbd ⊆ X :=
      mem_polymerDecomposition_subset
        (connectingComponentOf_mem G hXpow hij hXbd)
    change (connectingForwardMap G hij X).1 ∪ (connectingForwardMap G hij X).2 = X
    rw [connectingForwardMap_eq G hij hX]
    exact Finset.union_sdiff_of_subset hsub
  · intro p hp
    exact connectingForwardMap_union_pair_eq G hij hp
  · intro X hX
    have hXpow : X ∈ G.edgeFinset.powerset := ((mem_twoPointSubgraphs G).mp hX).1
    have hXbd : oddBoundary X = ({i, j} : Finset ι) := ((mem_twoPointSubgraphs G).mp hX).2
    have hsub :
        connectingComponentOf G hXpow hij hXbd ⊆ X :=
      mem_polymerDecomposition_subset
        (connectingComponentOf_mem G hXpow hij hXbd)
    have hcard :
        X.card =
          (connectingComponentOf G hXpow hij hXbd).card +
            (X \ connectingComponentOf G hXpow hij hXbd).card := by
      have h := Finset.card_sdiff_add_card_eq_card hsub
      omega
    change t ^ X.card
        = t ^ (connectingForwardMap G hij X).1.card * t ^ (connectingForwardMap G hij X).2.card
    rw [connectingForwardMap_eq G hij hX, hcard, pow_add]

/-- The connecting-pair sum factors into the outer connecting-component sum and the avoiding
even-subgraph inner sum, for complex activity `t`. -/
theorem connectingPairs_sum_eq_complex
    (G : SimpleGraph ι) [Fintype G.edgeSet] (i j : ι) (t : ℂ) :
    (∑ p ∈ connectingPairs G i j, t ^ p.1.card * t ^ p.2.card) =
      ∑ C ∈ connectingComponents G i j,
        t ^ C.card * ∑ Y ∈ evenSubgraphsAvoiding G C, t ^ Y.card := by
  classical
  unfold connectingPairs evenSubgraphsAvoiding
  rw [Finset.sum_filter, Finset.sum_product]
  simp_rw [Finset.mul_sum, Finset.sum_filter]

/-- **Complex equality factorization of the two-point numerator**: the two-point high-temperature
subgraph sum factors through the unique connecting component and an even remainder avoiding it. -/
theorem htSubgraphSum_pair_eq_sum_connectingComponent
    (G : SimpleGraph ι) [Fintype G.edgeSet] {i j : ι}
    (hij : i ≠ j) (t : ℂ) :
    htSubgraphSum G ({i, j} : Finset ι) t
      = ∑ C ∈ connectingComponents G i j,
          t ^ C.card * htSubgraphSumAvoiding G C t := by
  classical
  calc
    htSubgraphSum G ({i, j} : Finset ι) t
        = ∑ X ∈ twoPointSubgraphs G i j, t ^ X.card := by
          rw [htSubgraphSum]
          refine Finset.sum_congr ?_ (fun _ _ => rfl)
          ext X
          simp only [Finset.mem_filter, mem_twoPointSubgraphs]
    _ = ∑ p ∈ connectingPairs G i j, t ^ p.1.card * t ^ p.2.card :=
          twoPointSubgraphs_sum_eq_connectingPairs_complex G hij t
    _ = ∑ C ∈ connectingComponents G i j,
          t ^ C.card * ∑ Y ∈ evenSubgraphsAvoiding G C, t ^ Y.card :=
          connectingPairs_sum_eq_complex G i j t
    _ = ∑ C ∈ connectingComponents G i j,
          t ^ C.card * htSubgraphSumAvoiding G C t := by
          apply Finset.sum_congr rfl
          intro C _
          rfl

end IsingModel

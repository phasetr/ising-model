import IsingModel.ClusterExpansion.Basic
import IsingModel.ClusterExpansion.SourceGeneratingFunction
import IsingModel.ComplexAnalyticity.CorrelationRatioForm
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Capstone prerequisites for the two-point cluster-expansion bound

This file collects two small prerequisites for the final high-temperature two-point capstone:
a support-cardinality estimate for connected edge sets and a public `htSubgraphSum` wrapper around
an existing complex high-temperature ratio theorem whose internal subgraph sum is private.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- Vertices lying on the same edge of `C` are reachable in the graph on a prescribed support
subtype whose edges are the subtype-lifts of edges of `C`. -/
private lemma same_edge_reachable_in_supportGraph
    (C : Finset (Sym2 ι)) {e : Sym2 ι} (he : e ∈ C)
    (S : Finset ι)
    (H : SimpleGraph {v // v ∈ S})
    (hH : H = SimpleGraph.fromEdgeSet
      {f : Sym2 {v // v ∈ S} | Sym2.map Subtype.val f ∈ (C : Set (Sym2 ι))})
    (x y : {v // v ∈ S}) (hx : x.1 ∈ e) (hy : y.1 ∈ e) :
    H.Reachable x y := by
  classical
  subst hH
  by_cases hxy : x = y
  · subst hxy
    exact SimpleGraph.Reachable.refl x
  · have hxyval : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
    have he_eq : e = s(x.1, y.1) := (Sym2.mem_and_mem_iff hxyval).mp ⟨hx, hy⟩
    have hadj : (SimpleGraph.fromEdgeSet
        {f : Sym2 {v // v ∈ S} | Sym2.map Subtype.val f ∈ (C : Set (Sym2 ι))}).Adj x y := by
      rw [SimpleGraph.fromEdgeSet_adj]
      constructor
      · change Sym2.map Subtype.val s(x, y) ∈ (C : Set (Sym2 ι))
        simpa [Sym2.map_mk, ← he_eq] using he
      · exact hxy
    exact SimpleGraph.Adj.reachable hadj

/-- An edge-adjacency chain in `C` lifts to vertex reachability in the support graph of `C`. -/
private lemma edge_chain_reachable_in_supportGraph
    (C : Finset (Sym2 ι))
    (S : Finset ι) (hS : S = polymerSupport C)
    (H : SimpleGraph {v // v ∈ S})
    (hH : H = SimpleGraph.fromEdgeSet
      {f : Sym2 {v // v ∈ S} | Sym2.map Subtype.val f ∈ (C : Set (Sym2 ι))})
    {e f : Sym2 ι} (he : e ∈ C) (hf : f ∈ C)
    (hchain : Relation.ReflTransGen (edgeAdjacentIn C) e f)
    (x y : {v // v ∈ S}) (hx : x.1 ∈ e) (hy : y.1 ∈ f) :
    H.Reachable x y := by
  classical
  induction hchain generalizing y with
  | refl =>
      exact same_edge_reachable_in_supportGraph C he S H hH x y hx hy
  | tail h_chain h_step ih =>
      rename_i a b
      rcases h_step with ⟨haC, hbC, v, hva, hvb⟩
      have hvS : v ∈ S := by
        rw [hS]
        exact mem_polymerSupport.mpr ⟨a, haC, hva⟩
      let z : {v // v ∈ S} := ⟨v, hvS⟩
      have hxz : H.Reachable x z := ih haC z hva
      have hzy : H.Reachable z y :=
        same_edge_reachable_in_supportGraph C hbC S H hH z y hvb hy
      exact SimpleGraph.Reachable.trans hxz hzy

/-- A connected finite edge set has support cardinality at most its edge cardinality plus one. -/
theorem polymerSupport_card_le_card_add_one_of_isEdgeConnected
    (G : SimpleGraph ι) [Fintype G.edgeSet] {C : Finset (Sym2 ι)}
    (hCG : C ⊆ G.edgeFinset) (hCne : C.Nonempty) (hconn : IsEdgeConnected C) :
    (polymerSupport C).card ≤ C.card + 1 := by
  classical
  have _hCG_used : C ⊆ G.edgeFinset := hCG
  let S : Finset ι := polymerSupport C
  let H : SimpleGraph {v // v ∈ S} := SimpleGraph.fromEdgeSet
    {f : Sym2 {v // v ∈ S} | Sym2.map Subtype.val f ∈ (C : Set (Sym2 ι))}
  have hS : S = polymerSupport C := rfl
  have hH : H = SimpleGraph.fromEdgeSet
      {f : Sym2 {v // v ∈ S} | Sym2.map Subtype.val f ∈ (C : Set (Sym2 ι))} := rfl
  have hNonempty : Nonempty {v // v ∈ S} := by
    rcases hCne with ⟨e, he⟩
    exact ⟨⟨e.out.1, by
      rw [hS]
      exact mem_polymerSupport.mpr ⟨e, he, Sym2.out_fst_mem e⟩⟩⟩
  have hHpre : H.Preconnected := by
    intro x y
    have hxS : x.1 ∈ polymerSupport C := by simpa only [S] using x.2
    have hyS : y.1 ∈ polymerSupport C := by simpa only [S] using y.2
    rcases mem_polymerSupport.mp hxS with ⟨ex, hex, hxex⟩
    rcases mem_polymerSupport.mp hyS with ⟨ey, hey, hyey⟩
    exact edge_chain_reachable_in_supportGraph C S hS H hH hex hey
      (hconn ex hex ey hey) x y hxex hyey
  letI : Nonempty {v // v ∈ S} := hNonempty
  have hHconn : H.Connected := SimpleGraph.Connected.mk hHpre
  have hHcard := hHconn.card_vert_le_card_edgeSet_add_one
  have hEdgeCard : Nat.card H.edgeSet ≤ C.card := by
    let edgeMap : H.edgeSet → Sym2 ι := fun e => Sym2.map Subtype.val (e : Sym2 {v // v ∈ S})
    let edgeImage : Finset (Sym2 ι) :=
      (Finset.univ : Finset H.edgeSet).image edgeMap
    have hImageCard : Nat.card H.edgeSet = edgeImage.card := by
      rw [Nat.card_eq_fintype_card]
      change Fintype.card H.edgeSet = edgeImage.card
      rw [← Finset.card_univ]
      have hci : edgeImage.card = (Finset.univ : Finset H.edgeSet).card := by
        apply Finset.card_image_of_injOn
        intro a _ b _ hab
        apply Subtype.ext
        exact Sym2.map.injective Subtype.val_injective hab
      exact hci.symm
    have hImageSub : edgeImage ⊆ C := by
      intro e he
      rw [Finset.mem_image] at he
      rcases he with ⟨a, _, rfl⟩
      have ha : (a : Sym2 {v // v ∈ S}) ∈
          ({f : Sym2 {v // v ∈ S} | Sym2.map Subtype.val f ∈ (C : Set (Sym2 ι))} \
            Sym2.diagSet) := by
        simpa [H] using (a : H.edgeSet).property
      exact ha.1
    rw [hImageCard]
    exact Finset.card_le_card hImageSub
  calc
    (polymerSupport C).card = Nat.card {v // v ∈ S} := by
      rw [Nat.card_eq_fintype_card]
      simp [S]
    _ ≤ Nat.card H.edgeSet + 1 := hHcard
    _ ≤ C.card + 1 := Nat.add_le_add_right hEdgeCard 1

/-- The odd-boundary equation `∂X = A` is equivalent to the inline FV parity filter used in the
closed high-temperature expansion. -/
theorem oddBoundary_eq_iff_inline_even_filter (A : Finset ι) (X : Finset (Sym2 ι)) :
    oddBoundary X = A ↔
      ∀ v : ι, Even ((if v ∈ A then (1 : ℕ) else 0) + (X.filter (v ∈ ·)).card) := by
  unfold oddBoundary
  constructor
  · intro h v
    by_cases hv : v ∈ A
    · have hodd : Odd ((X.filter (v ∈ ·)).card) := by
        have hv' : v ∈ Finset.univ.filter (fun v => Odd ((X.filter (v ∈ ·)).card)) := by
          rw [h]
          exact hv
        exact (Finset.mem_filter.mp hv').2
      have heven1 : Even (1 + (X.filter (v ∈ ·)).card) :=
        (show Even (1 + (X.filter (v ∈ ·)).card) ↔ Odd ((X.filter (v ∈ ·)).card) from by
          rw [Nat.even_add]
          simp).mpr hodd
      simpa [hv] using heven1
    · have hnotodd : ¬ Odd ((X.filter (v ∈ ·)).card) := by
        intro hodd
        have hv' : v ∈ Finset.univ.filter (fun v => Odd ((X.filter (v ∈ ·)).card)) := by
          simp [hodd]
        exact hv (by simpa [h] using hv')
      simpa [hv] using (Nat.not_odd_iff_even.mp hnotodd)
  · intro h
    ext v
    by_cases hv : v ∈ A
    · have hev := h v
      have hodd : Odd ((X.filter (v ∈ ·)).card) := by
        exact (show Even (1 + (X.filter (v ∈ ·)).card) ↔ Odd ((X.filter (v ∈ ·)).card) from by
          rw [Nat.even_add]
          simp).mp (by simpa [hv] using hev)
      simp [hodd, hv]
    · have hev := h v
      have heven : Even ((X.filter (v ∈ ·)).card) := by simpa [hv] using hev
      have hnotodd : ¬ Odd ((X.filter (v ∈ ·)).card) := Nat.not_odd_iff_even.mpr heven
      simp [hnotodd, hv]

/-- Public `htSubgraphSum` form of the complex high-temperature expansion at zero field. -/
theorem correlationComplex_high_temp_expansion_h_zero_closed_on_ball_htSubgraphSum
    (G : SimpleGraph ι) [Fintype G.edgeSet] (A : Finset ι) (J : ℝ) :
    ∃ r > 0, ∀ β ∈ Metric.ball (0 : ℂ) r,
      correlationComplex G A (J : ℂ) 0 β =
        htSubgraphSum G A (Complex.tanh (β * (J : ℂ))) /
          htSubgraphSum G ∅ (Complex.tanh (β * (J : ℂ))) := by
  classical
  obtain ⟨r, hr, hratio⟩ := correlationComplex_high_temp_expansion_h_zero_closed_on_ball G A J
  refine ⟨r, hr, fun β hβ => ?_⟩
  rw [hratio β hβ]
  change
    (∑ X ∈ G.edgeFinset.powerset.filter
        (fun X => ∀ v : ι,
          Even ((if v ∈ A then (1 : ℕ) else 0) + (X.filter (v ∈ ·)).card)),
        Complex.tanh (β * (J : ℂ)) ^ X.card) /
      (∑ X ∈ G.edgeFinset.powerset.filter
        (fun X => ∀ v : ι,
          Even ((if v ∈ (∅ : Finset ι) then (1 : ℕ) else 0) + (X.filter (v ∈ ·)).card)),
        Complex.tanh (β * (J : ℂ)) ^ X.card)
      = htSubgraphSum G A (Complex.tanh (β * (J : ℂ))) /
        htSubgraphSum G ∅ (Complex.tanh (β * (J : ℂ)))
  have hAfilter :
      G.edgeFinset.powerset.filter
        (fun X => ∀ v : ι,
          Even ((if v ∈ A then (1 : ℕ) else 0) + (X.filter (v ∈ ·)).card)) =
      G.edgeFinset.powerset.filter (fun X => oddBoundary X = A) := by
    apply Finset.filter_congr
    intro X _
    exact (oddBoundary_eq_iff_inline_even_filter A X).symm
  have h0filter :
      G.edgeFinset.powerset.filter
        (fun X => ∀ v : ι,
          Even ((if v ∈ (∅ : Finset ι) then (1 : ℕ) else 0) + (X.filter (v ∈ ·)).card)) =
      G.edgeFinset.powerset.filter (fun X => oddBoundary X = (∅ : Finset ι)) := by
    apply Finset.filter_congr
    intro X _
    exact (oddBoundary_eq_iff_inline_even_filter (∅ : Finset ι) X).symm
  unfold htSubgraphSum
  rw [hAfilter, h0filter]

end IsingModel

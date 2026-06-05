import IsingModel.Conditioning.EdgeSetDistance
import Mathlib.Combinatorics.SimpleGraph.Walks.Decomp

/-!
# Closed walk traversing each edge of a connected edge set (FV Lemma 3.38)

FV §3.7.3 Lemma 3.38: a connected edge set admits a closed walk crossing each of its edges
exactly twice (length `2|X|`). This is the injection underlying the counting bound
`#{connected edge sets C ∋ z, |C|=ℓ} ≤ #{closed walks of length 2ℓ from z} ≤ (2d)^{2ℓ}`,
the final input to the high-temperature `m*(β)=0` (Issue #3613).

This file develops the supporting combinatorics:

* `exists_boundary_edge` — a connected edge set has, across any proper nonempty subset, an
  edge incident to the subset (the connectivity frontier).
* `exists_adj_of_mem_edge` — extract a directed adjacency from an edge through a vertex.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.3, Lemma 3.38, p. 117.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
/-- **Adjacency from an edge through a vertex**: if `e ∈ G.edgeSet` and `v ∈ e`, then the
other endpoint `w := Sym2.Mem.other` satisfies `G.Adj v w` and `e = s(v, w)`. -/
theorem exists_adj_of_mem_edge {G : SimpleGraph ι} {e : Sym2 ι} (he : e ∈ G.edgeSet)
    {v : ι} (hv : v ∈ e) :
    ∃ w : ι, G.Adj v w ∧ e = s(v, w) := by
  refine ⟨Sym2.Mem.other hv, ?_, (Sym2.other_spec hv).symm⟩
  have : s(v, Sym2.Mem.other hv) ∈ G.edgeSet := (Sym2.other_spec hv).symm ▸ he
  rwa [SimpleGraph.mem_edgeSet] at this

omit [DecidableEq ι] in
/-- **Connectivity frontier**: if `X` is edge-connected and `P ⊆ X` is a proper nonempty
subset, then some edge `e ∈ X \ P` is incident (shares a vertex) to some edge `f ∈ P`. The
combinatorial heart of the closed-walk construction: the prefix `P` can always be grown. -/
theorem exists_boundary_edge {X P : Finset (Sym2 ι)} (hconn : IsEdgeConnected X)
    (hPX : P ⊆ X) (hPne : P.Nonempty) (hPneX : P ≠ X) :
    ∃ e ∈ X, e ∉ P ∧ ∃ f ∈ P, ∃ v : ι, v ∈ e ∧ v ∈ f := by
  classical
  -- some edge of X lies outside P
  obtain ⟨e', he'X, he'P⟩ : ∃ e' ∈ X, e' ∉ P := by
    by_contra h
    push Not at h
    exact hPneX (Finset.Subset.antisymm hPX (fun x hx => h x hx))
  obtain ⟨f₀, hf₀⟩ := hPne
  -- walk the connectivity chain from `f₀ ∈ P` to `e' ∉ P`, find where it leaves `P`
  have hchain := hconn f₀ (hPX hf₀) e' he'X
  have key : ∀ {a b : Sym2 ι}, Relation.ReflTransGen (edgeAdjacentIn X) a b →
      a ∈ P → b ∉ P → ∃ e ∈ X, e ∉ P ∧ ∃ f ∈ P, ∃ v : ι, v ∈ e ∧ v ∈ f := by
    intro a b hab
    induction hab with
    | refl => intro ha hb; exact absurd ha hb
    | tail _ hcb ih =>
      rename_i c d _
      intro ha hd
      by_cases hc : c ∈ P
      · obtain ⟨_, hdX, v, hvc, hvd⟩ := hcb
        exact ⟨d, hdX, hd, c, hc, v, hvd, hvc⟩
      · exact ih ha hc
  exact key hchain hf₀ he'P

omit [DecidableEq ι] in
/-- **Edge-adjacency is monotone**: a shared-vertex relation in `P` persists in any
superset `Q`. -/
theorem edgeAdjacentIn_mono {P Q : Finset (Sym2 ι)} (hPQ : P ⊆ Q) {g h : Sym2 ι}
    (hgh : edgeAdjacentIn P g h) : edgeAdjacentIn Q g h := by
  obtain ⟨hg, hh, v, hvg, hvh⟩ := hgh
  exact ⟨hPQ hg, hPQ hh, v, hvg, hvh⟩

/-- **Inserting an incident edge preserves edge-connectedness**: if `P` is edge-connected
and the new edge `e` shares a vertex with some edge of `P`, then `insert e P` is
edge-connected. -/
theorem isEdgeConnected_insert {P : Finset (Sym2 ι)} {e : Sym2 ι}
    (hP : IsEdgeConnected P) (htouch : ∃ f ∈ P, ∃ v : ι, v ∈ e ∧ v ∈ f) :
    IsEdgeConnected (insert e P) := by
  classical
  obtain ⟨f₀, hf₀P, v₀, hv₀e, hv₀f₀⟩ := htouch
  have hsub : P ⊆ insert e P := Finset.subset_insert e P
  -- every edge of `insert e P` is connected to `f₀`
  have hto : ∀ g ∈ insert e P,
      Relation.ReflTransGen (edgeAdjacentIn (insert e P)) g f₀ := by
    intro g hg
    rcases Finset.mem_insert.mp hg with heq | hgP
    · rw [heq]
      exact Relation.ReflTransGen.single
        ⟨Finset.mem_insert_self e P, hsub hf₀P, v₀, hv₀e, hv₀f₀⟩
    · exact (hP g hgP f₀ hf₀P).mono (fun _ _ h => edgeAdjacentIn_mono hsub h)
  intro g₁ hg₁ g₂ hg₂
  exact (hto g₁ hg₁).trans
    (reflTransGen_edgeAdjacentIn_symmetric (insert e P) (hto g₂ hg₂))

/-- **FV Lemma 3.38**: a connected edge set `X` (with non-diagonal edges) admits a closed
walk from any incident vertex `z` crossing each edge exactly twice — its edge set is `X`
and its length is `2|X|`. Built by growing a connected prefix one incident edge at a time,
splicing a `v → w → v` detour at the first visit to the shared vertex `v`. -/
theorem exists_closed_walk_of_edgeConnected (X : Finset (Sym2 ι))
    (hXnd : ∀ e ∈ X, ¬ e.IsDiag) (hconn : IsEdgeConnected X)
    {z : ι} {e₀ : Sym2 ι} (he₀ : e₀ ∈ X) (hz : z ∈ e₀) :
    ∃ w : (SimpleGraph.fromEdgeSet (↑X : Set (Sym2 ι))).Walk z z,
      w.edges.toFinset = X ∧ w.length = 2 * X.card := by
  classical
  set G := SimpleGraph.fromEdgeSet (↑X : Set (Sym2 ι)) with hG
  have hmemG : ∀ {e : Sym2 ι}, e ∈ X → e ∈ G.edgeSet := by
    intro e he
    rw [hG, SimpleGraph.edgeSet_fromEdgeSet]
    exact ⟨by exact_mod_cast he, hXnd e he⟩
  obtain ⟨z', hadj₀, he₀eq⟩ := exists_adj_of_mem_edge (hmemG he₀) hz
  -- grow a connected prefix `P` until it equals `X`
  suffices H : ∀ m : ℕ, ∀ P : Finset (Sym2 ι), P ⊆ X → IsEdgeConnected P → e₀ ∈ P →
      (X \ P).card = m → ∀ w : G.Walk z z, w.edges.toFinset = P → w.length = 2 * P.card →
      ∃ w' : G.Walk z z, w'.edges.toFinset = X ∧ w'.length = 2 * X.card by
    refine H (X \ {e₀}).card {e₀} (Finset.singleton_subset_iff.mpr he₀) ?_
      (Finset.mem_singleton_self e₀) rfl
      (SimpleGraph.Walk.cons hadj₀ (SimpleGraph.Walk.cons hadj₀.symm SimpleGraph.Walk.nil))
      ?_ ?_
    · intro a ha b hb
      rw [Finset.mem_singleton] at ha hb; subst ha; subst hb; exact Relation.ReflTransGen.refl
    · have hcomm : s(z', z) = e₀ := by rw [Sym2.eq_swap, ← he₀eq]
      simp only [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, ← he₀eq, hcomm,
        List.toFinset_cons, List.toFinset_nil]
      simp
    · simp [SimpleGraph.Walk.length_cons]
  intro m
  induction m with
  | zero =>
    intro P hPX _ _ hcard w hwP hwlen
    have hXP : X = P := by
      have he : X \ P = ∅ := Finset.card_eq_zero.mp hcard
      refine Finset.Subset.antisymm (fun x hx => ?_) hPX
      by_contra hxP
      exact (Finset.notMem_empty x) (he ▸ Finset.mem_sdiff.mpr ⟨hx, hxP⟩)
    exact ⟨w, hXP ▸ hwP, hXP ▸ hwlen⟩
  | succ m ih =>
    intro P hPX hPconn he₀P hcard w hwP hwlen
    have hPneX : P ≠ X := by
      rintro rfl
      rw [Finset.sdiff_self, Finset.card_empty] at hcard
      exact (Nat.succ_ne_zero m) hcard.symm
    obtain ⟨e, heX, heP, f, hfP, v, hve, hvf⟩ := exists_boundary_edge hconn hPX ⟨e₀, he₀P⟩ hPneX
    have hfedges : f ∈ w.edges := by rw [← List.mem_toFinset, hwP]; exact hfP
    have hvsupp : v ∈ w.support := SimpleGraph.Walk.mem_support_of_mem_edges hfedges hvf
    obtain ⟨v', hadj, heeq⟩ := exists_adj_of_mem_edge (hmemG heX) hve
    set newwalk : G.Walk z z :=
      (w.takeUntil v hvsupp).append
        ((SimpleGraph.Walk.cons hadj (SimpleGraph.Walk.cons hadj.symm SimpleGraph.Walk.nil)).append
          (w.dropUntil v hvsupp)) with hnw
    -- edge-set: P with `e` inserted
    have htd : (w.takeUntil v hvsupp).edges ++ (w.dropUntil v hvsupp).edges = w.edges := by
      rw [← SimpleGraph.Walk.edges_append, SimpleGraph.Walk.take_spec]
    have hnew_edges : newwalk.edges.toFinset = insert e P := by
      have hcomm : s(v', v) = e := by rw [Sym2.eq_swap, ← heeq]
      rw [hnw]
      simp only [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_cons,
        SimpleGraph.Walk.edges_nil, ← heeq, hcomm, List.toFinset_append, List.toFinset_cons,
        List.toFinset_nil]
      ext x
      have key : (x ∈ (w.takeUntil v hvsupp).edges.toFinset ∨
          x ∈ (w.dropUntil v hvsupp).edges.toFinset) ↔ x ∈ P := by
        rw [← Finset.mem_union, ← List.toFinset_append, htd, hwP]
      simp only [Finset.mem_union, Finset.mem_insert, Finset.notMem_empty, or_false]
      tauto
    -- length: w.length + 2
    have hnew_len : newwalk.length = 2 * (insert e P).card := by
      rw [hnw, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_append,
        SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil]
      have hlen_td : (w.takeUntil v hvsupp).length + (w.dropUntil v hvsupp).length = w.length := by
        rw [← SimpleGraph.Walk.length_append, SimpleGraph.Walk.take_spec]
      rw [Finset.card_insert_of_notMem heP]
      omega
    -- recurse on `insert e P`
    refine ih (insert e P) (Finset.insert_subset heX hPX)
      (isEdgeConnected_insert hPconn ⟨f, hfP, v, hve, hvf⟩)
      (Finset.mem_insert_of_mem he₀P) ?_ newwalk hnew_edges hnew_len
    have he_sdiff : e ∈ X \ P := Finset.mem_sdiff.mpr ⟨heX, heP⟩
    have hcard' : (X \ insert e P).card = (X \ P).card - 1 := by
      rw [Finset.sdiff_insert, Finset.card_erase_of_mem he_sdiff]
    omega

end IsingModel

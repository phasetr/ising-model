import IsingModel.Peierls.DropletInjective

/-!
# Crossing parity of the cut (FV §3.7.2)

A walk crosses the edge cut `cutEdges G S` an even number of times iff its two endpoints lie on
the same side of `S`. This discrete Jordan / winding-parity fact is the combinatorial heart of
the Peierls "surrounding contour" extraction: a walk from the enclosed origin out to a far
vertex *outside* the droplet crosses the boundary an odd number of times, so it must traverse a
cut edge — detecting that the origin is enclosed.

* `cutCrossings` — the number of cut edges a walk traverses (with multiplicity).
* `even_cutCrossings_iff` — `Even (#crossings of w) ↔ (u ∈ S ↔ v ∈ S)`.
* `odd_cutCrossings_of_mem_not_mem` — crossing an odd number of times when endpoints differ.
* `exists_mem_edges_mem_cutEdges` — a walk from inside `S` to outside `S` traverses a cut edge.
* `cutEdges_nonempty_of_reachable_not_mem` — separation forces a nonempty cut.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset SimpleGraph

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The number of times a walk `w` traverses a cut edge of `S` (with multiplicity). -/
noncomputable def cutCrossings (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet]
    (S : Finset ι) {u v : ι} (w : G.Walk u v) : ℕ :=
  w.edges.countP (fun e => decide (e ∈ cutEdges G S))

omit [Fintype ι] in
/-- **Crossing parity**: a walk traverses the cut of `S` an even number of times iff its
endpoints lie on the same side of `S`. The discrete winding-parity identity. -/
theorem even_cutCrossings_iff (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet]
    (S : Finset ι) {u v : ι} (w : G.Walk u v) :
    Even (cutCrossings G S w) ↔ (u ∈ S ↔ v ∈ S) := by
  unfold cutCrossings
  induction w with
  | nil => simp
  | @cons a x t hadj w' ih =>
    rw [SimpleGraph.Walk.edges_cons, List.countP_cons]
    split_ifs with hif
    · -- crossing edge: `a` and `x` are on opposite sides
      have hcross : s(a, x) ∈ cutEdges G S := of_decide_eq_true hif
      have hax := (mem_cutEdges_iff.mp hcross).2
      rw [Nat.even_add_one, ih]
      tauto
    · -- non-crossing edge: `a` and `x` are on the same side
      have hcross : s(a, x) ∉ cutEdges G S := fun h => hif (decide_eq_true h)
      have hax : (a ∈ S) ↔ (x ∈ S) := by
        rw [mem_cutEdges_iff] at hcross
        push Not at hcross
        have := hcross hadj
        tauto
      rw [add_zero, ih]
      tauto

omit [Fintype ι] in
/-- **Odd crossing when endpoints differ**: a walk from inside `S` to outside `S` crosses the
cut an odd number of times. -/
theorem odd_cutCrossings_of_mem_not_mem (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (S : Finset ι) {u v : ι} (hu : u ∈ S) (hv : v ∉ S) (w : G.Walk u v) :
    Odd (cutCrossings G S w) := by
  have hne : ¬ Even (cutCrossings G S w) := by
    rw [even_cutCrossings_iff]; simp [hu, hv]
  exact Nat.not_even_iff_odd.mp hne

omit [Fintype ι] in
/-- **A walk from inside `S` to outside `S` traverses a cut edge**: among the edges of any walk
from `u ∈ S` to `v ∉ S` there is a cut edge of `S`, located on the walk. -/
theorem exists_mem_edges_mem_cutEdges (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (S : Finset ι) {u v : ι} (hu : u ∈ S) (hv : v ∉ S) (w : G.Walk u v) :
    ∃ e ∈ w.edges, e ∈ cutEdges G S := by
  by_contra hcon
  have hzero : cutCrossings G S w = 0 := by
    unfold cutCrossings
    rw [List.countP_eq_zero]
    intro e he hp
    exact hcon ⟨e, he, of_decide_eq_true hp⟩
  exact (odd_cutCrossings_of_mem_not_mem G S hu hv w).pos.ne' hzero

omit [Fintype ι] in
/-- **Separation forces a nonempty cut**: if `u ∈ S`, `v ∉ S`, and `u` reaches `v`, then the
cut of `S` is nonempty. -/
theorem cutEdges_nonempty_of_reachable_not_mem (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (S : Finset ι) {u v : ι} (hu : u ∈ S) (hv : v ∉ S)
    (h : G.Reachable u v) : (cutEdges G S).Nonempty := by
  obtain ⟨w⟩ := h
  obtain ⟨e, _, he⟩ := exists_mem_edges_mem_cutEdges G S hu hv w
  exact ⟨e, he⟩

end IsingModel

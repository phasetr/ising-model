import IsingModel.Peierls.LiftBoxCut

/-!
# Membership characterization of the lifted box cut (FV §3.7.2)

The lifted box cut `liftBoxCut Λ F` is `(cutEdges (box) F).image (Sym2.map Subtype.val)`. An ambient
edge lies in it exactly when it is the lift of a box edge joining an `F`-vertex to a
non-`F`-vertex. This oriented characterization mirrors `mem_dartPrimalCut_iff`, so the two can be
matched in the dart–cut box bridge.

* `mem_liftBoxCut_iff` — `e ∈ liftBoxCut Λ F ↔` `e` lifts a box cut edge of `F`.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {Λ : Finset (Fin 2 → ℤ)} {F : Finset ↑Λ}

/-- **Membership in the lifted box cut**: an ambient edge lies in `liftBoxCut Λ F` iff it is the
subtype lift `s(↑a, ↑b)` of a box edge with `a ∈ F` and `b ∉ F`. -/
theorem mem_liftBoxCut_iff {e : Sym2 (Fin 2 → ℤ)} :
    e ∈ liftBoxCut Λ F ↔
      ∃ a b : ↑Λ, e = s(↑a, ↑b) ∧ (latticeGraph 2).Adj ↑a ↑b ∧ a ∈ F ∧ b ∉ F := by
  classical
  rw [liftBoxCut, Finset.mem_image]
  constructor
  · rintro ⟨e0, he0, rfl⟩
    rw [cutEdges, Finset.mem_filter] at he0
    obtain ⟨hedge, hcross⟩ := he0
    induction e0 with
    | h a b =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hedge
      have hadj : (latticeGraph 2).Adj ↑a ↑b := SimpleGraph.induce_adj.mp hedge
      have hcross' : xor (decide (a ∈ F)) (decide (b ∈ F)) = true := by
        simpa [edgeCrosses, Sym2.lift_mk] using hcross
      by_cases hb : b ∈ F
      · -- then `a ∉ F`; swap orientation
        have ha : a ∉ F := by intro ha; simp [ha, hb] at hcross'
        exact ⟨b, a, by rw [Sym2.map_mk, Sym2.eq_swap], hadj.symm, hb, ha⟩
      · have ha : a ∈ F := by by_contra ha; simp [ha, hb] at hcross'
        exact ⟨a, b, by rw [Sym2.map_mk], hadj, ha, hb⟩
  · rintro ⟨a, b, rfl, hadj, ha, hb⟩
    refine ⟨s(a, b), ?_, by rw [Sym2.map_mk]⟩
    rw [cutEdges, Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      exact SimpleGraph.induce_adj.mpr hadj
    · simp [edgeCrosses, Sym2.lift_mk, ha, hb]

end IsingModel

import IsingModel.Peierls.DualCut
import IsingModel.Peierls.BoundaryDart
import IsingModel.Peierls.DartDualComponentImage

/-!
# The dual edge of a primal cut edge (FV §3.7.2)

Towards transporting the Eulerian (even-degree) property of a dart's dual component to its
box-primal image `B`, this file records the basic primal/dual edge correspondence on the lattice:
the dual of a dart's primal cut edge `s(leftSite, rightSite)` is its dual edge `s(tail, head)`.

* `dualEdge_toSym2` — `dualEdge (g.toSym2) = g.dual.toSym2` for any coordinate edge `g` (the
  `gridEdge2Equiv` round trip).
* `dualEdge_primalCutEdge` — `dualEdge (primalCutEdge t dir) = s(t, t + dir.vec)`.
* `dualEdge_map_val_boxPrimalCutEdge` — dualizing a dart's box-primal edge (mapped to the ambient
  lattice) recovers its ambient dual edge `s(tail, head)`.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

/-- **`toGrid` inverts `toSym2`**: `toGrid (g.toSym2) = g` for any coordinate edge `g` (the
`gridEdge2Equiv` round trip on lattice edges). -/
theorem toGrid_of_toSym2 (g : GridEdge2) : toGrid g.toSym2 = g := by
  have he : g.toSym2 ∈ (latticeGraph 2).edgeSet := g.toSym2_isLatticeEdge
  rw [toGrid, dif_pos he]
  have hval : gridEdge2Equiv g = ⟨g.toSym2, he⟩ := Subtype.ext rfl
  rw [← hval, gridEdge2Equiv.symm_apply_apply]

/-- **The dual edge of a coordinate edge's lattice edge** is its grid dual's lattice edge. -/
theorem dualEdge_toSym2 (g : GridEdge2) : dualEdge g.toSym2 = g.dual.toSym2 := by
  rw [dualEdge, toGrid_of_toSym2]

/-- **The dual edge of a dart's primal cut edge is its dual edge**: `dualEdge (primalCutEdge t dir)
= s(t, t + dir.vec)`. The primal cut edge `s(leftSite, rightSite)` and the dual edge `s(t, head)`
are perpendicular coordinate edges meeting at the dart. -/
theorem dualEdge_primalCutEdge (t : Fin 2 → ℤ) (dir : Dir2) :
    dualEdge (primalCutEdge t dir) = s(t, t + dir.vec) := by
  have hcut : ∀ g : GridEdge2, primalCutEdge t dir = g.toSym2 →
      dualEdge (primalCutEdge t dir) = g.dual.toSym2 := fun g hg => by rw [hg, dualEdge_toSym2]
  fin_cases dir
  · refine (hcut ⟨t + unitVec2 0, 1⟩ ?_).trans ?_
    · rw [primalCutEdge, GridEdge2.toSym2, Sym2.eq_swap]
      congr 1
      all_goals (simp only [leftSite, rightSite, Dir2.turnLeft, Dir2.vec]
                 funext i; fin_cases i <;> simp [unitVec2, Pi.add_apply, Pi.sub_apply])
    · simp only [GridEdge2.dual, GridEdge2.toSym2, otherAxis_one, Dir2.vec]
      congr 1
      all_goals (funext i; fin_cases i <;> simp [unitVec2, Pi.add_apply, Pi.sub_apply])
  · refine (hcut ⟨t + unitVec2 1, 0⟩ ?_).trans ?_
    · rw [primalCutEdge, GridEdge2.toSym2]
      congr 1
      all_goals (simp only [leftSite, rightSite, Dir2.turnLeft, Dir2.vec]
                 funext i; fin_cases i <;> simp [unitVec2, Pi.add_apply, Pi.sub_apply])
    · simp only [GridEdge2.dual, GridEdge2.toSym2, otherAxis_zero, Dir2.vec]
      congr 1
      all_goals (funext i; fin_cases i <;> simp [unitVec2, Pi.add_apply, Pi.sub_apply])
  · refine (hcut ⟨t, 1⟩ ?_).trans ?_
    · rw [primalCutEdge, GridEdge2.toSym2]
      congr 1
      all_goals (simp only [leftSite, rightSite, Dir2.turnLeft, Dir2.vec]
                 funext i; fin_cases i <;> simp [unitVec2, Pi.add_apply, Pi.sub_apply])
    · simp only [GridEdge2.dual, GridEdge2.toSym2, otherAxis_one, Dir2.vec]
      rw [Sym2.eq_swap]
      congr 1
      all_goals (funext i; fin_cases i <;> simp [unitVec2, Pi.add_apply, Pi.sub_apply])
  · refine (hcut ⟨t, 0⟩ ?_).trans ?_
    · rw [primalCutEdge, GridEdge2.toSym2, Sym2.eq_swap]
      congr 1
      all_goals (simp only [leftSite, rightSite, Dir2.turnLeft, Dir2.vec]
                 funext i; fin_cases i <;> simp [unitVec2, Pi.add_apply, Pi.sub_apply])
    · simp only [GridEdge2.dual, GridEdge2.toSym2, otherAxis_zero, Dir2.vec]
      rw [Sym2.eq_swap]
      congr 1
      all_goals (funext i; fin_cases i <;> simp [unitVec2, Pi.add_apply, Pi.sub_apply])

variable {F Λ : Finset (Fin 2 → ℤ)}

/-- **Dualizing a box-primal edge recovers the dart's dual edge**: applying `Sym2.map Subtype.val`
to a dart's box-primal cut edge and then `dualEdge` yields its ambient dual edge `s(tail, head)`. -/
theorem dualEdge_map_val_boxPrimalCutEdge (hFΛ : F ⊆ Λ)
    (hRΛ : ∀ q : BoundaryDart F, q.right ∈ Λ) (q : BoundaryDart F) :
    dualEdge (Sym2.map Subtype.val (BoundaryDart.boxPrimalCutEdge hFΛ hRΛ q))
      = s(q.tail, q.head) := by
  rw [BoundaryDart.map_val_boxPrimalCutEdge, dualEdge_primalCutEdge, BoundaryDart.head]

end IsingModel

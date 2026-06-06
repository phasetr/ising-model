import IsingModel.Peierls.Dir2
import IsingModel.Peierls.FlipSet

/-!
# Oriented boundary darts (FV §3.7.2)

The 2D Peierls contour is traversed by **boundary darts**: a dart sits at a dual vertex `tail`,
moves in a direction `dir` (to `tail + dir.vec`), and keeps the region `F` on its **left**. The
primal lattice points immediately to the left and right of the dart's motion are `leftSite` and
`rightSite`; the dart is *valid* when `leftSite ∈ F` and `rightSite ∉ F`, i.e. the dual edge it
traverses crosses the primal cut edge `s(leftSite, rightSite)`.

This file sets up the dart structure and the basic geometry (the two sites are adjacent and their
edge is a genuine cut edge). The traversal rule (`nextDart`) and its connectivity consequences
are built on top.

* `leftSite`, `rightSite`, `ValidAt`, `BoundaryDart` — the dart and its validity.
* `primalCutEdge`, `leftSite_rightSite_adjacent`, `validAt_edgeCrosses` — the crossed cut edge.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

/-- The primal lattice point on the **left** of a dart at `tail` moving in direction `dir`
(identifying a dual vertex with the lattice point at its lower-left corner). -/
def leftSite (tail : Fin 2 → ℤ) (dir : Dir2) : Fin 2 → ℤ :=
  ![tail + unitVec2 0 + unitVec2 1,   -- dir = e₀
    tail + unitVec2 1,                -- dir = e₁
    tail,                             -- dir = -e₀
    tail + unitVec2 0] dir            -- dir = -e₁

/-- The primal lattice point on the **right** of the dart: one step back along the left normal. -/
def rightSite (tail : Fin 2 → ℤ) (dir : Dir2) : Fin 2 → ℤ :=
  leftSite tail dir - (Dir2.turnLeft dir).vec

/-- A dart is **valid** when the region lies on its left and the complement on its right. -/
def ValidAt (F : Finset (Fin 2 → ℤ)) (tail : Fin 2 → ℤ) (dir : Dir2) : Prop :=
  leftSite tail dir ∈ F ∧ rightSite tail dir ∉ F

/-- An **oriented boundary dart** with the region `F` on its left. -/
structure BoundaryDart (F : Finset (Fin 2 → ℤ)) where
  /-- The dual vertex the dart starts at. -/
  tail : Fin 2 → ℤ
  /-- The direction of travel. -/
  dir : Dir2
  /-- The left site lies in `F`. -/
  left_mem : leftSite tail dir ∈ F
  /-- The right site lies outside `F`. -/
  right_not_mem : rightSite tail dir ∉ F

/-- The head of a dart (the next dual vertex). -/
def BoundaryDart.head {F : Finset (Fin 2 → ℤ)} (d : BoundaryDart F) : Fin 2 → ℤ :=
  d.tail + d.dir.vec

/-- The **primal cut edge** crossed by a boundary dart. -/
def primalCutEdge (tail : Fin 2 → ℤ) (dir : Dir2) : Sym2 (Fin 2 → ℤ) :=
  s(leftSite tail dir, rightSite tail dir)

/-- **The left and right sites are nearest neighbours**: their edge is a unit lattice edge. -/
theorem leftSite_rightSite_adjacent (tail : Fin 2 → ℤ) (dir : Dir2) :
    ∃ k : Fin 2,
      leftSite tail dir = rightSite tail dir + unitVec2 k ∨
        rightSite tail dir = leftSite tail dir + unitVec2 k := by
  fin_cases dir
  · exact ⟨1, Or.inl (by
      funext i; fin_cases i <;> simp [leftSite, rightSite, Dir2.vec, Dir2.turnLeft, unitVec2])⟩
  · exact ⟨0, Or.inr (by
      funext i; fin_cases i <;> simp [leftSite, rightSite, Dir2.vec, Dir2.turnLeft, unitVec2])⟩
  · exact ⟨1, Or.inr (by
      funext i; fin_cases i <;> simp [leftSite, rightSite, Dir2.vec, Dir2.turnLeft, unitVec2])⟩
  · exact ⟨0, Or.inl (by
      funext i; fin_cases i <;> simp [leftSite, rightSite, Dir2.vec, Dir2.turnLeft, unitVec2])⟩

/-- **A valid dart crosses a genuine cut edge**: `edgeCrosses F (primalCutEdge tail dir) = true`
when the dart is valid (left site in `F`, right site out). -/
theorem validAt_edgeCrosses {F : Finset (Fin 2 → ℤ)} {tail : Fin 2 → ℤ} {dir : Dir2}
    (h : ValidAt F tail dir) : edgeCrosses F (primalCutEdge tail dir) = true := by
  unfold primalCutEdge edgeCrosses
  rw [Sym2.lift_mk]
  simp [h.1, h.2]

end IsingModel

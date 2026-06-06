import IsingModel.Peierls.SingleOrbitFan

/-!
# Right-fan boundary detection (FV §3.7.2)

Dual to the left fan (`SingleOrbitFan`): the **right fan** around a fixed right site `q ∉ F` is the
set of boundary darts with right site `q`; a right turn keeps the right site fixed
(`right_nextDart_of_turnRight`), so iterating right turns rotates the dart around `q`. This file
proves the **boundary** of that fan: a `nextDart` step keeps the right site fixed **iff** it takes
the right turn (`right_nextDart_eq_right_iff_turnRight`). A left turn moves the right site by
`dir.vec + (turnLeft dir).vec ≠ 0`, and a straight step by `dir.vec ≠ 0`, so either way the right
site changes. This is the complement-side rotation needed for the "vary in-site" contact step.

* `Dir2.vec_add_turnLeft_vec_ne_zero` — the diagonal increment is nonzero.
* `right_nextDart_ne_right_of_turnLeft` / `_of_straight` — a non-right turn moves the right site.
* `right_nextDart_eq_right_iff_turnRight` — the right-fan boundary criterion.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- **The diagonal increment `dir.vec + (turnLeft dir).vec` is nonzero** (a sum of two perpendicular
unit vectors). -/
theorem Dir2.vec_add_turnLeft_vec_ne_zero (δ : Dir2) : δ.vec + (δ.turnLeft).vec ≠ 0 := by
  fin_cases δ <;>
    (intro h; have h0 := congrFun h 0; have h1 := congrFun h 1;
      simp [Dir2.vec, Dir2.turnLeft, unitVec2] at h0 h1)

/-- **A left turn moves the right site**: in the left-turn case the right site jumps by the nonzero
diagonal `dir.vec + (turnLeft dir).vec`. -/
theorem right_nextDart_ne_right_of_turnLeft (d : BoundaryDart F)
    (h : ValidAt F d.head d.dir.turnLeft) : d.nextDart.right ≠ d.right := by
  rw [right_nextDart_of_turnLeft d h]
  have hsub : leftSite d.head d.dir - d.right = d.dir.vec + (d.dir.turnLeft).vec := by
    change leftSite (d.tail + d.dir.vec) d.dir - rightSite d.tail d.dir
      = d.dir.vec + (d.dir.turnLeft).vec
    rw [leftSite_add, rightSite]; abel
  intro heq
  exact Dir2.vec_add_turnLeft_vec_ne_zero d.dir (by rw [← hsub, heq, sub_self])

/-- **A straight step moves the right site** by `dir.vec ≠ 0`. -/
theorem right_nextDart_ne_right_of_straight (d : BoundaryDart F)
    (hL : ¬ ValidAt F d.head d.dir.turnLeft) (hS : ValidAt F d.head d.dir) :
    d.nextDart.right ≠ d.right := by
  rw [right_nextDart_of_straight d hL hS]
  have hsub : rightSite d.head d.dir - d.right = d.dir.vec := by
    change rightSite (d.tail + d.dir.vec) d.dir - rightSite d.tail d.dir = d.dir.vec
    rw [rightSite_add]; abel
  intro heq
  exact Dir2.vec_ne_zero d.dir (by rw [← hsub, heq, sub_self])

/-- **The right-fan boundary criterion**: a `nextDart` step keeps the right site fixed iff it takes
the right turn (neither the left turn nor going straight is valid). -/
theorem right_nextDart_eq_right_iff_turnRight (d : BoundaryDart F) :
    d.nextDart.right = d.right ↔
      ¬ ValidAt F d.head d.dir.turnLeft ∧ ¬ ValidAt F d.head d.dir := by
  constructor
  · intro heq
    refine ⟨fun hL => right_nextDart_ne_right_of_turnLeft d hL heq, fun hS => ?_⟩
    by_cases hL : ValidAt F d.head d.dir.turnLeft
    · exact right_nextDart_ne_right_of_turnLeft d hL heq
    · exact right_nextDart_ne_right_of_straight d hL hS heq
  · rintro ⟨hL, hS⟩
    exact right_nextDart_of_turnRight d hL hS

end IsingModel

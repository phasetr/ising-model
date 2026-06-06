import IsingModel.Peierls.SingleOrbitBase
import IsingModel.Peierls.NextDart
import IsingModel.Peierls.DartBijection

/-!
# Site evolution under `nextDart` (FV §3.7.2)

How the two sites `(left, right)` of a boundary dart evolve under one `nextDart` step, case by case
on the turn taken. These are the concrete geometric increments the planned boundary-slide argument
relies on: a left turn pivots about the left site, a right turn pivots about the right site, and a
straight step advances both sites to the head. Each identity is a direct consequence of the four
site identities in `NextDart.lean` together with `nextDart_eq_{turnLeft,straight,turnRight}`.

* `left_nextDart_of_turnLeft` — a left turn keeps the left site fixed (`pivot about the left`).
* `right_nextDart_of_turnLeft` — its right site is the head's straight left site.
* `left_nextDart_of_straight` / `right_nextDart_of_straight` — a straight step is at the head.
* `right_nextDart_of_turnRight` — a right turn keeps the right site fixed (`pivot about the right`).
* `left_nextDart_of_turnRight` — its left site is the head's straight right site.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- **A left turn keeps the left site fixed**: when `nextDart` takes the left turn, the new dart's
left site equals the old left site (the boundary pivots about the left site). -/
theorem left_nextDart_of_turnLeft (d : BoundaryDart F)
    (h : ValidAt F d.head d.dir.turnLeft) : d.nextDart.left = d.left := by
  rw [nextDart_eq_turnLeft d h]
  exact leftSite_head_turnLeft d.tail d.dir

/-- **The right site after a left turn** is the head's straight left site. -/
theorem right_nextDart_of_turnLeft (d : BoundaryDart F)
    (h : ValidAt F d.head d.dir.turnLeft) :
    d.nextDart.right = leftSite d.head d.dir := by
  rw [nextDart_eq_turnLeft d h]
  exact rightSite_head_turnLeft_eq_leftSite_head d.tail d.dir

/-- **The left site after a straight step** is the head's straight left site. -/
theorem left_nextDart_of_straight (d : BoundaryDart F)
    (hL : ¬ ValidAt F d.head d.dir.turnLeft) (hS : ValidAt F d.head d.dir) :
    d.nextDart.left = leftSite d.head d.dir := by
  rw [nextDart_eq_straight d hL hS]; rfl

/-- **The right site after a straight step** is the head's straight right site. -/
theorem right_nextDart_of_straight (d : BoundaryDart F)
    (hL : ¬ ValidAt F d.head d.dir.turnLeft) (hS : ValidAt F d.head d.dir) :
    d.nextDart.right = rightSite d.head d.dir := by
  rw [nextDart_eq_straight d hL hS]; rfl

/-- **A right turn keeps the right site fixed**: when `nextDart` takes the right turn, the new
dart's right site equals the old right site (the boundary pivots about the right site). -/
theorem right_nextDart_of_turnRight (d : BoundaryDart F)
    (hL : ¬ ValidAt F d.head d.dir.turnLeft) (hS : ¬ ValidAt F d.head d.dir) :
    d.nextDart.right = d.right := by
  rw [nextDart_eq_turnRight d hL hS]
  exact rightSite_head_turnRight d.tail d.dir

/-- **The left site after a right turn** is the head's straight right site. -/
theorem left_nextDart_of_turnRight (d : BoundaryDart F)
    (hL : ¬ ValidAt F d.head d.dir.turnLeft) (hS : ¬ ValidAt F d.head d.dir) :
    d.nextDart.left = rightSite d.head d.dir := by
  rw [nextDart_eq_turnRight d hL hS]
  exact (rightSite_head_eq_leftSite_head_turnRight d.tail d.dir).symm

/-- **Every `nextDart` step pivots about a site or advances to the head**: one `nextDart` step
either keeps the left site fixed (left turn), keeps the right site fixed (right turn), or advances
both sites to the head (straight). This is the complete site-increment trichotomy driving the
boundary slide. -/
theorem nextDart_site_step (d : BoundaryDart F) :
    d.nextDart.left = d.left ∨ d.nextDart.right = d.right ∨
      (d.nextDart.left = leftSite d.head d.dir ∧
        d.nextDart.right = rightSite d.head d.dir) := by
  by_cases hL : ValidAt F d.head d.dir.turnLeft
  · exact Or.inl (left_nextDart_of_turnLeft d hL)
  · by_cases hS : ValidAt F d.head d.dir
    · exact Or.inr (Or.inr ⟨left_nextDart_of_straight d hL hS,
        right_nextDart_of_straight d hL hS⟩)
    · exact Or.inr (Or.inl (right_nextDart_of_turnRight d hL hS))

end IsingModel

import IsingModel.Peierls.SingleOrbitFanPrefix

/-!
# The left-fan validity criterion (FV §3.7.2)

The local condition controlling how far a left fan turns: after a left-fan prefix of length `n`, the
next left turn is valid **iff** the lattice point one step from the fixed left site in the current
(rotated) direction lies outside `F`. The `F`-side conjunct of validity is automatic (the left site
is the fixed `F`-vertex `d.left`), so only the out-side membership matters. This reduces the
wedge-existence question to a purely local membership condition on the neighbours of `d.left`.

* `leftFan_next_turnLeft_valid_iff` — the next left turn is valid iff
  `d.left + (turnLeft^[n] d.dir).vec ∉ F`.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- **The left-fan validity criterion**: after a left-fan prefix of length `n`, the next left turn
is valid iff the lattice point one step from `d.left` in the rotated direction `turnLeft^[n] d.dir`
lies outside `F` (the `F`-side conjunct is automatic, the left site being the fixed `F`-vertex). -/
theorem leftFan_next_turnLeft_valid_iff (d : BoundaryDart F) {n : ℕ}
    (hfan : d.LeftFanPrefix n) :
    ValidAt F (BoundaryDart.nextDart^[n] d).head (BoundaryDart.nextDart^[n] d).dir.turnLeft
      ↔ d.left + ((Dir2.turnLeft^[n]) d.dir).vec ∉ F := by
  set e := BoundaryDart.nextDart^[n] d with he
  have heL : e.left = d.left := left_eq_iterate_of_leftFanPrefix d hfan
  have heDir : e.dir = (Dir2.turnLeft^[n]) d.dir := dir_eq_iterate_of_leftFanPrefix d hfan
  have hl_eq : leftSite e.head e.dir.turnLeft = e.left :=
    leftSite_head_turnLeft e.tail e.dir
  have hr_eq : rightSite e.head e.dir.turnLeft = e.left + e.dir.vec := by
    change rightSite (e.tail + e.dir.vec) e.dir.turnLeft = leftSite e.tail e.dir + e.dir.vec
    rw [rightSite_head_turnLeft_eq_leftSite_head, leftSite_add]
  unfold ValidAt
  rw [hl_eq, hr_eq, heL, heDir]
  exact and_iff_right d.left_mem

end IsingModel

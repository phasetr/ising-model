import IsingModel.Peierls.NextDart

/-!
# The reverse local step of the boundary traversal (FV §3.7.2)

The boundary-dart traversal is locally reversible: at the head of a valid dart, the left turn's
*left* site always lies in `F` (it is the incoming left site), so validity of the left/straight/
right continuations reduces to a single condition each. In particular, if neither the right turn
nor going straight is valid, the **left** turn must be (`left_valid_of_not_right_not_straight`) —
the mirror of `right_valid_of_not_left_not_straight`. Together they show every continuation
direction at the head is governed by the priority rule, the basis for the orbit being a cycle.

* `validAt_turnLeft_iff`, `validAt_turnRight_iff` — validity reduces to one site condition.
* `left_valid_of_not_right_not_straight` — the left turn is forced when right and straight fail.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- **Validity of the left turn reduces to one condition**: since the left-turn left site equals
the incoming left site (in `F`), the left turn is valid iff its right site lies outside `F`. -/
theorem validAt_turnLeft_iff (d : BoundaryDart F) :
    ValidAt F d.head d.dir.turnLeft ↔ rightSite d.head d.dir.turnLeft ∉ F := by
  have hhead : d.head = d.tail + d.dir.vec := rfl
  rw [hhead]
  have e1 := leftSite_head_turnLeft d.tail d.dir
  unfold ValidAt
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨e1 ▸ d.left_mem, h⟩

/-- **Validity of the right turn reduces to one condition**: since the right-turn right site
equals the incoming right site (outside `F`), the right turn is valid iff its left site lies
in `F`. -/
theorem validAt_turnRight_iff (d : BoundaryDart F) :
    ValidAt F d.head d.dir.turnRight ↔ leftSite d.head d.dir.turnRight ∈ F := by
  have hhead : d.head = d.tail + d.dir.vec := rfl
  rw [hhead]
  have e4 := rightSite_head_turnRight d.tail d.dir
  unfold ValidAt
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, e4 ▸ d.right_not_mem⟩

/-- **The left turn is forced** (the reverse local step): if at the head of a valid dart neither
the right turn nor going straight is valid, the left turn is valid. Mirror of
`right_valid_of_not_left_not_straight`, using the same four site identities. -/
theorem left_valid_of_not_right_not_straight (d : BoundaryDart F)
    (hR : ¬ ValidAt F d.head d.dir.turnRight) (hS : ¬ ValidAt F d.head d.dir) :
    ValidAt F d.head d.dir.turnLeft := by
  have hhead : d.head = d.tail + d.dir.vec := rfl
  rw [hhead] at hR hS ⊢
  have e1 := leftSite_head_turnLeft d.tail d.dir
  have e2 := rightSite_head_turnLeft_eq_leftSite_head d.tail d.dir
  have e3 := rightSite_head_eq_leftSite_head_turnRight d.tail d.dir
  have e4 := rightSite_head_turnRight d.tail d.dir
  unfold ValidAt at hR hS ⊢
  -- right turn's right site is the incoming right site, outside F
  have hr4 : rightSite (d.tail + d.dir.vec) d.dir.turnRight ∉ F := e4 ▸ d.right_not_mem
  -- hence ¬(right valid) forces its left site out, i.e. the straight right site is out
  have s1 : rightSite (d.tail + d.dir.vec) d.dir ∉ F := by
    rw [e3]; intro hc; exact hR ⟨hc, hr4⟩
  -- hence ¬(straight valid) forces the straight left site out = left-turn right site out
  have s2 : leftSite (d.tail + d.dir.vec) d.dir ∉ F := fun hc => hS ⟨hc, s1⟩
  exact ⟨e1 ▸ d.left_mem, by rw [e2]; exact s2⟩

end IsingModel

import IsingModel.Peierls.BoundaryDart

/-!
# The boundary-dart turning rule (FV §3.7.2)

At the head of a boundary dart the contour continues by turning **left**, going **straight**, or
turning **right** — in that priority (the "keep the wall on the left" rule). The crux is that this
is always possible: if neither the left turn nor going straight is valid, the right turn must be
(`right_valid_of_not_left_not_straight`). This is the local discrete-Jordan step that lets the
traversal continue without dead-ends; combined with finiteness it closes the contour into a cycle.

The proof is a chain of four site identities (provable by `fin_cases` on the direction): the
incoming dart's sites coincide with the candidate next sites, so the incoming validity propagates
through left → straight → right.

* `leftSite_head_turnLeft`, `rightSite_head_turnLeft_eq_leftSite_head`,
  `rightSite_head_eq_leftSite_head_turnRight`, `rightSite_head_turnRight` — four site identities.
* `right_valid_of_not_left_not_straight` — the right turn is always available.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

/-- **Site identity 1**: the left-turn left site at the head equals the incoming left site. -/
theorem leftSite_head_turnLeft (t : Fin 2 → ℤ) (δ : Dir2) :
    leftSite (t + δ.vec) δ.turnLeft = leftSite t δ := by
  fin_cases δ <;>
    (funext i; fin_cases i <;>
      simp [leftSite, Dir2.vec, Dir2.turnLeft, unitVec2, Pi.add_apply])

/-- **Site identity 2**: the left-turn right site at the head equals the straight left site. -/
theorem rightSite_head_turnLeft_eq_leftSite_head (t : Fin 2 → ℤ) (δ : Dir2) :
    rightSite (t + δ.vec) δ.turnLeft = leftSite (t + δ.vec) δ := by
  fin_cases δ <;>
    (funext i; fin_cases i <;>
      simp [leftSite, rightSite, Dir2.vec, Dir2.turnLeft, unitVec2, Pi.add_apply] <;> omega)

/-- **Site identity 3**: the straight right site at the head equals the right-turn left site. -/
theorem rightSite_head_eq_leftSite_head_turnRight (t : Fin 2 → ℤ) (δ : Dir2) :
    rightSite (t + δ.vec) δ = leftSite (t + δ.vec) δ.turnRight := by
  fin_cases δ <;>
    (funext i; fin_cases i <;>
      simp [leftSite, rightSite, Dir2.vec, Dir2.turnLeft, Dir2.turnRight, unitVec2,
        Pi.add_apply])

/-- **Site identity 4**: the right-turn right site at the head equals the incoming right site. -/
theorem rightSite_head_turnRight (t : Fin 2 → ℤ) (δ : Dir2) :
    rightSite (t + δ.vec) δ.turnRight = rightSite t δ := by
  fin_cases δ <;>
    (funext i; fin_cases i <;>
      simp [leftSite, rightSite, Dir2.vec, Dir2.turnLeft, Dir2.turnRight, unitVec2,
        Pi.add_apply])

/-- **The right turn is always available** (the local discrete-Jordan step): if at the head of a
valid dart neither the left turn nor going straight is valid, the right turn is valid. -/
theorem right_valid_of_not_left_not_straight {F : Finset (Fin 2 → ℤ)} (d : BoundaryDart F)
    (hL : ¬ ValidAt F d.head d.dir.turnLeft) (hS : ¬ ValidAt F d.head d.dir) :
    ValidAt F d.head d.dir.turnRight := by
  have hhead : d.head = d.tail + d.dir.vec := rfl
  rw [hhead] at hL hS ⊢
  have e1 := leftSite_head_turnLeft d.tail d.dir
  have e2 := rightSite_head_turnLeft_eq_leftSite_head d.tail d.dir
  have e3 := rightSite_head_eq_leftSite_head_turnRight d.tail d.dir
  have e4 := rightSite_head_turnRight d.tail d.dir
  unfold ValidAt at hL hS ⊢
  -- propagate validity left → straight → right
  have s1 : leftSite (d.tail + d.dir.vec) d.dir.turnLeft ∈ F := e1 ▸ d.left_mem
  have s2 : rightSite (d.tail + d.dir.vec) d.dir.turnLeft ∈ F := by
    by_contra hc; exact hL ⟨s1, hc⟩
  have s3 : leftSite (d.tail + d.dir.vec) d.dir ∈ F := e2 ▸ s2
  have s4 : rightSite (d.tail + d.dir.vec) d.dir ∈ F := by
    by_contra hc; exact hS ⟨s3, hc⟩
  exact ⟨e3 ▸ s4, e4 ▸ d.right_not_mem⟩

/-- **The next boundary dart** in the left-hand traversal: at the head, take the left turn if
valid, else go straight if valid, else turn right (always valid by
`right_valid_of_not_left_not_straight`). -/
noncomputable def BoundaryDart.nextDart {F : Finset (Fin 2 → ℤ)} (d : BoundaryDart F) :
    BoundaryDart F := by
  classical
  by_cases hL : ValidAt F d.head d.dir.turnLeft
  · exact ⟨d.head, d.dir.turnLeft, hL.1, hL.2⟩
  · by_cases hS : ValidAt F d.head d.dir
    · exact ⟨d.head, d.dir, hS.1, hS.2⟩
    · have hR := right_valid_of_not_left_not_straight d hL hS
      exact ⟨d.head, d.dir.turnRight, hR.1, hR.2⟩

/-- **The next dart starts at the current head**: the traversal advances continuously. -/
theorem BoundaryDart.nextDart_tail {F : Finset (Fin 2 → ℤ)} (d : BoundaryDart F) :
    d.nextDart.tail = d.head := by
  classical
  unfold BoundaryDart.nextDart
  by_cases hL : ValidAt F d.head d.dir.turnLeft
  · rw [dif_pos hL]
  · rw [dif_neg hL]
    by_cases hS : ValidAt F d.head d.dir
    · rw [dif_pos hS]
    · rw [dif_neg hS]

end IsingModel

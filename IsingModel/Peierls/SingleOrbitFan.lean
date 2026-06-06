import IsingModel.Peierls.SingleOrbitSlide
import IsingModel.Peierls.SingleOrbitContact

/-!
# Fan boundary detection (FV §3.7.2)

The "fan" around a fixed left site `p ∈ F` is the set of boundary darts with left site `p`; a left
turn keeps the left site fixed (`left_nextDart_of_turnLeft`), so iterating left turns rotates the
dart around `p`. This file proves the **boundary** of that fan: a `nextDart` step keeps the left
site fixed **iff** it takes the left turn (`left_nextDart_eq_left_iff_turnLeft`). The forward
direction is `left_nextDart_of_turnLeft`; the converse is the new content — a straight step shifts
the left site by `dir.vec ≠ 0`, and a right turn shifts it by `dir.vec - (turnLeft dir).vec ≠ 0`, so
either way the left site changes.

* `leftSite_add` / `rightSite_add` — the sites are equivariant under lattice translation.
* `Dir2.vec_ne_zero` / `Dir2.vec_ne_turnLeft_vec` — direction vectors are nonzero and distinct from
  their left-turn.
* `dir_nextDart_of_turnLeft` — a left turn rotates the direction left.
* `left_nextDart_ne_left_of_not_turnLeft` — a non-left turn moves the left site.
* `left_nextDart_eq_left_iff_turnLeft` — the fan boundary criterion.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- **The left site is translation-equivariant**: `leftSite (t + v) δ = leftSite t δ + v`. -/
theorem leftSite_add (t v : Fin 2 → ℤ) (δ : Dir2) :
    leftSite (t + v) δ = leftSite t δ + v := by
  fin_cases δ <;> (funext i; fin_cases i <;> simp [leftSite, unitVec2, Pi.add_apply] <;> ring)

/-- **The right site is translation-equivariant**: `rightSite (t + v) δ = rightSite t δ + v`. -/
theorem rightSite_add (t v : Fin 2 → ℤ) (δ : Dir2) :
    rightSite (t + v) δ = rightSite t δ + v := by
  simp only [rightSite, leftSite_add]; abel

/-- **Direction vectors are nonzero**. -/
theorem Dir2.vec_ne_zero (δ : Dir2) : δ.vec ≠ 0 := by
  fin_cases δ <;>
    (intro h; have h0 := congrFun h 0; have h1 := congrFun h 1;
      simp [Dir2.vec, unitVec2] at h0 h1)

/-- **A left turn is not the identity** on directions. -/
theorem Dir2.turnLeft_ne_self (δ : Dir2) : δ.turnLeft ≠ δ := by
  revert δ; decide

/-- **A direction vector differs from its left-turn vector**. -/
theorem Dir2.vec_ne_turnLeft_vec (δ : Dir2) : δ.vec ≠ (δ.turnLeft).vec :=
  fun h => Dir2.turnLeft_ne_self δ (Dir2.vec_injective h).symm

/-- **A left turn rotates the direction left**: `d.nextDart.dir = d.dir.turnLeft`. -/
theorem dir_nextDart_of_turnLeft (d : BoundaryDart F)
    (h : ValidAt F d.head d.dir.turnLeft) : d.nextDart.dir = d.dir.turnLeft := by
  rw [nextDart_eq_turnLeft d h]

/-- **A non-left turn moves the left site**: if `nextDart` does not take the left turn, the new left
site differs from the old (straight shifts by `dir.vec`, a right turn by `dir.vec - turnLeft`). -/
theorem left_nextDart_ne_left_of_not_turnLeft (d : BoundaryDart F)
    (h : ¬ ValidAt F d.head d.dir.turnLeft) : d.nextDart.left ≠ d.left := by
  by_cases hS : ValidAt F d.head d.dir
  · rw [left_nextDart_of_straight d h hS]
    have hsub : leftSite d.head d.dir - d.left = d.dir.vec := by
      change leftSite (d.tail + d.dir.vec) d.dir - leftSite d.tail d.dir = d.dir.vec
      rw [leftSite_add]; abel
    intro heq
    exact Dir2.vec_ne_zero d.dir (by rw [← hsub, heq, sub_self])
  · rw [left_nextDart_of_turnRight d h hS]
    have hsub : rightSite d.head d.dir - d.left = d.dir.vec - (d.dir.turnLeft).vec := by
      change rightSite (d.tail + d.dir.vec) d.dir - leftSite d.tail d.dir
        = d.dir.vec - (d.dir.turnLeft).vec
      rw [rightSite_add, rightSite]; abel
    intro heq
    exact Dir2.vec_ne_turnLeft_vec d.dir (sub_eq_zero.mp (by rw [← hsub, heq, sub_self]))

/-- **The fan boundary criterion**: a `nextDart` step keeps the left site fixed iff it takes the
left turn. Iterating left turns rotates the dart around the fixed left site; the first non-left turn
leaves the fan. -/
theorem left_nextDart_eq_left_iff_turnLeft (d : BoundaryDart F) :
    d.nextDart.left = d.left ↔ ValidAt F d.head d.dir.turnLeft := by
  constructor
  · intro heq
    by_contra h
    exact left_nextDart_ne_left_of_not_turnLeft d h heq
  · exact left_nextDart_of_turnLeft d

end IsingModel

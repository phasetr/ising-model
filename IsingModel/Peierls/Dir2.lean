import IsingModel.Peierls.GridEdge2

/-!
# Directions and 90° rotation in 2D (FV §3.7.2)

The boundary-dart traversal of the 2D Peierls contour walks along the dual lattice, turning left
or right by 90° at each step (the "keep the wall on the left" rule). This file sets up the
direction algebra: a `Dir2` is one of the four axis directions `±e₀, ±e₁`, with a 90° left turn
(`turnLeft`) and right turn (`turnRight`) realised on vectors by `rot90`.

* `rot90` — the 90° rotation `(x, y) ↦ (-y, x)`.
* `Dir2`, `Dir2.vec`, `Dir2.turnLeft`, `Dir2.turnRight` — the four directions and turns.
* `vec_turnLeft` — a left turn acts on the vector by `rot90`; `vec_turnLeft_turnLeft` negates it.
* `turnLeft_turnRight`, `turnRight_turnLeft`, `turnLeft_four` — turn algebra.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

/-- **90° rotation** of a 2D integer vector: `(x, y) ↦ (-y, x)`. -/
def rot90 (v : Fin 2 → ℤ) : Fin 2 → ℤ := ![-v 1, v 0]

/-- A **direction** in the 2D lattice: one of the four axis directions, indexed `0 = e₀`,
`1 = e₁`, `2 = -e₀`, `3 = -e₁`. -/
abbrev Dir2 : Type := Fin 4

namespace Dir2

/-- The unit vector of a direction. -/
def vec (d : Dir2) : Fin 2 → ℤ :=
  ![unitVec2 0, unitVec2 1, -unitVec2 0, -unitVec2 1] d

/-- **Turn left** by 90° (counter-clockwise): `d ↦ d + 1`. -/
def turnLeft (d : Dir2) : Dir2 := d + 1

/-- **Turn right** by 90° (clockwise): `d ↦ d + 3 = d - 1`. -/
def turnRight (d : Dir2) : Dir2 := d + 3

@[simp] theorem turnLeft_turnRight (d : Dir2) : (d.turnLeft).turnRight = d := by
  revert d; decide

@[simp] theorem turnRight_turnLeft (d : Dir2) : (d.turnRight).turnLeft = d := by
  revert d; decide

/-- Four left turns return to the start. -/
theorem turnLeft_four (d : Dir2) : d.turnLeft.turnLeft.turnLeft.turnLeft = d := by
  revert d; decide

/-- `turnLeft` is injective. -/
theorem turnLeft_injective : Function.Injective turnLeft := by decide

/-- `turnRight` is injective. -/
theorem turnRight_injective : Function.Injective turnRight := by decide

/-- The right turn is the opposite of the left turn at the level of vectors:
`(turnRight d).vec = - (turnLeft d).vec`. -/
theorem turnRight_eq_turnLeft_turnLeft_turnLeft (d : Dir2) :
    d.turnRight = d.turnLeft.turnLeft.turnLeft := by revert d; decide

/-- **A left turn rotates the vector by 90°**: `(turnLeft d).vec = rot90 d.vec`. -/
theorem vec_turnLeft (d : Dir2) : (d.turnLeft).vec = rot90 d.vec := by
  fin_cases d <;>
    (funext i; fin_cases i <;>
      simp [turnLeft, vec, rot90, unitVec2])

/-- The opposite direction is two left turns: `(turnLeft (turnLeft d)).vec = - d.vec`. -/
theorem vec_turnLeft_turnLeft (d : Dir2) : (d.turnLeft.turnLeft).vec = - d.vec := by
  fin_cases d <;>
    (funext i; fin_cases i <;>
      simp [turnLeft, vec, unitVec2])

end Dir2

end IsingModel

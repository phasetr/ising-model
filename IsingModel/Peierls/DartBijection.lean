import IsingModel.Peierls.PrevDart

/-!
# Computing `nextDart` from validity (FV §3.7.2)

To prove `nextDart (prevDart e) = e` (and hence that `nextDart` is a bijection on the finite type
of darts, so the orbits are cycles), one needs to evaluate `nextDart` once the validity of the
candidate turns is known. This file provides those reductions and the supporting equalities.

* `rightSite_turnLeft` — the forward right site of a left turn is the original left site.
* `BoundaryDart.ext'` — darts agree when their tail and direction agree.
* `nextDart_eq_turnLeft`, `nextDart_eq_straight`, `nextDart_eq_turnRight` — `nextDart` in terms of
  which continuation is the first valid one.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- **Site identity**: `rightSite t (turnLeft δ) = leftSite t δ` (the right site of the left-turned
direction is the original left site). -/
theorem rightSite_turnLeft (t : Fin 2 → ℤ) (δ : Dir2) :
    rightSite t δ.turnLeft = leftSite t δ := by
  fin_cases δ <;>
    (funext i; fin_cases i <;>
      simp [leftSite, rightSite, Dir2.vec, Dir2.turnLeft, unitVec2, Pi.add_apply, Pi.sub_apply])

/-- **Extensionality for darts**: two boundary darts are equal once their tail and direction
agree (the validity proofs are irrelevant). -/
theorem BoundaryDart.ext' {d₁ d₂ : BoundaryDart F} (ht : d₁.tail = d₂.tail)
    (hd : d₁.dir = d₂.dir) : d₁ = d₂ := by
  cases d₁; cases d₂; cases ht; cases hd; rfl

/-- **`nextDart` takes the left turn** when it is valid. -/
theorem nextDart_eq_turnLeft (d : BoundaryDart F) (h : ValidAt F d.head d.dir.turnLeft) :
    d.nextDart = ⟨d.head, d.dir.turnLeft, h.1, h.2⟩ := by
  unfold BoundaryDart.nextDart
  rw [dif_pos h]

/-- **`nextDart` goes straight** when the left turn is invalid but straight is valid. -/
theorem nextDart_eq_straight (d : BoundaryDart F) (hL : ¬ ValidAt F d.head d.dir.turnLeft)
    (hS : ValidAt F d.head d.dir) : d.nextDart = ⟨d.head, d.dir, hS.1, hS.2⟩ := by
  unfold BoundaryDart.nextDart
  rw [dif_neg hL, dif_pos hS]

/-- **`nextDart` takes the right turn** when neither the left turn nor going straight is valid. -/
theorem nextDart_eq_turnRight (d : BoundaryDart F) (hL : ¬ ValidAt F d.head d.dir.turnLeft)
    (hS : ¬ ValidAt F d.head d.dir) :
    d.nextDart = ⟨d.head, d.dir.turnRight,
      (right_valid_of_not_left_not_straight d hL hS).1,
      (right_valid_of_not_left_not_straight d hL hS).2⟩ := by
  unfold BoundaryDart.nextDart
  rw [dif_neg hL, dif_neg hS]

end IsingModel

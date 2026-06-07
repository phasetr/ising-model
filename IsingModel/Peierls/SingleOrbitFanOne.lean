import IsingModel.Peierls.SingleOrbitFanPrefix
import IsingModel.Peierls.SingleOrbitRightFanPrefix

/-!
# One-step fan validity (FV §3.7.2)

The base case of fan-prefix construction: a length-one fan prefix is exactly a single valid turn.
A `LeftFanPrefix` of length one is a valid left turn at the head (`leftFanPrefix_one_iff`), and a
`RightFanPrefix` of length one is a right turn — neither the left turn nor going straight valid
(`rightFanPrefix_one_iff`). These are the elementary generators a fan-rotation (and hence a contact
step) is built from when the global connectivity argument constructs prefixes from local validity.

* `leftFanPrefix_one_iff` / `leftFanPrefix_one` — a length-one left-fan prefix is a valid left turn.
* `rightFanPrefix_one_iff` / `rightFanPrefix_one` — a length-one right-fan prefix is a right turn.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- **A length-one left-fan prefix is a valid left turn**. -/
theorem leftFanPrefix_one_iff (d : BoundaryDart F) :
    d.LeftFanPrefix 1 ↔ ValidAt F d.head d.dir.turnLeft := by
  constructor
  · intro h
    have h0 := h 0 Nat.one_pos
    simpa using h0
  · intro h k hk
    interval_cases k
    simpa using h

/-- **A valid left turn gives a length-one left-fan prefix**. -/
theorem leftFanPrefix_one (d : BoundaryDart F) (h : ValidAt F d.head d.dir.turnLeft) :
    d.LeftFanPrefix 1 :=
  (leftFanPrefix_one_iff d).mpr h

/-- **A length-one right-fan prefix is a right turn** (neither left turn nor straight valid). -/
theorem rightFanPrefix_one_iff (d : BoundaryDart F) :
    d.RightFanPrefix 1 ↔
      ¬ ValidAt F d.head d.dir.turnLeft ∧ ¬ ValidAt F d.head d.dir := by
  constructor
  · intro h
    have h0 := h 0 Nat.one_pos
    simpa using h0
  · intro h k hk
    interval_cases k
    simpa using h

/-- **A right turn gives a length-one right-fan prefix**. -/
theorem rightFanPrefix_one (d : BoundaryDart F)
    (hL : ¬ ValidAt F d.head d.dir.turnLeft) (hS : ¬ ValidAt F d.head d.dir) :
    d.RightFanPrefix 1 :=
  (rightFanPrefix_one_iff d).mpr ⟨hL, hS⟩

end IsingModel

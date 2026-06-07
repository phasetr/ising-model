import IsingModel.Peierls.SingleOrbitDegTwo

/-!
# The face-degree trichotomy of the contour (FV §3.7.2)

Completing the characterisation of the three contour face types by their `squareSplitCount`
(`0`, `2`, or `4`). An **empty** face has all four corners on the same side of `F`
(`squareSplitCount_eq_zero_iff`); a **crossing** face has strictly alternating corners
(`squareSplitCount_eq_four_iff`); the remaining (degree-two) faces are the ordinary ones where the
contour passes through once (`squareSplitCount_eq_two_iff`). Together these decide each face's type
from the four corner memberships, the case basis for analysing how `nextDart` routes the contour.

* `cyclic4_xor_count_eq_zero_iff` / `cyclic4_xor_count_eq_four_iff` — boolean characterisations.
* `squareSplitCount_eq_zero_iff` / `squareSplitCount_eq_four_iff` — empty and crossing faces.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

/-- **No sign changes around a 4-cycle of bits** iff all four bits are equal. -/
theorem cyclic4_xor_count_eq_zero_iff (b0 b1 b2 b3 : Bool) :
    ((if xor b0 b1 then 1 else 0) + (if xor b1 b2 then 1 else 0)
        + (if xor b2 b3 then 1 else 0) + (if xor b3 b0 then 1 else 0) = 0)
      ↔ (b0 = b1 ∧ b1 = b2 ∧ b2 = b3) := by
  revert b0 b1 b2 b3; decide

/-- **Four sign changes around a 4-cycle of bits** iff the bits strictly alternate. -/
theorem cyclic4_xor_count_eq_four_iff (b0 b1 b2 b3 : Bool) :
    ((if xor b0 b1 then 1 else 0) + (if xor b1 b2 then 1 else 0)
        + (if xor b2 b3 then 1 else 0) + (if xor b3 b0 then 1 else 0) = 4)
      ↔ (b0 ≠ b1 ∧ b1 ≠ b2 ∧ b2 ≠ b3) := by
  revert b0 b1 b2 b3; decide

/-- **A face is empty iff all four corners lie on the same side of `F`**. -/
theorem squareSplitCount_eq_zero_iff (F : Finset (Fin 2 → ℤ)) (c : Fin 2 → ℤ) :
    squareSplitCount F c = 0 ↔
      (decide (c ∈ F) = decide (c + unitVec2 0 ∈ F) ∧
        decide (c + unitVec2 0 ∈ F) = decide (c + unitVec2 0 + unitVec2 1 ∈ F) ∧
        decide (c + unitVec2 0 + unitVec2 1 ∈ F) = decide (c + unitVec2 1 ∈ F)) := by
  unfold squareSplitCount
  simp only [edgeCrosses, Sym2.lift_mk]
  exact cyclic4_xor_count_eq_zero_iff (decide (c ∈ F)) (decide (c + unitVec2 0 ∈ F))
    (decide (c + unitVec2 0 + unitVec2 1 ∈ F)) (decide (c + unitVec2 1 ∈ F))

/-- **A face is a crossing iff its four corners strictly alternate** across `F`. -/
theorem squareSplitCount_eq_four_iff (F : Finset (Fin 2 → ℤ)) (c : Fin 2 → ℤ) :
    squareSplitCount F c = 4 ↔
      (decide (c ∈ F) ≠ decide (c + unitVec2 0 ∈ F) ∧
        decide (c + unitVec2 0 ∈ F) ≠ decide (c + unitVec2 0 + unitVec2 1 ∈ F) ∧
        decide (c + unitVec2 0 + unitVec2 1 ∈ F) ≠ decide (c + unitVec2 1 ∈ F)) := by
  unfold squareSplitCount
  simp only [edgeCrosses, Sym2.lift_mk]
  exact cyclic4_xor_count_eq_four_iff (decide (c ∈ F)) (decide (c + unitVec2 0 ∈ F))
    (decide (c + unitVec2 0 + unitVec2 1 ∈ F)) (decide (c + unitVec2 1 ∈ F))

end IsingModel

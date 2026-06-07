import IsingModel.Peierls.ContourEven

/-!
# Degree-two faces of the contour (FV §3.7.2)

A characterisation of the `squareSplitCount = 2` faces — the "ordinary" faces of the Peierls
contour, where the curve passes through once (as opposed to empty faces, count `0`, and crossing
faces, count `4`). At the boolean level, four cyclic membership bits have two sign changes iff they
are neither all equal (an empty face) nor strictly alternating (a crossing face)
(`cyclic4_xor_count_eq_two_iff`); transported to the square this is `squareSplitCount_eq_two_iff`.
This isolates the crossing faces (count `4`) as the only obstruction to the single-orbit property,
the next step toward the discrete-Jordan argument.

* `cyclic4_xor_count_eq_two_iff` — the boolean characterisation of two sign changes.
* `squareSplitCount_eq_two_iff` — a face is degree-two iff not empty and not a crossing.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

/-- **Two sign changes around a 4-cycle of bits** iff the bits are neither all equal nor strictly
alternating. -/
theorem cyclic4_xor_count_eq_two_iff (b0 b1 b2 b3 : Bool) :
    ((if xor b0 b1 then 1 else 0) + (if xor b1 b2 then 1 else 0)
        + (if xor b2 b3 then 1 else 0) + (if xor b3 b0 then 1 else 0) = 2)
      ↔ ¬ (b0 = b1 ∧ b1 = b2 ∧ b2 = b3) ∧ ¬ (b0 ≠ b1 ∧ b1 ≠ b2 ∧ b2 ≠ b3) := by
  revert b0 b1 b2 b3; decide

/-- **A face is degree-two iff it is neither empty nor a crossing**: `squareSplitCount F c = 2`
exactly when the four corners of the unit square at `c` are not all on the same side of `F` and are
not strictly alternating. -/
theorem squareSplitCount_eq_two_iff (F : Finset (Fin 2 → ℤ)) (c : Fin 2 → ℤ) :
    squareSplitCount F c = 2 ↔
      ¬ (decide (c ∈ F) = decide (c + unitVec2 0 ∈ F) ∧
          decide (c + unitVec2 0 ∈ F) = decide (c + unitVec2 0 + unitVec2 1 ∈ F) ∧
          decide (c + unitVec2 0 + unitVec2 1 ∈ F) = decide (c + unitVec2 1 ∈ F)) ∧
        ¬ (decide (c ∈ F) ≠ decide (c + unitVec2 0 ∈ F) ∧
          decide (c + unitVec2 0 ∈ F) ≠ decide (c + unitVec2 0 + unitVec2 1 ∈ F) ∧
          decide (c + unitVec2 0 + unitVec2 1 ∈ F) ≠ decide (c + unitVec2 1 ∈ F)) := by
  unfold squareSplitCount
  simp only [edgeCrosses, Sym2.lift_mk]
  exact cyclic4_xor_count_eq_two_iff (decide (c ∈ F)) (decide (c + unitVec2 0 ∈ F))
    (decide (c + unitVec2 0 + unitVec2 1 ∈ F)) (decide (c + unitVec2 1 ∈ F))

end IsingModel

import IsingModel.Peierls.GridEdge2
import IsingModel.Peierls.FlipSet

/-!
# The Peierls contour is Eulerian (FV §3.7.2)

Each unit square (plaquette / dual vertex) of the 2D lattice has an **even** number of its four
sides in the Peierls cut of a region `F`. Equivalently, in the dual lattice every face has even
degree in the dual contour — the Eulerian property that makes the boundary darts pair up, the
local foundation of the contour's connectedness (the discrete Jordan argument).

The proof is the elementary parity fact that a cyclic binary sequence changes value an even
number of times: going around the four corners of a square, the number of `F`-membership changes
(= cut sides) is even.

* `cyclic4_xor_even` — a 4-cycle of bits has an even number of changes.
* `square_split_count_even` — even number of the four sides of a unit square are cut.
* `square_split_count_le_four`, `square_split_count_eq` — the count is `0`, `2`, or `4`.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

/-- The number of cut sides of a unit square at `c` (its four boundary edges split by `F`). -/
def squareSplitCount (F : Finset (Fin 2 → ℤ)) (c : Fin 2 → ℤ) : ℕ :=
  (if edgeCrosses F s(c, c + unitVec2 0) then 1 else 0)
    + (if edgeCrosses F s(c + unitVec2 0, c + unitVec2 0 + unitVec2 1) then 1 else 0)
    + (if edgeCrosses F s(c + unitVec2 0 + unitVec2 1, c + unitVec2 1) then 1 else 0)
    + (if edgeCrosses F s(c + unitVec2 1, c) then 1 else 0)

/-- **A 4-cycle of bits changes value an even number of times**: the elementary parity fact
underlying the Eulerian property of the contour. -/
theorem cyclic4_xor_even (b0 b1 b2 b3 : Bool) :
    Even ((if xor b0 b1 then 1 else 0) + (if xor b1 b2 then 1 else 0)
        + (if xor b2 b3 then 1 else 0) + (if xor b3 b0 then 1 else 0)) := by
  revert b0 b1 b2 b3; decide

/-- **Each unit square has an even number of cut sides** (the Eulerian / even-degree property of
the Peierls contour): going around the four corners `c, c+e₀, c+e₀+e₁, c+e₁` of the unit square at
`c`, the number of its four sides split by `F` is even. In the dual lattice this says every face
has even degree in the dual contour. -/
theorem square_split_count_even (F : Finset (Fin 2 → ℤ)) (c : Fin 2 → ℤ) :
    Even (squareSplitCount F c) := by
  unfold squareSplitCount
  simp only [edgeCrosses, Sym2.lift_mk]
  exact cyclic4_xor_even (decide (c ∈ F)) (decide (c + unitVec2 0 ∈ F))
    (decide (c + unitVec2 0 + unitVec2 1 ∈ F)) (decide (c + unitVec2 1 ∈ F))

/-- The cut-side count of a unit square is at most `4` (it has four sides). -/
theorem square_split_count_le_four (F : Finset (Fin 2 → ℤ)) (c : Fin 2 → ℤ) :
    squareSplitCount F c ≤ 4 := by
  unfold squareSplitCount
  have h : ∀ p : Prop, ∀ [Decidable p], (if p then (1 : ℕ) else 0) ≤ 1 := by
    intro p _; split <;> omega
  have := h (edgeCrosses F s(c, c + unitVec2 0) = true)
  have := h (edgeCrosses F s(c + unitVec2 0, c + unitVec2 0 + unitVec2 1) = true)
  have := h (edgeCrosses F s(c + unitVec2 0 + unitVec2 1, c + unitVec2 1) = true)
  have := h (edgeCrosses F s(c + unitVec2 1, c) = true)
  omega

/-- **The cut-side count of a unit square is `0`, `2`, or `4`**: the dart-pairing form of the
Eulerian property (each face carries an even, hence pairable, set of contour darts). -/
theorem square_split_count_eq (F : Finset (Fin 2 → ℤ)) (c : Fin 2 → ℤ) :
    squareSplitCount F c = 0 ∨ squareSplitCount F c = 2 ∨ squareSplitCount F c = 4 := by
  obtain ⟨k, hk⟩ := square_split_count_even F c
  have hle := square_split_count_le_four F c
  omega

end IsingModel

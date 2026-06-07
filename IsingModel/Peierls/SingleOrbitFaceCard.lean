import IsingModel.Peierls.SingleOrbitFaceDart
import IsingModel.Peierls.ContourEven

/-!
# The face degree counts incident cut directions (FV §3.7.2)

The contour's `squareSplitCount F c` equals the number of directions `dir : Dir2` whose cut edge
`primalCutEdge c dir` at the dual vertex `c` is crossed by `F`
(`squareSplitCount_eq_card_cut_dirs`). Using `leftSite_eq_cases`/`rightSite_eq_cases`, the four
`primalCutEdge c dir` are exactly the four sides of the unit square at `c` (up to orientation), so
the cut-side count `squareSplitCount` is the dual-cut degree at `c`. This identifies the contour's
local even degree (`square_split_count_even`) as a graph degree, the bridge to the cycle
structure of the `nextDart` orbits in the discrete-Jordan argument.

* `squareSplitCount_eq_card_cut_dirs` — the face degree is the number of incident cut directions.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

/-- **The face degree counts incident cut directions**: `squareSplitCount F c` equals the number of
directions whose cut edge `primalCutEdge c dir` at the dual vertex `c` is crossed by `F`. -/
theorem squareSplitCount_eq_card_cut_dirs (F : Finset (Fin 2 → ℤ)) (c : Fin 2 → ℤ) :
    squareSplitCount F c =
      ((Finset.univ : Finset Dir2).filter
        (fun dir => edgeCrosses F (primalCutEdge c dir) = true)).card := by
  have h0 : primalCutEdge c 0 = s(c + unitVec2 0 + unitVec2 1, c + unitVec2 0) := by
    rw [primalCutEdge, rightSite_eq_cases]; rfl
  have h1 : primalCutEdge c 1 = s(c + unitVec2 1, c + unitVec2 0 + unitVec2 1) := by
    rw [primalCutEdge, rightSite_eq_cases]; rfl
  have h2 : primalCutEdge c 2 = s(c, c + unitVec2 1) := by
    rw [primalCutEdge, rightSite_eq_cases]; rfl
  have h3 : primalCutEdge c 3 = s(c + unitVec2 0, c) := by
    rw [primalCutEdge, rightSite_eq_cases]; rfl
  rw [Finset.card_filter,
    Finset.sum_congr rfl (fun dir _ =>
      show (if edgeCrosses F (primalCutEdge c dir) = true then (1 : ℕ) else 0)
          = (if edgeCrosses F (primalCutEdge c dir) then 1 else 0) by
        cases edgeCrosses F (primalCutEdge c dir) <;> simp),
    Fin.sum_univ_four, h0, h1, h2, h3]
  unfold squareSplitCount
  rw [show (s(c + unitVec2 0 + unitVec2 1, c + unitVec2 0) : Sym2 (Fin 2 → ℤ))
        = s(c + unitVec2 0, c + unitVec2 0 + unitVec2 1) from Sym2.eq_swap,
    show (s(c + unitVec2 1, c + unitVec2 0 + unitVec2 1) : Sym2 (Fin 2 → ℤ))
        = s(c + unitVec2 0 + unitVec2 1, c + unitVec2 1) from Sym2.eq_swap,
    show (s(c, c + unitVec2 1) : Sym2 (Fin 2 → ℤ)) = s(c + unitVec2 1, c) from Sym2.eq_swap,
    show (s(c + unitVec2 0, c) : Sym2 (Fin 2 → ℤ)) = s(c, c + unitVec2 0) from Sym2.eq_swap]
  ring

end IsingModel

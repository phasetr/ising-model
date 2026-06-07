import IsingModel.Peierls.BoundaryDart

/-!
# Dart site coordinates at a dual vertex (FV §3.7.2)

Explicit values of `leftSite` and `rightSite` for a dart based at the dual vertex `c`, as the four
directions rotate. These exhibit the four `primalCutEdge c dir` as exactly the four sides of the
unit square at `c` (the bottom, right, top and left edges, in `dir = -e₁, e₀, e₁, -e₀` order), the
geometric input relating the contour's face degree (`squareSplitCount`) to the dual-cut degree
at `c` in the discrete-Jordan argument.

* `leftSite_eq_cases` / `rightSite_eq_cases` — the left/right sites at `c` for each direction.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

/-- **The left sites at a dual vertex**, for each of the four directions. -/
theorem leftSite_eq_cases (c : Fin 2 → ℤ) (dir : Dir2) :
    leftSite c dir =
      ![c + unitVec2 0 + unitVec2 1, c + unitVec2 1, c, c + unitVec2 0] dir := rfl

/-- **The right sites at a dual vertex**, for each of the four directions: one step back along the
left normal from `leftSite_eq_cases`. -/
theorem rightSite_eq_cases (c : Fin 2 → ℤ) (dir : Dir2) :
    rightSite c dir =
      ![c + unitVec2 0, c + unitVec2 0 + unitVec2 1, c + unitVec2 1, c] dir := by
  fin_cases dir <;>
    (funext i; fin_cases i <;>
      simp [rightSite, leftSite, Dir2.vec, Dir2.turnLeft, unitVec2, Pi.add_apply, Pi.sub_apply,
        Pi.neg_apply])

end IsingModel

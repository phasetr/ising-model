import IsingModel.Peierls.DartDualCutCard
import IsingModel.Peierls.DualToPrimal

/-!
# A crossed cut edge is a valid dart, one way or the other (FV §3.7.2)

`edgeCrosses F (primalCutEdge c dir)` says the cut edge crossed by the direction `dir` at the dual
vertex `c` separates `F`. By the dart reversal identities (`leftSite_reverse`, `rightSite_reverse`),
this happens exactly when either the dart `(c, dir)` is valid (`F` on its left) or the opposite dart
`(c + dir.vec, dir + 2)` is (`F` on the *other* side): `edgeCrosses_primalCutEdge_iff`. This is the
orientation correction needed to count incident cut directions as boundary darts — a cut edge with
`F` on the right is realised by the reversed dart based at the neighbour.

* `edgeCrosses_primalCutEdge_iff` — a crossed cut edge is a valid dart in one orientation.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

/-- **A crossed cut edge is a valid dart in one of two orientations**: the edge crossed by `dir` at
`c` separates `F` iff the dart `(c, dir)` is valid or the opposite dart `(c + dir.vec, dir + 2)`. -/
theorem edgeCrosses_primalCutEdge_iff (F : Finset (Fin 2 → ℤ)) (c : Fin 2 → ℤ) (dir : Dir2) :
    edgeCrosses F (primalCutEdge c dir) = true ↔
      ValidAt F c dir ∨ ValidAt F (c + dir.vec) (dir + 2) := by
  unfold primalCutEdge edgeCrosses ValidAt
  rw [Sym2.lift_mk, leftSite_reverse, rightSite_reverse]
  by_cases hl : leftSite c dir ∈ F <;> by_cases hr : rightSite c dir ∈ F <;> simp [hl, hr]

end IsingModel

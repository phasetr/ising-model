import IsingModel.Peierls.SingleOrbitEulerian
import IsingModel.Peierls.SingleOrbitEdgeValid

/-!
# Cut directions are boundary darts (FV §3.7.2)

A direction `dir` lies in `cutDirs F c` exactly when the dual vertex `c` carries a boundary dart in
the direction `dir` — either the dart `(c, dir)` (with `F` on its left) or its reverse
`(c + dir.vec, dir + 2)` (with `F` on the right): `mem_cutDirs_iff`. Thus the Eulerian degree
`(cutDirs F c).card` counts the boundary darts incident to `c` in one of the two orientations, the
graph-theoretic shadow of the contour passing through `c`. This is the link between the even-degree
(`card_cut_dirs_even`) and the `nextDart` orbits in the discrete-Jordan argument.

* `mem_cutDirs_iff` — membership in `cutDirs` is a valid dart in one of the two orientations.
* `mem_cutDirs_of_validAt` / `mem_cutDirs_of_validAt_reverse` — either orientation is in `cutDirs`.
* `not_mem_cutDirs_iff` — non-membership is the absence of a boundary dart either way.
* `dir_mem_cutDirs_tail` — a boundary dart's direction is a cut direction at its tail.
* `cutDirs_eq_empty_iff` / `card_cut_dirs_eq_zero_iff` — empty degree is no incident dart.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

/-- **Cut directions are boundary darts**: `dir ∈ cutDirs F c` iff the dart `(c, dir)` is valid or
its reverse `(c + dir.vec, dir + 2)` is. -/
theorem mem_cutDirs_iff (F : Finset (Fin 2 → ℤ)) (c : Fin 2 → ℤ) (dir : Dir2) :
    dir ∈ cutDirs F c ↔ ValidAt F c dir ∨ ValidAt F (c + dir.vec) (dir + 2) := by
  rw [cutDirs, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  exact edgeCrosses_primalCutEdge_iff F c dir

/-- **A valid dart is a cut direction**: if `(c, dir)` is valid then `dir ∈ cutDirs F c`. -/
theorem mem_cutDirs_of_validAt {F : Finset (Fin 2 → ℤ)} {c : Fin 2 → ℤ} {dir : Dir2}
    (h : ValidAt F c dir) : dir ∈ cutDirs F c :=
  (mem_cutDirs_iff F c dir).2 (Or.inl h)

/-- **A reversed valid dart is a cut direction**: if `(c + dir.vec, dir + 2)` is valid then
`dir ∈ cutDirs F c`. -/
theorem mem_cutDirs_of_validAt_reverse {F : Finset (Fin 2 → ℤ)} {c : Fin 2 → ℤ} {dir : Dir2}
    (h : ValidAt F (c + dir.vec) (dir + 2)) : dir ∈ cutDirs F c :=
  (mem_cutDirs_iff F c dir).2 (Or.inr h)

/-- **Non-membership in `cutDirs`** is the absence of a boundary dart in either orientation. -/
theorem not_mem_cutDirs_iff (F : Finset (Fin 2 → ℤ)) (c : Fin 2 → ℤ) (dir : Dir2) :
    dir ∉ cutDirs F c ↔ ¬ ValidAt F c dir ∧ ¬ ValidAt F (c + dir.vec) (dir + 2) := by
  rw [mem_cutDirs_iff, not_or]

/-- **A boundary dart's direction is a cut direction at its tail**. -/
theorem dir_mem_cutDirs_tail {F : Finset (Fin 2 → ℤ)} (d : BoundaryDart F) :
    d.dir ∈ cutDirs F d.tail :=
  mem_cutDirs_of_validAt ⟨d.left_mem, d.right_not_mem⟩

/-- **An empty cut degree** means no boundary dart, in either orientation, is incident to `c`. -/
theorem cutDirs_eq_empty_iff (F : Finset (Fin 2 → ℤ)) (c : Fin 2 → ℤ) :
    cutDirs F c = ∅ ↔ ∀ dir : Dir2, ¬ ValidAt F c dir ∧ ¬ ValidAt F (c + dir.vec) (dir + 2) := by
  rw [Finset.eq_empty_iff_forall_notMem]
  exact forall_congr' (fun dir => not_mem_cutDirs_iff F c dir)

/-- **Zero cut degree** is the empty cut direction set. -/
theorem card_cut_dirs_eq_zero_iff (F : Finset (Fin 2 → ℤ)) (c : Fin 2 → ℤ) :
    (cutDirs F c).card = 0 ↔ cutDirs F c = ∅ :=
  Finset.card_eq_zero

end IsingModel

import IsingModel.Peierls.SingleOrbitFaceCard

/-!
# The Eulerian property of the dual cut (FV §3.7.2)

Transporting the contour's local even/`0`-`2`-`4` degree facts (`ContourEven`) through the
identification of `squareSplitCount` with the cut-direction count
(`squareSplitCount_eq_card_cut_dirs`) gives the **Eulerian property** of the dual cut at the graph
level: at every dual vertex `c` the
number of incident cut directions is even (`card_cut_dirs_even`), at most four
(`card_cut_dirs_le_four`), and in fact `0`, `2`, or `4` (`card_cut_dirs_eq`). Even degree everywhere
is exactly the hypothesis under which a finite graph decomposes into edge-disjoint cycles — the
combinatorial heart of identifying the `nextDart` orbits as the cycles of the contour in the
discrete-Jordan argument.

* `card_cut_dirs_even` / `card_cut_dirs_le_four` / `card_cut_dirs_eq` — the dual-cut degree at `c`.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

/-- The set of directions whose cut edge at `c` is crossed by `F`. -/
private def cutDirs (F : Finset (Fin 2 → ℤ)) (c : Fin 2 → ℤ) : Finset Dir2 :=
  (Finset.univ : Finset Dir2).filter (fun dir => edgeCrosses F (primalCutEdge c dir) = true)

/-- **Even cut-degree at every dual vertex** (the Eulerian property): the number of incident cut
directions at `c` is even. -/
theorem card_cut_dirs_even (F : Finset (Fin 2 → ℤ)) (c : Fin 2 → ℤ) :
    Even (cutDirs F c).card := by
  rw [cutDirs, ← squareSplitCount_eq_card_cut_dirs]
  exact square_split_count_even F c

/-- **At most four cut directions at every dual vertex**. -/
theorem card_cut_dirs_le_four (F : Finset (Fin 2 → ℤ)) (c : Fin 2 → ℤ) :
    (cutDirs F c).card ≤ 4 := by
  rw [cutDirs, ← squareSplitCount_eq_card_cut_dirs]
  exact square_split_count_le_four F c

/-- **The cut-degree is `0`, `2`, or `4`** at every dual vertex. -/
theorem card_cut_dirs_eq (F : Finset (Fin 2 → ℤ)) (c : Fin 2 → ℤ) :
    (cutDirs F c).card = 0 ∨ (cutDirs F c).card = 2 ∨ (cutDirs F c).card = 4 := by
  rw [cutDirs, ← squareSplitCount_eq_card_cut_dirs]
  exact square_split_count_eq F c

end IsingModel

import IsingModel.Peierls.PrimalSquareBoundary

/-!
# The unit square at a dual vertex (FV §3.7.2)

Towards the vertical step of the fixed-ray parity, this file makes `primalSquareBoundaryEdges x`
explicit as the four edges of the unit square with lower-left corner `x` (corners
`x, x+e₀, x+e₁, x+e₀+e₁`). The even square count
(`primalSquareBoundaryEdges_count_even_of_dualIncident_even`) then becomes an even count over the
square's four sides, the ingredient of the vertical telescope (built in a later file).

* `primalCutEdge_unitSquare_*` — the four `primalCutEdge x dir` are the square's
  bottom/right/top/left edges.
* `primalSquareBoundaryEdges_unitSquare` — `primalSquareBoundaryEdges x = {four square edges}`.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

/-- **Bottom edge** of the unit square at `x`: `primalCutEdge x 3 = s(x, x+e₀)`. -/
theorem primalCutEdge_unitSquare_bottom (x : Fin 2 → ℤ) :
    primalCutEdge x 3 = s(x, x + unitVec2 0) := by
  rw [primalCutEdge, Sym2.eq_swap]
  congr 1
  all_goals (funext i; fin_cases i <;>
    simp [leftSite, rightSite, Dir2.turnLeft, Dir2.vec, unitVec2, Pi.add_apply, Pi.sub_apply])

/-- **Right edge** of the unit square at `x`: `primalCutEdge x 0 = s(x+e₀, x+e₀+e₁)`. -/
theorem primalCutEdge_unitSquare_right (x : Fin 2 → ℤ) :
    primalCutEdge x 0 = s(x + unitVec2 0, x + unitVec2 0 + unitVec2 1) := by
  rw [primalCutEdge, Sym2.eq_swap]
  congr 1
  all_goals (funext i; fin_cases i <;>
    simp [leftSite, rightSite, Dir2.turnLeft, Dir2.vec, unitVec2, Pi.add_apply, Pi.sub_apply])

/-- **Top edge** of the unit square at `x`: `primalCutEdge x 1 = s(x+e₁, x+e₁+e₀)`. -/
theorem primalCutEdge_unitSquare_top (x : Fin 2 → ℤ) :
    primalCutEdge x 1 = s(x + unitVec2 1, x + unitVec2 1 + unitVec2 0) := by
  rw [primalCutEdge]
  congr 1
  all_goals (funext i; fin_cases i <;>
    simp [leftSite, rightSite, Dir2.turnLeft, Dir2.vec, unitVec2, Pi.add_apply, Pi.sub_apply])

/-- **Left edge** of the unit square at `x`: `primalCutEdge x 2 = s(x, x+e₁)`. -/
theorem primalCutEdge_unitSquare_left (x : Fin 2 → ℤ) :
    primalCutEdge x 2 = s(x, x + unitVec2 1) := by
  rw [primalCutEdge]
  congr 1
  all_goals (funext i; fin_cases i <;>
    simp [leftSite, rightSite, Dir2.turnLeft, Dir2.vec, unitVec2, Pi.add_apply, Pi.sub_apply])

/-- **The square boundary at `x` is the four unit-square edges** with lower-left corner `x`. -/
theorem primalSquareBoundaryEdges_unitSquare (x : Fin 2 → ℤ) :
    primalSquareBoundaryEdges x =
      ({s(x, x + unitVec2 0), s(x + unitVec2 0, x + unitVec2 0 + unitVec2 1),
        s(x + unitVec2 1, x + unitVec2 1 + unitVec2 0), s(x, x + unitVec2 1)} :
        Finset (Sym2 (Fin 2 → ℤ))) := by
  classical
  ext e
  rw [primalSquareBoundaryEdges, Finset.mem_image]
  simp only [Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨dir, rfl⟩
    fin_cases dir
    · exact Or.inr (Or.inl (primalCutEdge_unitSquare_right x))
    · exact Or.inr (Or.inr (Or.inl (primalCutEdge_unitSquare_top x)))
    · exact Or.inr (Or.inr (Or.inr (primalCutEdge_unitSquare_left x)))
    · exact Or.inl (primalCutEdge_unitSquare_bottom x)
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨3, primalCutEdge_unitSquare_bottom x⟩
    · exact ⟨0, primalCutEdge_unitSquare_right x⟩
    · exact ⟨1, primalCutEdge_unitSquare_top x⟩
    · exact ⟨2, primalCutEdge_unitSquare_left x⟩

end IsingModel

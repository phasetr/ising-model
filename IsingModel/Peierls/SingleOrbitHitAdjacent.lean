import IsingModel.Peierls.SingleOrbitDirCycle
import IsingModel.Peierls.DartOfCut

/-!
# An `F`-neighbour is hit by a rotation (FV §3.7.2)

The precondition of `exists_first_turnLeft_mem` is met whenever the vertex `a` has any
`F`-neighbour: since `turnLeft` reaches every direction in `< 4` steps and the four direction
vectors are exactly `±e₀, ±e₁`, some rotation `a + (turnLeft^[k] dir).vec` equals it and lands in
`F` (`exists_turnLeft_hit_of_adjacent_mem`). Combined with `exists_first_turnLeft_mem` this turns
"`a` has an `F`-neighbour" into the cleared-arc-and-stop data of the wedge advance.

* `exists_turnLeft_hit_of_adjacent_mem` — an `F`-neighbour is reached by some `< 4` left rotation.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

/-- **An `F`-neighbour is hit by a rotation**: if `a'` is an `F`-vertex adjacent to `a`, then some
left rotation `a + (turnLeft^[k] dir).vec` (`k < 4`) lands in `F`. -/
theorem exists_turnLeft_hit_of_adjacent_mem (F : Finset (Fin 2 → ℤ)) (a a' : Fin 2 → ℤ) (dir : Dir2)
    (hadj : (latticeGraph 2).Adj a a') (ha' : a' ∈ F) :
    ∃ k, k < 4 ∧ a + ((Dir2.turnLeft^[k]) dir).vec ∈ F := by
  obtain ⟨δ, hδ⟩ : ∃ δ : Dir2, a + δ.vec = a' := by
    rcases latticeGraph2_adj_cases hadj with h | h | h | h
    · exact ⟨0, by rw [h, show (0 : Dir2).vec = unitVec2 0 from rfl]⟩
    · exact ⟨2, by rw [h, show (2 : Dir2).vec = -unitVec2 0 from rfl]; abel⟩
    · exact ⟨1, by rw [h, show (1 : Dir2).vec = unitVec2 1 from rfl]⟩
    · exact ⟨3, by rw [h, show (3 : Dir2).vec = -unitVec2 1 from rfl]; abel⟩
  obtain ⟨k, hk4, hk⟩ := Dir2.exists_turnLeft_iterate_lt_four dir δ
  exact ⟨k, hk4, by rw [hk, hδ]; exact ha'⟩

end IsingModel

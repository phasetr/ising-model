import IsingModel.Peierls.RightRayVerticalSquare

/-!
# The four sides of the unit square have even total `B`-membership (FV §3.7.2)

The vertical telescope needs the parity statement that the four sides of the unit square at `x` have
an even total `B`-membership. Since the even square count
(`primalSquareBoundaryEdges_count_even_of_dualIncident_even`) counts exactly these four distinct
edges, the count is the sum of the four side indicators, and its evenness gives the parity
statement.

* `unitSquare_count_eq` — `B`-count of `primalSquareBoundaryEdges x` is the sum of the four side
  indicators (the four edges being distinct).
* `unitSquare_sides_even` — under even square count, the sum of the four side indicators is even.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

/-- Helper: two unit-square corner sums are unequal when they differ at a coordinate. -/
private theorem unitSquare_corner_ne (x : Fin 2 → ℤ) :
    x ≠ x + unitVec2 0 ∧ x ≠ x + unitVec2 1 ∧ x + unitVec2 0 ≠ x + unitVec2 1 ∧
      x + unitVec2 0 ≠ x + unitVec2 0 + unitVec2 1 ∧
      x + unitVec2 1 + unitVec2 0 ≠ x ∧ x + unitVec2 1 + unitVec2 0 ≠ x + unitVec2 0 ∧
      x + unitVec2 0 + unitVec2 1 ≠ x ∧ x + unitVec2 0 + unitVec2 1 ≠ x + unitVec2 1 := by
  have e00 : (unitVec2 0) 0 = 1 := by simp [unitVec2]
  have e01 : (unitVec2 0) 1 = 0 := by simp [unitVec2]
  have e10 : (unitVec2 1) 0 = 0 := by simp [unitVec2]
  have e11 : (unitVec2 1) 1 = 1 := by simp [unitVec2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;>
    first
      | (have := congrFun h 0; simp only [Pi.add_apply, e00, e10, add_zero] at this; omega)
      | (have := congrFun h 1; simp only [Pi.add_apply, e01, e11, add_zero] at this; omega)

/-- **The `B`-count of the unit square is the sum of the four side indicators**. -/
theorem unitSquare_count_eq (B : Finset (Sym2 (Fin 2 → ℤ))) (x : Fin 2 → ℤ) :
    (B.filter (fun e => e ∈ primalSquareBoundaryEdges x)).card =
      (if s(x, x + unitVec2 0) ∈ B then 1 else 0) +
        (if s(x + unitVec2 0, x + unitVec2 0 + unitVec2 1) ∈ B then 1 else 0) +
        (if s(x + unitVec2 1, x + unitVec2 1 + unitVec2 0) ∈ B then 1 else 0) +
        (if s(x, x + unitVec2 1) ∈ B then 1 else 0) := by
  classical
  obtain ⟨c01, c02, c12, c03, c04, c05, c06, c07⟩ := unitSquare_corner_ne x
  rw [primalSquareBoundaryEdges_unitSquare, Finset.filter_mem_eq_inter, Finset.inter_comm,
    ← Finset.filter_mem_eq_inter, Finset.card_filter]
  rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  · ring
  · simp only [Finset.mem_singleton, Sym2.eq_iff]; tauto
  · simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]; tauto
  · simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]; tauto

/-- **The four side indicators sum to an even number** under the even square count. -/
theorem unitSquare_sides_even (B : Finset (Sym2 (Fin 2 → ℤ))) (x : Fin 2 → ℤ)
    (hEven : Even ((B.filter (fun e => e ∈ primalSquareBoundaryEdges x)).card)) :
    Even ((if s(x, x + unitVec2 0) ∈ B then 1 else 0) +
      (if s(x + unitVec2 0, x + unitVec2 0 + unitVec2 1) ∈ B then 1 else 0) +
      (if s(x + unitVec2 1, x + unitVec2 1 + unitVec2 0) ∈ B then 1 else 0) +
      (if s(x, x + unitVec2 1) ∈ B then 1 else 0)) := by
  rwa [unitSquare_count_eq] at hEven

end IsingModel

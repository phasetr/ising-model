import IsingModel.Peierls.DartDualCutCard
import IsingModel.Lattice

/-!
# Every cut edge is crossed by a boundary dart (FV §3.7.2)

The reverse of `primalCutEdge`: given a primal cut edge `s(a, b)` of a region `F` (with `a ∈ F`,
`b ∉ F` adjacent in the lattice), there is a boundary dart crossing it. The dart's direction and
tail are recovered from the offset `b - a` by inverting the `leftSite`/`rightSite` formulas (four
cases, one per axis direction). Together with the easy inclusion `dartPrimalCut F ⊆ cutEdges`, this
gives the dart–cut bijection underlying the contour count.

* `latticeGraph2_adj_cases` — a 2D lattice neighbour is one of the four axis shifts.
* `exists_dart_of_cut` — every cut edge is crossed by a boundary dart.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

/-- **A 2D lattice neighbour is an axis shift**: if `a` and `b` are adjacent in `latticeGraph 2`
then `b` is `a` shifted by `±e₀` or `±e₁`. -/
theorem latticeGraph2_adj_cases {a b : Fin 2 → ℤ} (h : (latticeGraph 2).Adj a b) :
    b = a + unitVec2 0 ∨ b = a - unitVec2 0 ∨ b = a + unitVec2 1 ∨ b = a - unitVec2 1 := by
  have h' : |a 0 - b 0| + |a 1 - b 1| = 1 := by
    have hsum : (∑ i : Fin 2, |a i - b i|) = 1 := h
    rwa [Fin.sum_univ_two] at hsum
  have nn0 := abs_nonneg (a 0 - b 0)
  have nn1 := abs_nonneg (a 1 - b 1)
  have key : (|a 0 - b 0| = 0 ∧ |a 1 - b 1| = 1) ∨ (|a 0 - b 0| = 1 ∧ |a 1 - b 1| = 0) := by
    omega
  rcases key with ⟨hk0, hk1⟩ | ⟨hk0, hk1⟩
  · -- coordinate 1 differs by ±1
    rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)] at hk1
    rw [abs_eq_zero, sub_eq_zero] at hk0
    rcases hk1 with hk1 | hk1
    · -- a 1 - b 1 = 1, i.e. b 1 = a 1 - 1
      right; right; right
      funext i; fin_cases i <;>
        simp [unitVec2, Pi.sub_apply] <;> omega
    · right; right; left
      funext i; fin_cases i <;>
        simp [unitVec2, Pi.add_apply] <;> omega
  · -- coordinate 0 differs by ±1
    rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)] at hk0
    rw [abs_eq_zero, sub_eq_zero] at hk1
    rcases hk0 with hk0 | hk0
    · right; left
      funext i; fin_cases i <;>
        simp [unitVec2, Pi.sub_apply] <;> omega
    · left
      funext i; fin_cases i <;>
        simp [unitVec2, Pi.add_apply] <;> omega

/-- **Every cut edge is crossed by a boundary dart**: if `a ∈ F`, `b ∉ F`, and `a, b` are adjacent,
some boundary dart of `F` has primal cut edge `s(a, b)`. -/
theorem exists_dart_of_cut {F : Finset (Fin 2 → ℤ)} {a b : Fin 2 → ℤ}
    (hadj : (latticeGraph 2).Adj a b) (ha : a ∈ F) (hb : b ∉ F) :
    ∃ d : BoundaryDart F, primalCutEdge d.tail d.dir = s(a, b) := by
  rcases latticeGraph2_adj_cases hadj with hb' | hb' | hb' | hb'
  · -- b = a + e₀: dir = 1, tail = a - e₁
    have hL : leftSite (a - unitVec2 1) 1 = a := by
      funext i; fin_cases i <;> simp [leftSite, unitVec2, Pi.sub_apply]
    have hR : rightSite (a - unitVec2 1) 1 = b := by
      refine Eq.trans ?_ hb'.symm
      funext i; fin_cases i <;> simp [rightSite, leftSite, Dir2.turnLeft, Dir2.vec,
        unitVec2, Pi.add_apply, Pi.sub_apply]
    exact ⟨⟨a - unitVec2 1, 1, by rw [hL]; exact ha, by rw [hR]; exact hb⟩,
      by simp only [primalCutEdge, hL, hR]⟩
  · -- b = a - e₀: dir = 3, tail = a - e₀
    have hL : leftSite (a - unitVec2 0) 3 = a := by
      funext i; fin_cases i <;> simp [leftSite, unitVec2, Pi.sub_apply]
    have hR : rightSite (a - unitVec2 0) 3 = b := by
      refine Eq.trans ?_ hb'.symm
      funext i; fin_cases i <;> simp [rightSite, leftSite, Dir2.turnLeft, Dir2.vec,
        unitVec2, Pi.sub_apply]
    exact ⟨⟨a - unitVec2 0, 3, by rw [hL]; exact ha, by rw [hR]; exact hb⟩,
      by simp only [primalCutEdge, hL, hR]⟩
  · -- b = a + e₁: dir = 2, tail = a
    have hL : leftSite a 2 = a := by
      funext i; fin_cases i <;> simp [leftSite, unitVec2]
    have hR : rightSite a 2 = b := by
      refine Eq.trans ?_ hb'.symm
      funext i; fin_cases i <;> simp [rightSite, leftSite, Dir2.turnLeft, Dir2.vec,
        unitVec2, Pi.add_apply]
    exact ⟨⟨a, 2, by rw [hL]; exact ha, by rw [hR]; exact hb⟩,
      by simp only [primalCutEdge, hL, hR]⟩
  · -- b = a - e₁: dir = 0, tail = a - e₀ - e₁
    have hL : leftSite (a - unitVec2 0 - unitVec2 1) 0 = a := by
      funext i; fin_cases i <;> simp [leftSite, unitVec2, Pi.add_apply, Pi.sub_apply]
    have hR : rightSite (a - unitVec2 0 - unitVec2 1) 0 = b := by
      refine Eq.trans ?_ hb'.symm
      funext i; fin_cases i <;> simp [rightSite, leftSite, Dir2.turnLeft, Dir2.vec,
        unitVec2, Pi.add_apply, Pi.sub_apply]
    exact ⟨⟨a - unitVec2 0 - unitVec2 1, 0, by rw [hL]; exact ha, by rw [hR]; exact hb⟩,
      by simp only [primalCutEdge, hL, hR]⟩

end IsingModel

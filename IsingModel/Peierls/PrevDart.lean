import IsingModel.Peierls.DartStepReverse

/-!
# The predecessor dart (FV §3.7.2)

The boundary traversal is invertible: every dart has a unique predecessor. The validity of the
three candidate predecessor darts (with directions `turnRight e.dir`, `e.dir`, `turnLeft e.dir`,
all ending at `e.tail`) reduces — via the site identities — to membership of just two lattice
points to the left of `e.tail`. This makes the predecessor `prevDart e` a clean case split, and
`nextDart (prevDart e) = e` together with finiteness gives that `nextDart` is a bijection, so the
dart orbits are pure cycles.

* `validAt_prev_iff` — predecessor validity at `p` reduces to head-sites at `p`.
* `validAt_prev_candidates_iff` — the three predecessor candidates' validity in two conditions.
* `BoundaryDart.prevDart` — the predecessor dart.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- **Site identity A**: `rightSite t (turnRight (turnRight δ)) = leftSite t (turnLeft δ)`. -/
theorem rightSite_turnRight_turnRight (t : Fin 2 → ℤ) (δ : Dir2) :
    rightSite t δ.turnRight.turnRight = leftSite t δ.turnLeft := by
  fin_cases δ <;>
    (funext i; fin_cases i <;>
      simp [leftSite, rightSite, Dir2.vec, Dir2.turnLeft, Dir2.turnRight, unitVec2, Pi.add_apply,
        Pi.sub_apply])

/-- **Site identity B**: `rightSite t (turnRight δ) = leftSite t (turnLeft (turnLeft δ))`. -/
theorem rightSite_turnRight_eq_leftSite_turnLeft_turnLeft (t : Fin 2 → ℤ) (δ : Dir2) :
    rightSite t δ.turnRight = leftSite t δ.turnLeft.turnLeft := by
  fin_cases δ <;>
    (funext i; fin_cases i <;>
      simp [leftSite, rightSite, Dir2.vec, Dir2.turnLeft, Dir2.turnRight, unitVec2, Pi.add_apply,
        Pi.sub_apply])

/-- **Predecessor validity reduces to head-sites**: a dart with direction `δ` ending at `p` is
valid iff `leftSite p (turnLeft δ) ∈ F` and `rightSite p (turnRight δ) ∉ F`. -/
theorem validAt_prev_iff (p : Fin 2 → ℤ) (δ : Dir2) :
    ValidAt F (p - δ.vec) δ ↔ leftSite p δ.turnLeft ∈ F ∧ rightSite p δ.turnRight ∉ F := by
  have hp : (p - δ.vec) + δ.vec = p := by abel
  have hl : leftSite (p - δ.vec) δ = leftSite p δ.turnLeft := by
    rw [← leftSite_head_turnLeft (p - δ.vec) δ, hp]
  have hr : rightSite (p - δ.vec) δ = rightSite p δ.turnRight := by
    rw [← rightSite_head_turnRight (p - δ.vec) δ, hp]
  rw [ValidAt, hl, hr]

/-- **The three predecessor candidates' validity**: each of the three possible predecessor
directions is valid iff a single membership condition on the two points to the left of `e.tail`
holds (the other site is fixed by `e`'s own validity). -/
theorem validAt_prev_candidates_iff (e : BoundaryDart F) :
    (ValidAt F (e.tail - e.dir.turnRight.vec) e.dir.turnRight ↔
        leftSite e.tail e.dir.turnLeft ∉ F) ∧
      (ValidAt F (e.tail - e.dir.vec) e.dir ↔
        leftSite e.tail e.dir.turnLeft ∈ F ∧ leftSite e.tail e.dir.turnLeft.turnLeft ∉ F) ∧
        (ValidAt F (e.tail - e.dir.turnLeft.vec) e.dir.turnLeft ↔
          leftSite e.tail e.dir.turnLeft.turnLeft ∈ F) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [validAt_prev_iff, Dir2.turnRight_turnLeft, rightSite_turnRight_turnRight,
      and_iff_right e.left_mem]
  · rw [validAt_prev_iff, rightSite_turnRight_eq_leftSite_turnLeft_turnLeft]
  · rw [validAt_prev_iff, Dir2.turnLeft_turnRight, and_iff_left e.right_not_mem]

/-- **The predecessor dart**: the unique dart whose `nextDart` is `e`, given by the reverse
priority (left, straight, right) read off through `validAt_prev_candidates_iff`. -/
noncomputable def BoundaryDart.prevDart (e : BoundaryDart F) : BoundaryDart F := by
  classical
  obtain ⟨hR, hS, hL⟩ := validAt_prev_candidates_iff e
  by_cases h₁ : leftSite e.tail e.dir.turnLeft ∈ F
  · by_cases h₂ : leftSite e.tail e.dir.turnLeft.turnLeft ∈ F
    · exact ⟨e.tail - e.dir.turnLeft.vec, e.dir.turnLeft, (hL.mpr h₂).1, (hL.mpr h₂).2⟩
    · exact ⟨e.tail - e.dir.vec, e.dir, (hS.mpr ⟨h₁, h₂⟩).1, (hS.mpr ⟨h₁, h₂⟩).2⟩
  · exact ⟨e.tail - e.dir.turnRight.vec, e.dir.turnRight, (hR.mpr h₁).1, (hR.mpr h₁).2⟩

end IsingModel

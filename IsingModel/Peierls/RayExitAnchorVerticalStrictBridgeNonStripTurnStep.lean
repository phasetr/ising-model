import IsingModel.Peierls.RayExitAnchorVerticalStrictBridgeNonStripTurn

/-!
# Concrete local turn steps for non-strip strict ray-exit chains (FV §3.7.2)

`RayExitAnchorVerticalStrictBridgeNonStripTurn.lean` introduced finite chains of local turn
certificates as the remaining input for non-strip frontier chains.  This file starts supplying
concrete local geometry for those certificates.

The first step is the straight continuation along a lower-exits-first horizontal strip: when two
consecutive lower ray successors are outside `F` while the corresponding upper successor remains
inside `F`, the left turn is blocked by an `F` site on its right and the straight move is valid.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-! ## Generic congruence helpers -/

/-- A one-step turn certificate may be transported across equality of its target dart. -/
theorem nextDartTurnStep_of_eq {d e f : BoundaryDart F}
    (hstep : NextDartTurnStep d e) (hef : e = f) : NextDartTurnStep d f := by
  rw [← hef]
  exact hstep

/-! ## Lower strip straight steps -/

/-- The straight candidate after a lower `+e₀` strip dart is valid when the next upper ray point
is still in `F` and the next lower ray point is outside `F`. -/
theorem validAt_ltStripDart_straight_succ
    (a b : {x : Fin 2 → ℤ // x ∈ F}) (hup : b.1 = a.1 + unitVec2 1)
    (n : ℕ)
    (hupper₂ : n + 2 ≤ rayExitIndex F b.1 b.2)
    (hlower₂ : ray0 a.1 (n + 2) ∉ F) :
    ValidAt F (ray0 a.1 (n + 1)) 0 := by
  constructor
  · have hL : leftSite (ray0 a.1 (n + 1)) 0 = ray0 b.1 (n + 2) := by
      funext j
      fin_cases j <;>
        simp [hup, leftSite, ray0, unitVec2, Pi.add_apply]; omega
    rw [hL]
    exact rayExitIndex_below b.1 b.2 (n + 2) hupper₂
  · have hR : rightSite (ray0 a.1 (n + 1)) 0 = ray0 a.1 (n + 2) := by
      funext j
      fin_cases j <;>
        simp [rightSite, leftSite, Dir2.turnLeft, Dir2.vec, ray0, unitVec2, Pi.add_apply,
          Pi.sub_apply]; omega
    rw [hR]
    exact hlower₂

/-- The left-turn candidate after a lower `+e₀` strip dart is invalid while the corresponding
upper ray point is still in `F`: its right site is that upper ray point. -/
theorem not_validAt_ltStripDart_turnLeft_succ
    (a b : {x : Fin 2 → ℤ // x ∈ F}) (hup : b.1 = a.1 + unitVec2 1)
    (n : ℕ)
    (hupper₂ : n + 2 ≤ rayExitIndex F b.1 b.2) :
    ¬ ValidAt F (ray0 a.1 (n + 1)) (Dir2.turnLeft 0) := by
  intro hvalid
  have hR : rightSite (ray0 a.1 (n + 1)) (Dir2.turnLeft 0) = ray0 b.1 (n + 2) := by
    funext j
    fin_cases j <;>
      simp [hup, rightSite, leftSite, Dir2.turnLeft, Dir2.vec, ray0, unitVec2,
        Pi.add_apply, Pi.sub_apply]; omega
  have hmem : rightSite (ray0 a.1 (n + 1)) (Dir2.turnLeft 0) ∈ F := by
    rw [hR]
    exact rayExitIndex_below b.1 b.2 (n + 2) hupper₂
  exact hvalid.2 hmem

/-- Consecutive lower strip darts are connected by a certified straight `nextDart` step. -/
theorem nextDartTurnStep_ltStripDart_succ
    (a b : {x : Fin 2 → ℤ // x ∈ F}) (hup : b.1 = a.1 + unitVec2 1)
    (n : ℕ)
    (hupper₁ : n + 1 ≤ rayExitIndex F b.1 b.2)
    (hlower₁ : ray0 a.1 (n + 1) ∉ F)
    (hupper₂ : n + 2 ≤ rayExitIndex F b.1 b.2)
    (hlower₂ : ray0 a.1 (n + 2) ∉ F) :
    NextDartTurnStep
      (rayExitVerticalStrictLtStripDart a b hup n hupper₁ hlower₁)
      (rayExitVerticalStrictLtStripDart a b hup (n + 1) hupper₂ hlower₂) := by
  let d := rayExitVerticalStrictLtStripDart a b hup n hupper₁ hlower₁
  have hL : ¬ ValidAt F d.head d.dir.turnLeft := by
    rw [rayExitVerticalStrictLtStripDart_head, rayExitVerticalStrictLtStripDart_dir]
    exact not_validAt_ltStripDart_turnLeft_succ a b hup n hupper₂
  have hS : ValidAt F d.head d.dir := by
    rw [rayExitVerticalStrictLtStripDart_head, rayExitVerticalStrictLtStripDart_dir]
    exact validAt_ltStripDart_straight_succ a b hup n hupper₂ hlower₂
  refine nextDartTurnStep_of_eq (NextDartTurnStep.straight (d := d) hL hS) ?_
  exact BoundaryDart.ext'
    (by
      change d.head = (rayExitVerticalStrictLtStripDart a b hup (n + 1) hupper₂ hlower₂).tail
      dsimp [d]
      rw [rayExitVerticalStrictLtStripDart_head])
    (by
      change d.dir = (rayExitVerticalStrictLtStripDart a b hup (n + 1) hupper₂ hlower₂).dir
      dsimp [d])

end IsingModel

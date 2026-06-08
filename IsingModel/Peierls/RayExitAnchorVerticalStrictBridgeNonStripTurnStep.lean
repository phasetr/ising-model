import IsingModel.Peierls.RayExitAnchorVerticalStrictBridgeNonStripTurn

/-!
# Concrete local turn steps for non-strip strict ray-exit chains (FV §3.7.2)

`RayExitAnchorVerticalStrictBridgeNonStripTurn.lean` introduced finite chains of local turn
certificates as the remaining input for non-strip frontier chains.  This file starts supplying
concrete local geometry for those certificates.

The first step is the straight continuation along a lower-exits-first horizontal strip: when two
consecutive lower ray successors are outside `F` while the corresponding upper successor remains
inside `F`, the left turn is blocked by an `F` site on its right and the straight move is valid.
The one-step certificate is also lifted to a finite lower strip turn chain.
The endpoint bridge dart is identified with the first strip dart as a trivial chain.
The terminal strip dart turns right into the first lower re-entry frontier dart.

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

/-- A turn-certificate chain may be transported across equality of its target dart. -/
theorem nextDartTurnChain_of_eq {d e f : BoundaryDart F}
    (hchain : NextDartTurnChain d e) (hef : e = f) : NextDartTurnChain d f := by
  rw [← hef]
  exact hchain

/-- Turn-certificate chains compose by transitivity. -/
theorem nextDartTurnChain_trans {d e f : BoundaryDart F}
    (hde : NextDartTurnChain d e) (hef : NextDartTurnChain e f) :
    NextDartTurnChain d f := by
  induction hef with
  | refl =>
      exact hde
  | snoc hchain hstep ih =>
      exact NextDartTurnChain.snoc ih hstep

/-! ## Lower strip straight steps -/

/-- The lower endpoint bridge dart is the first lower strip dart, as a trivial turn chain. -/
theorem nextDartTurnChain_ltBridgeDart_ltStripDart_base
    (a b : {x : Fin 2 → ℤ // x ∈ F}) (hup : b.1 = a.1 + unitVec2 1)
    (hlt : rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2)
    (hupper : rayExitIndex F a.1 a.2 + 1 ≤ rayExitIndex F b.1 b.2)
    (hlower : ray0 a.1 (rayExitIndex F a.1 a.2 + 1) ∉ F) :
    NextDartTurnChain
      (rayExitVerticalStrictLtBridgeDart a b hup hlt)
      (rayExitVerticalStrictLtStripDart a b hup (rayExitIndex F a.1 a.2) hupper hlower) := by
  have heq :
      rayExitVerticalStrictLtBridgeDart a b hup hlt =
        rayExitVerticalStrictLtStripDart a b hup (rayExitIndex F a.1 a.2) hupper hlower :=
    BoundaryDart.ext'
      (by rw [rayExitVerticalStrictLtBridgeDart_tail, rayExitVerticalStrictLtStripDart_tail])
      (by rw [rayExitVerticalStrictLtBridgeDart_dir, rayExitVerticalStrictLtStripDart_dir])
  rw [heq]
  exact NextDartTurnChain.refl _

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

/-- A finite lower strip of horizontal darts is a certified local turn chain. -/
theorem nextDartTurnChain_ltStripDart_iterate
    (a b : {x : Fin 2 → ℤ // x ∈ F}) (hup : b.1 = a.1 + unitVec2 1)
    (n m : ℕ)
    (hupper : n + m + 1 ≤ rayExitIndex F b.1 b.2)
    (hstrip : ∀ t, n + 1 ≤ t → t ≤ n + m + 1 → ray0 a.1 t ∉ F) :
    NextDartTurnChain
      (rayExitVerticalStrictLtStripDart a b hup n
        (by omega) (hstrip (n + 1) (by omega) (by omega)))
      (rayExitVerticalStrictLtStripDart a b hup (n + m)
        hupper (hstrip (n + m + 1) (by omega) (by omega))) := by
  induction m with
  | zero =>
      exact NextDartTurnChain.refl _
  | succ m ih =>
      have hupperPrev : n + m + 1 ≤ rayExitIndex F b.1 b.2 := by omega
      have hstripPrev : ∀ t, n + 1 ≤ t → t ≤ n + m + 1 → ray0 a.1 t ∉ F := by
        intro t ht0 ht1
        exact hstrip t ht0 (by omega)
      have hchain := ih hupperPrev hstripPrev
      exact NextDartTurnChain.snoc hchain
        (nextDartTurnStep_ltStripDart_succ a b hup (n + m)
          hupperPrev (hstrip (n + m + 1) (by omega) (by omega))
          hupper (hstrip (n + (m + 1) + 1) (by omega) (by omega)))

/-! ## Lower strip terminal frontier step -/

/-- At the last lower strip dart before first re-entry, the left-turn candidate is invalid:
its right site is an upper ray point still in `F`. -/
theorem not_validAt_ltStripDart_turnLeft_frontier
    (a b : {x : Fin 2 → ℤ // x ∈ F}) (hup : b.1 = a.1 + unitVec2 1)
    (n : ℕ)
    (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2)
    (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b)
    (hn : n + 2 = rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon) :
    ¬ ValidAt F (ray0 a.1 (n + 1)) (Dir2.turnLeft 0) := by
  intro hvalid
  have hupper₂ : n + 2 ≤ rayExitIndex F b.1 b.2 := by
    have hub := rayExitVerticalStrictLtFirstFrontierIndex_upper_bound a b hgap hnon
    omega
  have hR : rightSite (ray0 a.1 (n + 1)) (Dir2.turnLeft 0) = ray0 b.1 (n + 2) := by
    funext j
    fin_cases j <;>
      simp [hup, rightSite, leftSite, Dir2.turnLeft, Dir2.vec, ray0, unitVec2,
        Pi.add_apply, Pi.sub_apply]; omega
  have hmem : rightSite (ray0 a.1 (n + 1)) (Dir2.turnLeft 0) ∈ F := by
    rw [hR]
    exact rayExitIndex_below b.1 b.2 (n + 2) hupper₂
  exact hvalid.2 hmem

/-- At the last lower strip dart before first re-entry, the straight candidate is invalid:
its right site is the first lower re-entry point in `F`. -/
theorem not_validAt_ltStripDart_straight_frontier
    (a b : {x : Fin 2 → ℤ // x ∈ F})
    (n : ℕ)
    (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2)
    (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b)
    (hn : n + 2 = rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon) :
    ¬ ValidAt F (ray0 a.1 (n + 1)) 0 := by
  intro hvalid
  have hR : rightSite (ray0 a.1 (n + 1)) 0 = ray0 a.1 (n + 2) := by
    funext j
    fin_cases j <;>
      simp [rightSite, leftSite, Dir2.turnLeft, Dir2.vec, ray0, unitVec2, Pi.add_apply,
        Pi.sub_apply]; omega
  have hmem : rightSite (ray0 a.1 (n + 1)) 0 ∈ F := by
    rw [hR]
    have hfront := rayExitVerticalStrictLtFirstFrontierIndex_mem a b hgap hnon
    rwa [← hn] at hfront
  exact hvalid.2 hmem

/-- At the last lower strip dart before first re-entry, the right-turn candidate is valid:
its left site is the first lower re-entry point and its right site is the predecessor outside
`F`. -/
theorem validAt_ltStripDart_turnRight_frontier
    (a b : {x : Fin 2 → ℤ // x ∈ F})
    (n : ℕ)
    (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2)
    (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b)
    (hn : n + 2 = rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon)
    (hlower : ray0 a.1 (n + 1) ∉ F) :
    ValidAt F (ray0 a.1 (n + 1)) (Dir2.turnRight 0) := by
  constructor
  · have hL : leftSite (ray0 a.1 (n + 1)) (Dir2.turnRight 0) = ray0 a.1 (n + 2) := by
      funext j
      fin_cases j <;>
        simp [leftSite, Dir2.turnRight, ray0, unitVec2, Pi.add_apply]; omega
    rw [hL]
    have hfront := rayExitVerticalStrictLtFirstFrontierIndex_mem a b hgap hnon
    rwa [← hn] at hfront
  · have hR : rightSite (ray0 a.1 (n + 1)) (Dir2.turnRight 0) = ray0 a.1 (n + 1) := by
      funext j
      fin_cases j <;>
        simp [rightSite, leftSite, Dir2.turnLeft, Dir2.turnRight, Dir2.vec, ray0,
          unitVec2, Pi.add_apply, Pi.sub_apply]
    rw [hR]
    exact hlower

/-- The last lower strip dart before first re-entry turns right into the lower frontier dart. -/
theorem nextDartTurnStep_ltStripDart_frontier
    (a b : {x : Fin 2 → ℤ // x ∈ F}) (hup : b.1 = a.1 + unitVec2 1)
    (n : ℕ)
    (hupper : n + 1 ≤ rayExitIndex F b.1 b.2)
    (hlower : ray0 a.1 (n + 1) ∉ F)
    (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2)
    (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b)
    (hn : n + 2 = rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon) :
    NextDartTurnStep
      (rayExitVerticalStrictLtStripDart a b hup n hupper hlower)
      (rayExitVerticalStrictLtFrontierDart a b hgap hnon) := by
  let d := rayExitVerticalStrictLtStripDart a b hup n hupper hlower
  have hL : ¬ ValidAt F d.head d.dir.turnLeft := by
    rw [rayExitVerticalStrictLtStripDart_head, rayExitVerticalStrictLtStripDart_dir]
    exact not_validAt_ltStripDart_turnLeft_frontier a b hup n hgap hnon hn
  have hS : ¬ ValidAt F d.head d.dir := by
    rw [rayExitVerticalStrictLtStripDart_head, rayExitVerticalStrictLtStripDart_dir]
    exact not_validAt_ltStripDart_straight_frontier a b n hgap hnon hn
  refine nextDartTurnStep_of_eq (NextDartTurnStep.turnRight (d := d) hL hS) ?_
  exact BoundaryDart.ext'
    (by
      change d.head = (rayExitVerticalStrictLtFrontierDart a b hgap hnon).tail
      dsimp [d]
      rw [rayExitVerticalStrictLtStripDart_head]
      unfold rayExitVerticalStrictLtFrontierDart
      rw [ray0ReentryDart_tail]
      have hpos : 0 < rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon := by
        have hstrict := rayExitVerticalStrictLtFirstFrontierIndex_strict_lower_bound a b hgap hnon
        omega
      rw [ray0_sub_unitVec2_zero_of_pos a.1 hpos]
      congr 1
      omega)
    (by
      change d.dir.turnRight = (rayExitVerticalStrictLtFrontierDart a b hgap hnon).dir
      dsimp [d]
      unfold rayExitVerticalStrictLtFrontierDart
      rw [ray0ReentryDart_dir]
      rfl)

/-- The lower endpoint bridge dart reaches the first lower frontier dart by combining the
bridge base link, the finite lower strip chain, and the terminal right turn. -/
theorem nextDartTurnChain_ltBridgeDart_ltFrontierDart
    (a b : {x : Fin 2 → ℤ // x ∈ F}) (hup : b.1 = a.1 + unitVec2 1)
    (hlt : rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2)
    (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2)
    (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) :
    NextDartTurnChain
      (rayExitVerticalStrictLtBridgeDart a b hup hlt)
      (rayExitVerticalStrictLtFrontierDart a b hgap hnon) := by
  let k := rayExitIndex F a.1 a.2
  let j := rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon
  let m := j - k - 2
  have hstrict : k + 1 < j := by
    dsimp [k, j]
    exact rayExitVerticalStrictLtFirstFrontierIndex_strict_lower_bound a b hgap hnon
  have hupperJ : j ≤ rayExitIndex F b.1 b.2 := by
    dsimp [j]
    exact rayExitVerticalStrictLtFirstFrontierIndex_upper_bound a b hgap hnon
  have hm : k + m + 2 = j := by
    dsimp [m]
    omega
  have hstrip : ∀ t, k + 1 ≤ t → t ≤ k + m + 1 → ray0 a.1 t ∉ F := by
    intro t ht0 ht1
    have ht0' : rayExitIndex F a.1 a.2 + 1 ≤ t := by
      simpa [k] using ht0
    have htlt : t < j := by omega
    exact rayExitVerticalStrictLtFirstFrontierIndex_min a b hgap hnon ht0' (by
      simpa [j] using htlt)
  have hbaseRaw := nextDartTurnChain_ltBridgeDart_ltStripDart_base a b hup hlt
    (by omega) (rayExitIndex_succ_not_mem a.1 a.2)
  have hbase :
      NextDartTurnChain
        (rayExitVerticalStrictLtBridgeDart a b hup hlt)
        (rayExitVerticalStrictLtStripDart a b hup k
          (by omega) (hstrip (k + 1) (by omega) (by omega))) := by
    refine nextDartTurnChain_of_eq hbaseRaw ?_
    exact BoundaryDart.ext'
      (by simp [k])
      (by simp)
  have hupperLast : k + m + 1 ≤ rayExitIndex F b.1 b.2 := by omega
  have hlastNotMem : ray0 a.1 (k + m + 1) ∉ F :=
    hstrip (k + m + 1) (by omega) (by omega)
  have hiter :
      NextDartTurnChain
        (rayExitVerticalStrictLtStripDart a b hup k
          (by omega) (hstrip (k + 1) (by omega) (by omega)))
        (rayExitVerticalStrictLtStripDart a b hup (k + m) hupperLast hlastNotMem) :=
    nextDartTurnChain_ltStripDart_iterate a b hup k m hupperLast hstrip
  have hprefix := nextDartTurnChain_trans hbase hiter
  exact NextDartTurnChain.snoc hprefix
    (nextDartTurnStep_ltStripDart_frontier a b hup (k + m) hupperLast hlastNotMem
      hgap hnon (by simpa [j] using hm))

end IsingModel

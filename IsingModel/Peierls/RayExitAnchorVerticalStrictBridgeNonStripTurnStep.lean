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

variable {F Λ Λd : Finset (Fin 2 → ℤ)}

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

/-! ## Ray-exit anchor straight steps -/

/-- Equal-index upward ray-exit anchors are connected by a certified straight turn step. -/
theorem nextDartTurnStep_rayExitAnchorDartMap_add_e1_of_index_eq
    (x y : {x : Fin 2 → ℤ // x ∈ F}) (hup : y.1 = x.1 + unitVec2 1)
    (hidx : rayExitIndex F y.1 y.2 = rayExitIndex F x.1 x.2) :
    NextDartTurnStep (rayExitAnchorDartMap F x) (rayExitAnchorDartMap F y) := by
  let d := rayExitAnchorDartMap F x
  have hL : ¬ ValidAt F d.head d.dir.turnLeft := by
    intro hvalid
    have hR :
        rightSite (ray0 x.1 (rayExitIndex F x.1 x.2)) (Dir2.turnLeft 1) =
          ray0 y.1 (rayExitIndex F y.1 y.2) := by
      rw [hidx]
      funext j
      fin_cases j <;>
        simp [hup, rightSite, leftSite, Dir2.turnLeft, Dir2.vec, ray0, unitVec2,
          Pi.add_apply, Pi.sub_apply]
    have hmem : rightSite d.head d.dir.turnLeft ∈ F := by
      rw [rayExitAnchorDartMap_head, rayExitAnchorDartMap_dir, hR]
      exact rayExitIndex_mem y.1 y.2
    exact hvalid.2 hmem
  have hS : ValidAt F d.head d.dir := by
    constructor
    · have hleft :
          leftSite (ray0 x.1 (rayExitIndex F x.1 x.2)) 1 =
            ray0 y.1 (rayExitIndex F y.1 y.2) := by
        rw [hidx]
        funext j
        fin_cases j <;>
          simp [hup, leftSite, ray0, unitVec2, Pi.add_apply]
      rw [rayExitAnchorDartMap_head, rayExitAnchorDartMap_dir, hleft]
      exact rayExitIndex_mem y.1 y.2
    · have hright :
          rightSite (ray0 x.1 (rayExitIndex F x.1 x.2)) 1 =
            ray0 y.1 (rayExitIndex F y.1 y.2 + 1) := by
        rw [hidx]
        funext j
        fin_cases j
        · simp [hup, rightSite, leftSite, Dir2.turnLeft, Dir2.vec, ray0, unitVec2,
            Pi.add_apply, Pi.sub_apply]
          omega
        · simp [hup, rightSite, leftSite, Dir2.turnLeft, Dir2.vec, ray0, unitVec2,
            Pi.add_apply, Pi.sub_apply]
      rw [rayExitAnchorDartMap_head, rayExitAnchorDartMap_dir, hright]
      exact rayExitIndex_succ_not_mem y.1 y.2
  refine nextDartTurnStep_of_eq (NextDartTurnStep.straight (d := d) hL hS) ?_
  exact BoundaryDart.ext'
    (by
      change d.head = (rayExitAnchorDartMap F y).tail
      dsimp [d]
      rw [rayExitAnchorDart_head, rayExitAnchorDart_tail, hidx]
      funext j
      fin_cases j <;>
        simp [hup, ray0, unitVec2, Pi.add_apply, Pi.sub_apply])
    (by
      change d.dir = (rayExitAnchorDartMap F y).dir
      dsimp [d]
      rw [rayExitAnchorDart_dir, rayExitAnchorDart_dir])

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

/-! ## Lower frontier remaining input -/

/-- Remaining lower-exits-first turn-chain data after the lower bridge-to-frontier leg has been
discharged: only the first lower frontier dart to the upper ray-exit anchor remains. -/
def RayExitVerticalStrictLtFrontierAnchorTurnChain (F : Finset (Fin 2 → ℤ)) : Prop :=
  ∀ a b : {x : Fin 2 → ℤ // x ∈ F},
    (hup : b.1 = a.1 + unitVec2 1) →
      (hlt : rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2) →
        (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2) →
          (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) →
            NextDartTurnChain
              (rayExitVerticalStrictLtFrontierDart a b hgap hnon)
              (rayExitAnchorDartMap F b)

/-! ## Lower frontier-anchor split input -/

/-- The first lower re-entry site, packaged as a site of `F`. -/
noncomputable def rayExitVerticalStrictLtFrontierSite
    (a b : {x : Fin 2 → ℤ // x ∈ F})
    (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2)
    (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) : {x : Fin 2 → ℤ // x ∈ F} :=
  ⟨ray0 a.1 (rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon),
    rayExitVerticalStrictLtFirstFrontierIndex_mem a b hgap hnon⟩

/-- The value of the packaged first lower re-entry site. -/
@[simp] theorem rayExitVerticalStrictLtFrontierSite_val
    (a b : {x : Fin 2 → ℤ // x ∈ F})
    (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2)
    (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) :
    (rayExitVerticalStrictLtFrontierSite a b hgap hnon).1 =
      ray0 a.1 (rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon) :=
  rfl

/-- The lower frontier dart's left site is the packaged first lower re-entry site. -/
theorem rayExitVerticalStrictLtFrontierDart_left_frontierSite
    (a b : {x : Fin 2 → ℤ // x ∈ F})
    (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2)
    (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) :
    (rayExitVerticalStrictLtFrontierDart a b hgap hnon).left =
      (rayExitVerticalStrictLtFrontierSite a b hgap hnon).1 := by
  rw [rayExitVerticalStrictLtFrontierDart_left]
  rfl

/-- The upper ray point at the same index as the first lower re-entry, packaged as a site of `F`.
It lies in `F` because the lower first frontier index is still at or before the upper first-exit
index. -/
noncomputable def rayExitVerticalStrictLtFrontierUpperSite
    (a b : {x : Fin 2 → ℤ // x ∈ F})
    (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2)
    (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) : {x : Fin 2 → ℤ // x ∈ F} :=
  ⟨ray0 b.1 (rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon),
    rayExitIndex_below b.1 b.2
      (rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon)
      (rayExitVerticalStrictLtFirstFrontierIndex_upper_bound a b hgap hnon)⟩

/-- The value of the upper ray point at the first lower frontier index. -/
@[simp] theorem rayExitVerticalStrictLtFrontierUpperSite_val
    (a b : {x : Fin 2 → ℤ // x ∈ F})
    (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2)
    (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) :
    (rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon).1 =
      ray0 b.1 (rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon) :=
  rfl

/-- The packaged upper ray point sits one vertical step above the packaged lower frontier site. -/
theorem rayExitVerticalStrictLtFrontierUpperSite_eq_frontierSite_add_e1
    (a b : {x : Fin 2 → ℤ // x ∈ F}) (hup : b.1 = a.1 + unitVec2 1)
    (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2)
    (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) :
    (rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon).1 =
      (rayExitVerticalStrictLtFrontierSite a b hgap hnon).1 + unitVec2 1 := by
  funext j
  fin_cases j <;>
    simp [hup, ray0, unitVec2, Pi.add_apply]

/-- The upper-prefix site's first-exit index is the remaining length to the original upper
ray's first exit. -/
theorem rayExitIndex_ltFrontierUpperSite_eq
    (a b : {x : Fin 2 → ℤ // x ∈ F})
    (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2)
    (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) :
    rayExitIndex F
        (rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon).1
        (rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon).2 =
      rayExitIndex F b.1 b.2 -
        rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon := by
  simpa [rayExitVerticalStrictLtFrontierUpperSite] using
    rayExitIndex_shift b.1 b.2
      (rayExitVerticalStrictLtFirstFrontierIndex_upper_bound a b hgap hnon)

/-- The upper prefix site's ray-exit anchor is the original upper site's ray-exit anchor. -/
theorem rayExitAnchorDartMap_ltFrontierUpperSite_eq
    (a b : {x : Fin 2 → ℤ // x ∈ F})
    (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2)
    (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) :
    rayExitAnchorDartMap F (rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon) =
      rayExitAnchorDartMap F b := by
  exact rayExitAnchorDartMap_prefix_eq b
    (rayExitVerticalStrictLtFirstFrontierIndex_upper_bound a b hgap hnon)

/-- A split form of the lower frontier-anchor input: first reach the ray-exit anchor of the
frontier site itself, then reach the upper site's ray-exit anchor. -/
def RayExitVerticalStrictLtFrontierAnchorSplitTurnChain
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  ∀ a b : {x : Fin 2 → ℤ // x ∈ F},
    (hup : b.1 = a.1 + unitVec2 1) →
      (hlt : rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2) →
        (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2) →
          (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) →
            NextDartTurnChain
                (rayExitVerticalStrictLtFrontierDart a b hgap hnon)
                (rayExitAnchorDartMap F
                  (rayExitVerticalStrictLtFrontierSite a b hgap hnon)) ∧
            NextDartTurnChain
                (rayExitAnchorDartMap F
                  (rayExitVerticalStrictLtFrontierSite a b hgap hnon))
                (rayExitAnchorDartMap F b)

/-- Split lower frontier-anchor data recover the one-piece lower frontier-anchor input. -/
theorem rayExitVerticalStrictLtFrontierAnchorTurnChain_of_splitTurnChain
    (hsplit : RayExitVerticalStrictLtFrontierAnchorSplitTurnChain F) :
    RayExitVerticalStrictLtFrontierAnchorTurnChain F := by
  intro a b hup hlt hgap hnon
  exact nextDartTurnChain_trans (hsplit a b hup hlt hgap hnon).1
    (hsplit a b hup hlt hgap hnon).2

/-! ## Lower frontier-site-anchor input -/

/-- The remaining lower-exits-first local turn-chain data after the lower bridge-to-frontier leg
and the frontier-dart-to-frontier-site-anchor leg are discharged: only the frontier site's
ray-exit anchor to the upper site's ray-exit anchor remains. -/
def RayExitVerticalStrictLtFrontierSiteAnchorTurnChain
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  ∀ a b : {x : Fin 2 → ℤ // x ∈ F},
    (hup : b.1 = a.1 + unitVec2 1) →
      (hlt : rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2) →
        (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2) →
          (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) →
            NextDartTurnChain
              (rayExitAnchorDartMap F (rayExitVerticalStrictLtFrontierSite a b hgap hnon))
              (rayExitAnchorDartMap F b)

/-- A split form of the frontier-site-anchor input: first reach the anchor of the upper ray point
at the same frontier index, whose anchor is then identified with the original upper site's anchor
by ray-prefix stability. -/
def RayExitVerticalStrictLtFrontierUpperSiteAnchorTurnChain
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  ∀ a b : {x : Fin 2 → ℤ // x ∈ F},
    (hup : b.1 = a.1 + unitVec2 1) →
      (hlt : rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2) →
        (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2) →
          (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) →
            NextDartTurnChain
              (rayExitAnchorDartMap F (rayExitVerticalStrictLtFrontierSite a b hgap hnon))
              (rayExitAnchorDartMap F
                (rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon))

/-- The upper-prefix split input recovers the frontier-site-anchor input by ray-prefix stability
on the upper ray. -/
theorem rayExitVerticalStrictLtFrontierSiteAnchorTurnChain_of_upperSiteAnchorTurnChain
    (hupper : RayExitVerticalStrictLtFrontierUpperSiteAnchorTurnChain F) :
    RayExitVerticalStrictLtFrontierSiteAnchorTurnChain F := by
  intro a b hup hlt hgap hnon
  exact nextDartTurnChain_of_eq (hupper a b hup hlt hgap hnon)
    (rayExitAnchorDartMap_ltFrontierUpperSite_eq a b hgap hnon)

/-! ## Lower frontier-site to upper-prefix anchor reachability -/

/-- A weaker split form of the frontier-site-anchor input: it only asks for `DartReachable` from
the lower frontier site's ray-exit anchor to the upper-prefix site's ray-exit anchor.  This is the
form consumed by the edge-connected route. -/
def RayExitVerticalStrictLtFrontierUpperSiteAnchorReachable
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  ∀ a b : {x : Fin 2 → ℤ // x ∈ F},
    (hup : b.1 = a.1 + unitVec2 1) →
      (hlt : rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2) →
        (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2) →
          (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) →
            DartReachable F
              (rayExitAnchorDartMap F (rayExitVerticalStrictLtFrontierSite a b hgap hnon))
              (rayExitAnchorDartMap F
                (rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon))

/-- The remaining strict subcase of the lower frontier-site to upper-prefix anchor leg: if the
frontier site and upper-prefix site have unequal ray-exit indices, their anchors must be reachable.
The equal-index subcase is closed by shared-vertex geometry. -/
def RayExitVerticalStrictLtFrontierUpperSiteAnchorStrictReachable
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  ∀ a b : {x : Fin 2 → ℤ // x ∈ F},
    (hup : b.1 = a.1 + unitVec2 1) →
      (hlt : rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2) →
        (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2) →
          (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) →
            rayExitIndex F
                (rayExitVerticalStrictLtFrontierSite a b hgap hnon).1
                (rayExitVerticalStrictLtFrontierSite a b hgap hnon).2 ≠
              rayExitIndex F
                (rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon).1
                (rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon).2 →
              DartReachable F
                (rayExitAnchorDartMap F
                  (rayExitVerticalStrictLtFrontierSite a b hgap hnon))
                (rayExitAnchorDartMap F
                  (rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon))

/-- Ordered lower frontier-site to upper-prefix anchor data for the local-index increasing
subcase. -/
def RayExitVerticalStrictLtFrontierUpperSiteAnchorLtReachable
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  ∀ a b : {x : Fin 2 → ℤ // x ∈ F},
    (hup : b.1 = a.1 + unitVec2 1) →
      (hlt : rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2) →
        (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2) →
          (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) →
            rayExitIndex F
                (rayExitVerticalStrictLtFrontierSite a b hgap hnon).1
                (rayExitVerticalStrictLtFrontierSite a b hgap hnon).2 <
              rayExitIndex F
                (rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon).1
                (rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon).2 →
              DartReachable F
                (rayExitAnchorDartMap F
                  (rayExitVerticalStrictLtFrontierSite a b hgap hnon))
                (rayExitAnchorDartMap F
                  (rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon))

/-- Ordered lower frontier-site to upper-prefix anchor data for the local-index decreasing
subcase. -/
def RayExitVerticalStrictLtFrontierUpperSiteAnchorGtReachable
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  ∀ a b : {x : Fin 2 → ℤ // x ∈ F},
    (hup : b.1 = a.1 + unitVec2 1) →
      (hlt : rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2) →
        (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2) →
          (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) →
            rayExitIndex F
                (rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon).1
                (rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon).2 <
              rayExitIndex F
                (rayExitVerticalStrictLtFrontierSite a b hgap hnon).1
                (rayExitVerticalStrictLtFrontierSite a b hgap hnon).2 →
              DartReachable F
                (rayExitAnchorDartMap F
                  (rayExitVerticalStrictLtFrontierSite a b hgap hnon))
                (rayExitAnchorDartMap F
                  (rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon))

/-- Ordered lower frontier-site to upper-prefix anchor data split by local ray-exit index order. -/
def RayExitVerticalStrictLtFrontierUpperSiteAnchorOrderedReachable
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  RayExitVerticalStrictLtFrontierUpperSiteAnchorLtReachable F ∧
    RayExitVerticalStrictLtFrontierUpperSiteAnchorGtReachable F

/-- Residual-index form of the local-index increasing subcase: the upper-prefix site's
ray-exit index is written as the remaining upper ray length from the lower frontier index. -/
def RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtReachable
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  ∀ a b : {x : Fin 2 → ℤ // x ∈ F},
    (hup : b.1 = a.1 + unitVec2 1) →
      (hlt : rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2) →
        (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2) →
          (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) →
            rayExitIndex F
                (rayExitVerticalStrictLtFrontierSite a b hgap hnon).1
                (rayExitVerticalStrictLtFrontierSite a b hgap hnon).2 <
              rayExitIndex F b.1 b.2 -
                rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon →
              DartReachable F
                (rayExitAnchorDartMap F
                  (rayExitVerticalStrictLtFrontierSite a b hgap hnon))
                (rayExitAnchorDartMap F
                  (rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon))

/-- Residual-index form of the local-index decreasing subcase. -/
def RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualGtReachable
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  ∀ a b : {x : Fin 2 → ℤ // x ∈ F},
    (hup : b.1 = a.1 + unitVec2 1) →
      (hlt : rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2) →
        (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2) →
          (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) →
            rayExitIndex F b.1 b.2 -
                rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon <
              rayExitIndex F
                (rayExitVerticalStrictLtFrontierSite a b hgap hnon).1
                (rayExitVerticalStrictLtFrontierSite a b hgap hnon).2 →
              DartReachable F
                (rayExitAnchorDartMap F
                  (rayExitVerticalStrictLtFrontierSite a b hgap hnon))
                (rayExitAnchorDartMap F
                  (rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon))

/-- Residual-index ordered data split the remaining lower frontier-site to upper-prefix anchor
leg by comparing the lower frontier site's ray-exit index with the remaining upper ray length. -/
def RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualOrderedReachable
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtReachable F ∧
    RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualGtReachable F

/-- Genuine-gap residual-index data for the local-index increasing subcase.  The adjacent
residual case is automatic by the existing lower-first bridge shared-vertex geometry. -/
def RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtGapReachable
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  ∀ a b : {x : Fin 2 → ℤ // x ∈ F},
    (hup : b.1 = a.1 + unitVec2 1) →
      (hlt : rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2) →
        (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2) →
          (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) →
            rayExitIndex F
                  (rayExitVerticalStrictLtFrontierSite a b hgap hnon).1
                  (rayExitVerticalStrictLtFrontierSite a b hgap hnon).2 + 1 <
              rayExitIndex F b.1 b.2 -
                rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon →
              DartReachable F
                (rayExitAnchorDartMap F
                  (rayExitVerticalStrictLtFrontierSite a b hgap hnon))
                (rayExitAnchorDartMap F
                  (rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon))

/-- Genuine-gap residual-index data for the local-index decreasing subcase.  The adjacent
residual case is automatic by the existing upper-first bridge shared-vertex geometry. -/
def RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualGtGapReachable
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  ∀ a b : {x : Fin 2 → ℤ // x ∈ F},
    (hup : b.1 = a.1 + unitVec2 1) →
      (hlt : rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2) →
        (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2) →
          (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) →
            rayExitIndex F b.1 b.2 -
                  rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon + 1 <
              rayExitIndex F
                (rayExitVerticalStrictLtFrontierSite a b hgap hnon).1
                (rayExitVerticalStrictLtFrontierSite a b hgap hnon).2 →
              DartReachable F
                (rayExitAnchorDartMap F
                  (rayExitVerticalStrictLtFrontierSite a b hgap hnon))
                (rayExitAnchorDartMap F
                  (rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon))

/-- Residual-index gap data split the remaining lower frontier-site to upper-prefix anchor leg
after the adjacent residual cases have been discharged. -/
def RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualGapReachable
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtGapReachable F ∧
    RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualGtGapReachable F

/-- The adjacent residual lower-first subcase is a two-step bridge/shared-vertex chain from the
lower frontier site's ray-exit anchor to the upper-prefix site's ray-exit anchor. -/
theorem dartReachable_rayExitAnchorDartMap_ltFrontierUpperSite_of_residualLtSucc
    (a b : {x : Fin 2 → ℤ // x ∈ F}) (hup : b.1 = a.1 + unitVec2 1)
    (_hlt : rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2)
    (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2)
    (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b)
    (hsucc : rayExitIndex F b.1 b.2 -
        rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon =
      rayExitIndex F
          (rayExitVerticalStrictLtFrontierSite a b hgap hnon).1
          (rayExitVerticalStrictLtFrontierSite a b hgap hnon).2 + 1) :
    DartReachable F
      (rayExitAnchorDartMap F (rayExitVerticalStrictLtFrontierSite a b hgap hnon))
      (rayExitAnchorDartMap F
        (rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon)) := by
  let c := rayExitVerticalStrictLtFrontierSite a b hgap hnon
  let u := rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon
  have hupCU : u.1 = c.1 + unitVec2 1 := by
    dsimp [c, u]
    exact rayExitVerticalStrictLtFrontierUpperSite_eq_frontierSite_add_e1
      a b hup hgap hnon
  have hidxU :
      rayExitIndex F u.1 u.2 =
        rayExitIndex F b.1 b.2 -
          rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon := by
    simpa [u] using rayExitIndex_ltFrontierUpperSite_eq a b hgap hnon
  have hltCU : rayExitIndex F c.1 c.2 < rayExitIndex F u.1 u.2 := by
    rw [hidxU]
    dsimp [c] at hsucc ⊢
    omega
  have hsuccCU : rayExitIndex F u.1 u.2 = rayExitIndex F c.1 c.2 + 1 := by
    rw [hidxU]
    exact hsucc
  exact (dartReachable_rayExitAnchorDartMap_ltBridgeDart c u hupCU hltCU).trans
    (dartReachable_ltBridgeDart_rayExitAnchorDartMap_of_succ c u hupCU hltCU hsuccCU)

/-- The adjacent residual upper-first subcase is a two-step bridge/shared-vertex chain from the
lower frontier site's ray-exit anchor to the upper-prefix site's ray-exit anchor. -/
theorem dartReachable_rayExitAnchorDartMap_ltFrontierUpperSite_of_residualGtSucc
    (a b : {x : Fin 2 → ℤ // x ∈ F}) (hup : b.1 = a.1 + unitVec2 1)
    (_hlt : rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2)
    (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2)
    (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b)
    (hsucc :
      rayExitIndex F
          (rayExitVerticalStrictLtFrontierSite a b hgap hnon).1
          (rayExitVerticalStrictLtFrontierSite a b hgap hnon).2 =
        rayExitIndex F b.1 b.2 -
            rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon + 1) :
    DartReachable F
      (rayExitAnchorDartMap F (rayExitVerticalStrictLtFrontierSite a b hgap hnon))
      (rayExitAnchorDartMap F
        (rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon)) := by
  let c := rayExitVerticalStrictLtFrontierSite a b hgap hnon
  let u := rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon
  have hupCU : u.1 = c.1 + unitVec2 1 := by
    dsimp [c, u]
    exact rayExitVerticalStrictLtFrontierUpperSite_eq_frontierSite_add_e1
      a b hup hgap hnon
  have hidxU :
      rayExitIndex F u.1 u.2 =
        rayExitIndex F b.1 b.2 -
          rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon := by
    simpa [u] using rayExitIndex_ltFrontierUpperSite_eq a b hgap hnon
  have hgtCU : rayExitIndex F u.1 u.2 < rayExitIndex F c.1 c.2 := by
    rw [hidxU]
    dsimp [c] at hsucc ⊢
    omega
  have hsuccCU : rayExitIndex F c.1 c.2 = rayExitIndex F u.1 u.2 + 1 := by
    rw [hidxU]
    exact hsucc
  exact
    (dartReachable_rayExitAnchorDartMap_gtBridgeDart_of_succ c u hupCU hgtCU hsuccCU).trans
      (dartReachable_rayExitAnchorDartMap_gtBridgeDart c u hupCU hgtCU).symm

/-- Gap-reduced residual lower-first data recover the full residual lower-first input because the
adjacent residual case is automatic. -/
theorem rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtReachable_of_gap
    (hgapReach : RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtGapReachable F) :
    RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtReachable F := by
  intro a b hup hlt hgap hnon hidx
  by_cases hsucc : rayExitIndex F b.1 b.2 -
      rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon =
    rayExitIndex F
        (rayExitVerticalStrictLtFrontierSite a b hgap hnon).1
        (rayExitVerticalStrictLtFrontierSite a b hgap hnon).2 + 1
  · exact dartReachable_rayExitAnchorDartMap_ltFrontierUpperSite_of_residualLtSucc
      a b hup hlt hgap hnon hsucc
  · exact hgapReach a b hup hlt hgap hnon (by omega)

/-- Gap-reduced residual upper-first data recover the full residual upper-first input because the
adjacent residual case is automatic. -/
theorem rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualGtReachable_of_gap
    (hgapReach : RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualGtGapReachable F) :
    RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualGtReachable F := by
  intro a b hup hlt hgap hnon hidx
  by_cases hsucc :
      rayExitIndex F
          (rayExitVerticalStrictLtFrontierSite a b hgap hnon).1
          (rayExitVerticalStrictLtFrontierSite a b hgap hnon).2 =
        rayExitIndex F b.1 b.2 -
            rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon + 1
  · exact dartReachable_rayExitAnchorDartMap_ltFrontierUpperSite_of_residualGtSucc
      a b hup hlt hgap hnon hsucc
  · exact hgapReach a b hup hlt hgap hnon (by omega)

/-- Gap-reduced residual data recover the residual ordered input. -/
theorem rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualOrderedReachable_of_gap
    (hgapReach :
      RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualGapReachable F) :
    RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualOrderedReachable F :=
  ⟨rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtReachable_of_gap hgapReach.1,
    rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualGtReachable_of_gap hgapReach.2⟩

/-- Non-strip residual lower-first data for the local frontier-site to upper-prefix anchor leg.
The straight residual strip subcase is automatic by the existing lower-first strip chain. -/
def RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtNonStripReachable
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  ∀ a b : {x : Fin 2 → ℤ // x ∈ F},
    (hup : b.1 = a.1 + unitVec2 1) →
      (hlt : rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2) →
        (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2) →
          (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) →
            (hresGap :
              rayExitIndex F
                    (rayExitVerticalStrictLtFrontierSite a b hgap hnon).1
                    (rayExitVerticalStrictLtFrontierSite a b hgap hnon).2 + 1 <
                rayExitIndex F b.1 b.2 -
                  rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon) →
              ¬ RayExitVerticalStrictLtGapStrip F
                (rayExitVerticalStrictLtFrontierSite a b hgap hnon)
                (rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon) →
                DartReachable F
                  (rayExitAnchorDartMap F
                    (rayExitVerticalStrictLtFrontierSite a b hgap hnon))
                  (rayExitAnchorDartMap F
                    (rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon))

/-- Non-strip residual upper-first data for the local frontier-site to upper-prefix anchor leg.
The straight residual strip subcase is automatic by the existing upper-first strip chain. -/
def RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualGtNonStripReachable
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  ∀ a b : {x : Fin 2 → ℤ // x ∈ F},
    (hup : b.1 = a.1 + unitVec2 1) →
      (hlt : rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2) →
        (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2) →
          (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) →
            (hresGap :
              rayExitIndex F b.1 b.2 -
                    rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon + 1 <
                rayExitIndex F
                  (rayExitVerticalStrictLtFrontierSite a b hgap hnon).1
                  (rayExitVerticalStrictLtFrontierSite a b hgap hnon).2) →
              ¬ RayExitVerticalStrictGtGapStrip F
                (rayExitVerticalStrictLtFrontierSite a b hgap hnon)
                (rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon) →
                DartReachable F
                  (rayExitAnchorDartMap F
                    (rayExitVerticalStrictLtFrontierSite a b hgap hnon))
                  (rayExitAnchorDartMap F
                    (rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon))

/-- Non-strip residual data split the remaining genuine residual-gap lower input after straight
strip residual subcases have been discharged. -/
def RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualNonStripReachable
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtNonStripReachable F ∧
    RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualGtNonStripReachable F

/-- A straight lower-first residual strip closes the local frontier-site to upper-prefix anchor
leg by the existing finite strip chain. -/
theorem dartReachable_rayExitAnchorDartMap_ltFrontierUpperSite_of_residualLtStrip
    (a b : {x : Fin 2 → ℤ // x ∈ F}) (hup : b.1 = a.1 + unitVec2 1)
    (_hlt : rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2)
    (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2)
    (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b)
    (hresGap :
      rayExitIndex F
            (rayExitVerticalStrictLtFrontierSite a b hgap hnon).1
            (rayExitVerticalStrictLtFrontierSite a b hgap hnon).2 + 1 <
        rayExitIndex F b.1 b.2 -
          rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon)
    (hstrip : RayExitVerticalStrictLtGapStrip F
      (rayExitVerticalStrictLtFrontierSite a b hgap hnon)
      (rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon)) :
    DartReachable F
      (rayExitAnchorDartMap F (rayExitVerticalStrictLtFrontierSite a b hgap hnon))
      (rayExitAnchorDartMap F
        (rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon)) := by
  let c := rayExitVerticalStrictLtFrontierSite a b hgap hnon
  let u := rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon
  have hupCU : u.1 = c.1 + unitVec2 1 := by
    dsimp [c, u]
    exact rayExitVerticalStrictLtFrontierUpperSite_eq_frontierSite_add_e1
      a b hup hgap hnon
  have hidxU :
      rayExitIndex F u.1 u.2 =
        rayExitIndex F b.1 b.2 -
          rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon := by
    simpa [u] using rayExitIndex_ltFrontierUpperSite_eq a b hgap hnon
  have hltCU : rayExitIndex F c.1 c.2 < rayExitIndex F u.1 u.2 := by
    rw [hidxU]
    dsimp [c] at hresGap ⊢
    omega
  rcases hstrip with ⟨m, hm, hout⟩
  exact (dartReachable_rayExitAnchorDartMap_ltBridgeDart c u hupCU hltCU).trans
    (dartReachable_ltBridgeDart_rayExitAnchorDartMap_of_strip c u hupCU hltCU
      m hm hout)

/-- A straight upper-first residual strip closes the local frontier-site to upper-prefix anchor
leg by the existing finite strip chain. -/
theorem dartReachable_rayExitAnchorDartMap_ltFrontierUpperSite_of_residualGtStrip
    (a b : {x : Fin 2 → ℤ // x ∈ F}) (hup : b.1 = a.1 + unitVec2 1)
    (_hlt : rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2)
    (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2)
    (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b)
    (hresGap :
      rayExitIndex F b.1 b.2 -
            rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon + 1 <
        rayExitIndex F
          (rayExitVerticalStrictLtFrontierSite a b hgap hnon).1
          (rayExitVerticalStrictLtFrontierSite a b hgap hnon).2)
    (hstrip : RayExitVerticalStrictGtGapStrip F
      (rayExitVerticalStrictLtFrontierSite a b hgap hnon)
      (rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon)) :
    DartReachable F
      (rayExitAnchorDartMap F (rayExitVerticalStrictLtFrontierSite a b hgap hnon))
      (rayExitAnchorDartMap F
        (rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon)) := by
  let c := rayExitVerticalStrictLtFrontierSite a b hgap hnon
  let u := rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon
  have hupCU : u.1 = c.1 + unitVec2 1 := by
    dsimp [c, u]
    exact rayExitVerticalStrictLtFrontierUpperSite_eq_frontierSite_add_e1
      a b hup hgap hnon
  have hidxU :
      rayExitIndex F u.1 u.2 =
        rayExitIndex F b.1 b.2 -
          rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon := by
    simpa [u] using rayExitIndex_ltFrontierUpperSite_eq a b hgap hnon
  have hgtCU : rayExitIndex F u.1 u.2 < rayExitIndex F c.1 c.2 := by
    rw [hidxU]
    dsimp [c] at hresGap ⊢
    omega
  rcases hstrip with ⟨m, hm, hout⟩
  exact
    (dartReachable_rayExitAnchorDartMap_gtBridgeDart_of_strip c u hupCU hgtCU
      m hm hout).trans
      (dartReachable_rayExitAnchorDartMap_gtBridgeDart c u hupCU hgtCU).symm

/-- Non-strip residual lower-first data recover the residual lower-first gap input because
straight residual strips are automatic. -/
theorem rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtGapReachable_of_nonStrip
    (hnonStrip :
      RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtNonStripReachable F) :
    RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtGapReachable F := by
  intro a b hup hlt hgap hnon hresGap
  let c := rayExitVerticalStrictLtFrontierSite a b hgap hnon
  let u := rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon
  by_cases hstrip : RayExitVerticalStrictLtGapStrip F c u
  · exact dartReachable_rayExitAnchorDartMap_ltFrontierUpperSite_of_residualLtStrip
      a b hup hlt hgap hnon hresGap hstrip
  · exact hnonStrip a b hup hlt hgap hnon hresGap hstrip

/-- Non-strip residual upper-first data recover the residual upper-first gap input because
straight residual strips are automatic. -/
theorem rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualGtGapReachable_of_nonStrip
    (hnonStrip :
      RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualGtNonStripReachable F) :
    RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualGtGapReachable F := by
  intro a b hup hlt hgap hnon hresGap
  let c := rayExitVerticalStrictLtFrontierSite a b hgap hnon
  let u := rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon
  by_cases hstrip : RayExitVerticalStrictGtGapStrip F c u
  · exact dartReachable_rayExitAnchorDartMap_ltFrontierUpperSite_of_residualGtStrip
      a b hup hlt hgap hnon hresGap hstrip
  · exact hnonStrip a b hup hlt hgap hnon hresGap hstrip

/-- Non-strip residual data recover the residual-gap input. -/
theorem rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualGapReachable_of_nonStrip
    (hnonStrip :
      RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualNonStripReachable F) :
    RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualGapReachable F :=
  ⟨rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtGapReachable_of_nonStrip
      hnonStrip.1,
    rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualGtGapReachable_of_nonStrip
      hnonStrip.2⟩

/-- Lower-first residual non-strip bridge data for the local frontier-site to upper-prefix-site
pair.  The automatic lower anchor-to-bridge step is not part of this input. -/
def RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtNonStripBridgeReachable
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  ∀ a b : {x : Fin 2 → ℤ // x ∈ F},
    (hup : b.1 = a.1 + unitVec2 1) →
      (hlt : rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2) →
        (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2) →
          (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) →
            (hresGap :
              rayExitIndex F
                    (rayExitVerticalStrictLtFrontierSite a b hgap hnon).1
                    (rayExitVerticalStrictLtFrontierSite a b hgap hnon).2 + 1 <
                rayExitIndex F b.1 b.2 -
                  rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon) →
              (hnonRes : ¬ RayExitVerticalStrictLtGapStrip F
                (rayExitVerticalStrictLtFrontierSite a b hgap hnon)
                (rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon)) →
                let c := rayExitVerticalStrictLtFrontierSite a b hgap hnon
                let u := rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon
                (hupCU : u.1 = c.1 + unitVec2 1) →
                  (hltCU : rayExitIndex F c.1 c.2 < rayExitIndex F u.1 u.2) →
                    DartReachable F (rayExitVerticalStrictLtBridgeDart c u hupCU hltCU)
                      (rayExitAnchorDartMap F u)

/-- Upper-first residual non-strip bridge data for the local frontier-site to upper-prefix-site
pair.  The automatic upper bridge-to-anchor step is not part of this input. -/
def RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualGtNonStripBridgeReachable
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  ∀ a b : {x : Fin 2 → ℤ // x ∈ F},
    (hup : b.1 = a.1 + unitVec2 1) →
      (hlt : rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2) →
        (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2) →
          (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) →
            (hresGap :
              rayExitIndex F b.1 b.2 -
                    rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon + 1 <
                rayExitIndex F
                  (rayExitVerticalStrictLtFrontierSite a b hgap hnon).1
                  (rayExitVerticalStrictLtFrontierSite a b hgap hnon).2) →
              (hnonRes : ¬ RayExitVerticalStrictGtGapStrip F
                (rayExitVerticalStrictLtFrontierSite a b hgap hnon)
                (rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon)) →
                let c := rayExitVerticalStrictLtFrontierSite a b hgap hnon
                let u := rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon
                (hupCU : u.1 = c.1 + unitVec2 1) →
                  (hgtCU : rayExitIndex F u.1 u.2 < rayExitIndex F c.1 c.2) →
                    DartReachable F (rayExitAnchorDartMap F c)
                      (rayExitVerticalStrictGtBridgeDart c u hupCU hgtCU)

/-- Residual non-strip bridge data for the local frontier-site to upper-prefix-site pair. -/
def RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualNonStripBridgeReachable
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtNonStripBridgeReachable F ∧
    RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualGtNonStripBridgeReachable F

/-- Lower-first residual non-strip data with the local residual bridge leg split at the first
lower re-entry frontier dart of the residual pair. -/
def RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtNonStripFrontierReachable
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  ∀ a b : {x : Fin 2 → ℤ // x ∈ F},
    (hup : b.1 = a.1 + unitVec2 1) →
      (hlt : rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2) →
        (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2) →
          (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) →
            (hresGap :
              rayExitIndex F
                    (rayExitVerticalStrictLtFrontierSite a b hgap hnon).1
                    (rayExitVerticalStrictLtFrontierSite a b hgap hnon).2 + 1 <
                rayExitIndex F b.1 b.2 -
                  rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon) →
              (hnonRes : ¬ RayExitVerticalStrictLtGapStrip F
                (rayExitVerticalStrictLtFrontierSite a b hgap hnon)
                (rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon)) →
                let c := rayExitVerticalStrictLtFrontierSite a b hgap hnon
                let u := rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon
                (hgapCU : rayExitIndex F c.1 c.2 + 1 < rayExitIndex F u.1 u.2) →
                  DartReachable F (rayExitVerticalStrictLtFrontierDart c u hgapCU hnonRes)
                    (rayExitAnchorDartMap F u)

/-- Upper-first residual non-strip data with the local residual bridge leg split at the first
upper re-entry frontier dart of the residual pair. -/
def RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualGtNonStripFrontierReachable
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  ∀ a b : {x : Fin 2 → ℤ // x ∈ F},
    (hup : b.1 = a.1 + unitVec2 1) →
      (hlt : rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2) →
        (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2) →
          (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) →
            (hresGap :
              rayExitIndex F b.1 b.2 -
                    rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon + 1 <
                rayExitIndex F
                  (rayExitVerticalStrictLtFrontierSite a b hgap hnon).1
                  (rayExitVerticalStrictLtFrontierSite a b hgap hnon).2) →
              (hnonRes : ¬ RayExitVerticalStrictGtGapStrip F
                (rayExitVerticalStrictLtFrontierSite a b hgap hnon)
                (rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon)) →
                let c := rayExitVerticalStrictLtFrontierSite a b hgap hnon
                let u := rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon
                (hupCU : u.1 = c.1 + unitVec2 1) →
                  (hgtCU : rayExitIndex F u.1 u.2 < rayExitIndex F c.1 c.2) →
                    (hgapCU : rayExitIndex F u.1 u.2 + 1 < rayExitIndex F c.1 c.2) →
                      DartReachable F (rayExitAnchorDartMap F c)
                        (rayExitVerticalStrictGtFrontierDart c u hgapCU hnonRes) ∧
                      DartReachable F
                        (rayExitVerticalStrictGtFrontierDart c u hgapCU hnonRes)
                        (rayExitVerticalStrictGtBridgeDart c u hupCU hgtCU)

/-- Residual non-strip frontier data for the local frontier-site to upper-prefix-site pair. -/
def RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualNonStripFrontierReachable
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtNonStripFrontierReachable F ∧
    RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualGtNonStripFrontierReachable F

/-- Lower-first residual non-strip data with the post-frontier residual leg starting at the
ray-exit anchor of the residual pair's first lower re-entry site. -/
def RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtNonStripFrontierSiteReachable
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  ∀ a b : {x : Fin 2 → ℤ // x ∈ F},
    (hup : b.1 = a.1 + unitVec2 1) →
      (hlt : rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2) →
        (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2) →
          (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) →
            (hresGap :
              rayExitIndex F
                    (rayExitVerticalStrictLtFrontierSite a b hgap hnon).1
                    (rayExitVerticalStrictLtFrontierSite a b hgap hnon).2 + 1 <
                rayExitIndex F b.1 b.2 -
                  rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon) →
              (hnonRes : ¬ RayExitVerticalStrictLtGapStrip F
                (rayExitVerticalStrictLtFrontierSite a b hgap hnon)
                (rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon)) →
                let c := rayExitVerticalStrictLtFrontierSite a b hgap hnon
                let u := rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon
                (hgapCU : rayExitIndex F c.1 c.2 + 1 < rayExitIndex F u.1 u.2) →
                  DartReachable F
                    (rayExitAnchorDartMap F
                      (rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes))
                    (rayExitAnchorDartMap F u)

/-- Residual non-strip data with the lower post-frontier leg split through the residual
frontier-site anchor, while the upper-first residual frontier legs remain explicit. -/
def RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualNonStripFrontierSiteReachable
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtNonStripFrontierSiteReachable F ∧
    RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualGtNonStripFrontierReachable F

/-- Lower-first residual non-strip data with the post-frontier residual leg ending at the
residual upper-prefix site's ray-exit anchor.  The target is later identified with the original
residual upper anchor by prefix stability on the residual upper ray. -/
def RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtNonStripFrontierUpperSiteReachable
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  ∀ a b : {x : Fin 2 → ℤ // x ∈ F},
    (hup : b.1 = a.1 + unitVec2 1) →
      (hlt : rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2) →
        (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2) →
          (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) →
            (hresGap :
              rayExitIndex F
                    (rayExitVerticalStrictLtFrontierSite a b hgap hnon).1
                    (rayExitVerticalStrictLtFrontierSite a b hgap hnon).2 + 1 <
                rayExitIndex F b.1 b.2 -
                  rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon) →
              (hnonRes : ¬ RayExitVerticalStrictLtGapStrip F
                (rayExitVerticalStrictLtFrontierSite a b hgap hnon)
                (rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon)) →
                let c := rayExitVerticalStrictLtFrontierSite a b hgap hnon
                let u := rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon
                (hgapCU : rayExitIndex F c.1 c.2 + 1 < rayExitIndex F u.1 u.2) →
                  DartReachable F
                    (rayExitAnchorDartMap F
                      (rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes))
                    (rayExitAnchorDartMap F
                      (rayExitVerticalStrictLtFrontierUpperSite c u hgapCU hnonRes))

/-- Residual non-strip data with the lower post-frontier residual leg ending at the residual
upper-prefix-site anchor, while the upper-first residual frontier legs remain explicit. -/
def RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualNonStripFrontierUpperSiteReachable
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtNonStripFrontierUpperSiteReachable
      F ∧
    RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualGtNonStripFrontierReachable F

/-- Local-index increasing subcase of the lower residual upper-prefix-site leg. -/
def
RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteLtReachable
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  ∀ a b : {x : Fin 2 → ℤ // x ∈ F},
    (hup : b.1 = a.1 + unitVec2 1) →
      (hlt : rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2) →
        (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2) →
          (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) →
            (hresGap :
              rayExitIndex F
                    (rayExitVerticalStrictLtFrontierSite a b hgap hnon).1
                    (rayExitVerticalStrictLtFrontierSite a b hgap hnon).2 + 1 <
                rayExitIndex F b.1 b.2 -
                  rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon) →
              (hnonRes : ¬ RayExitVerticalStrictLtGapStrip F
                (rayExitVerticalStrictLtFrontierSite a b hgap hnon)
                (rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon)) →
                let c := rayExitVerticalStrictLtFrontierSite a b hgap hnon
                let u := rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon
                (hgapCU : rayExitIndex F c.1 c.2 + 1 < rayExitIndex F u.1 u.2) →
                  rayExitIndex F
                      (rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes).1
                      (rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes).2 <
                    rayExitIndex F
                      (rayExitVerticalStrictLtFrontierUpperSite c u hgapCU hnonRes).1
                      (rayExitVerticalStrictLtFrontierUpperSite c u hgapCU hnonRes).2 →
                    DartReachable F
                      (rayExitAnchorDartMap F
                        (rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes))
                      (rayExitAnchorDartMap F
                        (rayExitVerticalStrictLtFrontierUpperSite c u hgapCU hnonRes))

/-- Local-index decreasing subcase of the lower residual upper-prefix-site leg. -/
def
RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteGtReachable
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  ∀ a b : {x : Fin 2 → ℤ // x ∈ F},
    (hup : b.1 = a.1 + unitVec2 1) →
      (hlt : rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2) →
        (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2) →
          (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) →
            (hresGap :
              rayExitIndex F
                    (rayExitVerticalStrictLtFrontierSite a b hgap hnon).1
                    (rayExitVerticalStrictLtFrontierSite a b hgap hnon).2 + 1 <
                rayExitIndex F b.1 b.2 -
                  rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon) →
              (hnonRes : ¬ RayExitVerticalStrictLtGapStrip F
                (rayExitVerticalStrictLtFrontierSite a b hgap hnon)
                (rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon)) →
                let c := rayExitVerticalStrictLtFrontierSite a b hgap hnon
                let u := rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon
                (hgapCU : rayExitIndex F c.1 c.2 + 1 < rayExitIndex F u.1 u.2) →
                  rayExitIndex F
                      (rayExitVerticalStrictLtFrontierUpperSite c u hgapCU hnonRes).1
                      (rayExitVerticalStrictLtFrontierUpperSite c u hgapCU hnonRes).2 <
                    rayExitIndex F
                      (rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes).1
                      (rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes).2 →
                    DartReachable F
                      (rayExitAnchorDartMap F
                        (rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes))
                      (rayExitAnchorDartMap F
                        (rayExitVerticalStrictLtFrontierUpperSite c u hgapCU hnonRes))

/-- Ordered residual upper-prefix-site data split by local residual ray-exit index order. -/
def RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteOrderedReachable
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteLtReachable
      F ∧
    RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteGtReachable F

/-- Residual-index form of the increasing subcase of the lower residual upper-prefix-site leg. -/
def
RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteResidualLtReachable
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  ∀ a b : {x : Fin 2 → ℤ // x ∈ F},
    (hup : b.1 = a.1 + unitVec2 1) →
      (hlt : rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2) →
        (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2) →
          (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) →
            (hresGap :
              rayExitIndex F
                    (rayExitVerticalStrictLtFrontierSite a b hgap hnon).1
                    (rayExitVerticalStrictLtFrontierSite a b hgap hnon).2 + 1 <
                rayExitIndex F b.1 b.2 -
                  rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon) →
              (hnonRes : ¬ RayExitVerticalStrictLtGapStrip F
                (rayExitVerticalStrictLtFrontierSite a b hgap hnon)
                (rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon)) →
                let c := rayExitVerticalStrictLtFrontierSite a b hgap hnon
                let u := rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon
                (hgapCU : rayExitIndex F c.1 c.2 + 1 < rayExitIndex F u.1 u.2) →
                  rayExitIndex F
                      (rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes).1
                      (rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes).2 <
                    rayExitIndex F u.1 u.2 -
                      rayExitVerticalStrictLtFirstFrontierIndex c u hgapCU hnonRes →
                    DartReachable F
                      (rayExitAnchorDartMap F
                        (rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes))
                      (rayExitAnchorDartMap F
                        (rayExitVerticalStrictLtFrontierUpperSite c u hgapCU hnonRes))

/-- Residual-index form of the decreasing subcase of the lower residual upper-prefix-site leg. -/
def
RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteResidualGtReachable
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  ∀ a b : {x : Fin 2 → ℤ // x ∈ F},
    (hup : b.1 = a.1 + unitVec2 1) →
      (hlt : rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2) →
        (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2) →
          (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) →
            (hresGap :
              rayExitIndex F
                    (rayExitVerticalStrictLtFrontierSite a b hgap hnon).1
                    (rayExitVerticalStrictLtFrontierSite a b hgap hnon).2 + 1 <
                rayExitIndex F b.1 b.2 -
                  rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon) →
              (hnonRes : ¬ RayExitVerticalStrictLtGapStrip F
                (rayExitVerticalStrictLtFrontierSite a b hgap hnon)
                (rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon)) →
                let c := rayExitVerticalStrictLtFrontierSite a b hgap hnon
                let u := rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon
                (hgapCU : rayExitIndex F c.1 c.2 + 1 < rayExitIndex F u.1 u.2) →
                  rayExitIndex F u.1 u.2 -
                      rayExitVerticalStrictLtFirstFrontierIndex c u hgapCU hnonRes <
                    rayExitIndex F
                      (rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes).1
                      (rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes).2 →
                    DartReachable F
                      (rayExitAnchorDartMap F
                        (rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes))
                      (rayExitAnchorDartMap F
                        (rayExitVerticalStrictLtFrontierUpperSite c u hgapCU hnonRes))

/-- Residual-index ordered residual upper-prefix-site data. -/
def RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteResidualOrderedReachable
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteResidualLtReachable
      F ∧
    RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteResidualGtReachable F

/-- The strict subcase of the lower residual upper-prefix-site leg: if the residual
frontier-site and residual upper-prefix site have unequal ray-exit indices, their anchors must be
reachable.  The equal-index subcase is closed by shared-vertex geometry. -/
def
RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteStrictReachable
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  ∀ a b : {x : Fin 2 → ℤ // x ∈ F},
    (hup : b.1 = a.1 + unitVec2 1) →
      (hlt : rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2) →
        (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2) →
          (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) →
            (hresGap :
              rayExitIndex F
                    (rayExitVerticalStrictLtFrontierSite a b hgap hnon).1
                    (rayExitVerticalStrictLtFrontierSite a b hgap hnon).2 + 1 <
                rayExitIndex F b.1 b.2 -
                  rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon) →
              (hnonRes : ¬ RayExitVerticalStrictLtGapStrip F
                (rayExitVerticalStrictLtFrontierSite a b hgap hnon)
                (rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon)) →
                let c := rayExitVerticalStrictLtFrontierSite a b hgap hnon
                let u := rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon
                (hgapCU : rayExitIndex F c.1 c.2 + 1 < rayExitIndex F u.1 u.2) →
                  rayExitIndex F
                      (rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes).1
                      (rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes).2 ≠
                    rayExitIndex F
                      (rayExitVerticalStrictLtFrontierUpperSite c u hgapCU hnonRes).1
                      (rayExitVerticalStrictLtFrontierUpperSite c u hgapCU hnonRes).2 →
                    DartReachable F
                      (rayExitAnchorDartMap F
                        (rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes))
                      (rayExitAnchorDartMap F
                        (rayExitVerticalStrictLtFrontierUpperSite c u hgapCU hnonRes))

/-- Residual non-strip data with the lower residual upper-prefix-site leg reduced to its strict
unequal-index subcase, while the upper-first residual frontier legs remain explicit. -/
def RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualUpperSiteStrictReachable
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteStrictReachable
      F ∧
    RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualGtNonStripFrontierReachable F

/-- Ordered residual upper-prefix-site data together with the explicit upper-first residual
frontier legs. -/
def RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualUpperSiteOrderedReachable
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteOrderedReachable
      F ∧
    RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualGtNonStripFrontierReachable F

/-- Residual-index ordered residual upper-prefix-site data together with the explicit upper-first
residual frontier legs. -/
def RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualUpperSiteResidualOrderedReachable
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteResidualOrderedReachable
      F ∧
    RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualGtNonStripFrontierReachable F

/-- Gap-reduced residual-index form of the increasing subcase of the lower residual
upper-prefix-site leg.  The adjacent residual-index case is automatic. -/
def
RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteResidualLtGapReachable
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  ∀ a b : {x : Fin 2 → ℤ // x ∈ F},
    (hup : b.1 = a.1 + unitVec2 1) →
      (hlt : rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2) →
        (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2) →
          (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) →
            (hresGap :
              rayExitIndex F
                    (rayExitVerticalStrictLtFrontierSite a b hgap hnon).1
                    (rayExitVerticalStrictLtFrontierSite a b hgap hnon).2 + 1 <
                rayExitIndex F b.1 b.2 -
                  rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon) →
              (hnonRes : ¬ RayExitVerticalStrictLtGapStrip F
                (rayExitVerticalStrictLtFrontierSite a b hgap hnon)
                (rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon)) →
                let c := rayExitVerticalStrictLtFrontierSite a b hgap hnon
                let u := rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon
                (hgapCU : rayExitIndex F c.1 c.2 + 1 < rayExitIndex F u.1 u.2) →
                  let p := rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes
                  let q :=
                    rayExitVerticalStrictLtFrontierUpperSite c u hgapCU hnonRes
                  rayExitIndex F p.1 p.2 + 1 <
                    rayExitIndex F u.1 u.2 -
                      rayExitVerticalStrictLtFirstFrontierIndex c u hgapCU hnonRes →
                    DartReachable F (rayExitAnchorDartMap F p)
                      (rayExitAnchorDartMap F q)

/-- Gap-reduced residual-index form of the decreasing subcase of the lower residual
upper-prefix-site leg.  The adjacent residual-index case is automatic. -/
def
RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteResidualGtGapReachable
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  ∀ a b : {x : Fin 2 → ℤ // x ∈ F},
    (hup : b.1 = a.1 + unitVec2 1) →
      (hlt : rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2) →
        (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2) →
          (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) →
            (hresGap :
              rayExitIndex F
                    (rayExitVerticalStrictLtFrontierSite a b hgap hnon).1
                    (rayExitVerticalStrictLtFrontierSite a b hgap hnon).2 + 1 <
                rayExitIndex F b.1 b.2 -
                  rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon) →
              (hnonRes : ¬ RayExitVerticalStrictLtGapStrip F
                (rayExitVerticalStrictLtFrontierSite a b hgap hnon)
                (rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon)) →
                let c := rayExitVerticalStrictLtFrontierSite a b hgap hnon
                let u := rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon
                (hgapCU : rayExitIndex F c.1 c.2 + 1 < rayExitIndex F u.1 u.2) →
                  let p := rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes
                  let q :=
                    rayExitVerticalStrictLtFrontierUpperSite c u hgapCU hnonRes
                  rayExitIndex F u.1 u.2 -
                        rayExitVerticalStrictLtFirstFrontierIndex c u hgapCU hnonRes + 1 <
                    rayExitIndex F p.1 p.2 →
                    DartReachable F (rayExitAnchorDartMap F p)
                      (rayExitAnchorDartMap F q)

/-- Gap-reduced residual-index ordered residual upper-prefix-site data. -/
def
RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteResidualGapReachable
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteResidualLtGapReachable
      F ∧
    RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteResidualGtGapReachable
      F

/-- Gap-reduced residual-index ordered residual upper-prefix-site data together with the explicit
upper-first residual frontier legs. -/
def RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualUpperSiteResidualGapReachable
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteResidualGapReachable
      F ∧
    RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualGtNonStripFrontierReachable F

/-- Non-strip form of the increasing subcase of the residual upper-prefix-site residual leg.
Straight local residual strips are automatic by the existing finite strip chain. -/
def
RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteResidualLtNonStripReachable
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  ∀ a b : {x : Fin 2 → ℤ // x ∈ F},
    (hup : b.1 = a.1 + unitVec2 1) →
      (hlt : rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2) →
        (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2) →
          (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) →
            (hresGap :
              rayExitIndex F
                    (rayExitVerticalStrictLtFrontierSite a b hgap hnon).1
                    (rayExitVerticalStrictLtFrontierSite a b hgap hnon).2 + 1 <
                rayExitIndex F b.1 b.2 -
                  rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon) →
              (hnonRes : ¬ RayExitVerticalStrictLtGapStrip F
                (rayExitVerticalStrictLtFrontierSite a b hgap hnon)
                (rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon)) →
                let c := rayExitVerticalStrictLtFrontierSite a b hgap hnon
                let u := rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon
                (hgapCU : rayExitIndex F c.1 c.2 + 1 < rayExitIndex F u.1 u.2) →
                  let p := rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes
                  let q :=
                    rayExitVerticalStrictLtFrontierUpperSite c u hgapCU hnonRes
                  rayExitIndex F p.1 p.2 + 1 <
                    rayExitIndex F u.1 u.2 -
                      rayExitVerticalStrictLtFirstFrontierIndex c u hgapCU hnonRes →
                    ¬ RayExitVerticalStrictLtGapStrip F p q →
                      DartReachable F (rayExitAnchorDartMap F p)
                        (rayExitAnchorDartMap F q)

/-- Non-strip form of the decreasing subcase of the residual upper-prefix-site residual leg.
Straight local residual strips are automatic by the existing finite strip chain. -/
def
RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteResidualGtNonStripReachable
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  ∀ a b : {x : Fin 2 → ℤ // x ∈ F},
    (hup : b.1 = a.1 + unitVec2 1) →
      (hlt : rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2) →
        (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2) →
          (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) →
            (hresGap :
              rayExitIndex F
                    (rayExitVerticalStrictLtFrontierSite a b hgap hnon).1
                    (rayExitVerticalStrictLtFrontierSite a b hgap hnon).2 + 1 <
                rayExitIndex F b.1 b.2 -
                  rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon) →
              (hnonRes : ¬ RayExitVerticalStrictLtGapStrip F
                (rayExitVerticalStrictLtFrontierSite a b hgap hnon)
                (rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon)) →
                let c := rayExitVerticalStrictLtFrontierSite a b hgap hnon
                let u := rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon
                (hgapCU : rayExitIndex F c.1 c.2 + 1 < rayExitIndex F u.1 u.2) →
                  let p := rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes
                  let q :=
                    rayExitVerticalStrictLtFrontierUpperSite c u hgapCU hnonRes
                  rayExitIndex F u.1 u.2 -
                        rayExitVerticalStrictLtFirstFrontierIndex c u hgapCU hnonRes + 1 <
                    rayExitIndex F p.1 p.2 →
                    ¬ RayExitVerticalStrictGtGapStrip F p q →
                      DartReachable F (rayExitAnchorDartMap F p)
                        (rayExitAnchorDartMap F q)

/-- Non-strip residual-index residual upper-prefix-site data. -/
def
RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteResidualNonStripReachable
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteResidualLtNonStripReachable
      F ∧
    RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteResidualGtNonStripReachable
      F

/-- Non-strip residual-index residual upper-prefix-site data together with the explicit upper-first
residual frontier legs. -/
def
RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualUpperSiteResidualNonStripReachable
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteResidualNonStripReachable
      F ∧
    RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualGtNonStripFrontierReachable F

/-- Non-strip data recover the increasing residual-gap input because straight local residual
strips are automatic. -/
theorem
    rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteResidualLtGap_of_nonStrip
    (hnonStrip :
      RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteResidualLtNonStripReachable
        F) :
    RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteResidualLtGapReachable
      F := by
  intro a b hup hlt hgap hnon hresGap hnonRes
  let c := rayExitVerticalStrictLtFrontierSite a b hgap hnon
  let u := rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon
  change (hgapCU : rayExitIndex F c.1 c.2 + 1 < rayExitIndex F u.1 u.2) →
    rayExitIndex F (rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes).1
        (rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes).2 + 1 <
      rayExitIndex F u.1 u.2 -
        rayExitVerticalStrictLtFirstFrontierIndex c u hgapCU hnonRes →
      DartReachable F
        (rayExitAnchorDartMap F (rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes))
        (rayExitAnchorDartMap F
          (rayExitVerticalStrictLtFrontierUpperSite c u hgapCU hnonRes))
  intro hgapCU hidx
  let p := rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes
  let q := rayExitVerticalStrictLtFrontierUpperSite c u hgapCU hnonRes
  have hupCU : u.1 = c.1 + unitVec2 1 := by
    dsimp [c, u]
    exact rayExitVerticalStrictLtFrontierUpperSite_eq_frontierSite_add_e1
      a b hup hgap hnon
  have hidxU :
      rayExitIndex F u.1 u.2 =
        rayExitIndex F b.1 b.2 -
          rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon := by
    simpa [u] using rayExitIndex_ltFrontierUpperSite_eq a b hgap hnon
  have hltCU : rayExitIndex F c.1 c.2 < rayExitIndex F u.1 u.2 := by
    rw [hidxU]
    dsimp [c] at hresGap ⊢
    omega
  by_cases hstrip : RayExitVerticalStrictLtGapStrip F p q
  · simpa [p, q] using
      dartReachable_rayExitAnchorDartMap_ltFrontierUpperSite_of_residualLtStrip
        c u hupCU hltCU hgapCU hnonRes hidx hstrip
  · exact hnonStrip a b hup hlt hgap hnon hresGap hnonRes hgapCU hidx hstrip

/-- Non-strip data recover the decreasing residual-gap input because straight local residual
strips are automatic. -/
theorem
    rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteResidualGtGap_of_nonStrip
    (hnonStrip :
      RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteResidualGtNonStripReachable
        F) :
    RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteResidualGtGapReachable
      F := by
  intro a b hup hlt hgap hnon hresGap hnonRes
  let c := rayExitVerticalStrictLtFrontierSite a b hgap hnon
  let u := rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon
  change (hgapCU : rayExitIndex F c.1 c.2 + 1 < rayExitIndex F u.1 u.2) →
    rayExitIndex F u.1 u.2 -
        rayExitVerticalStrictLtFirstFrontierIndex c u hgapCU hnonRes + 1 <
      rayExitIndex F (rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes).1
        (rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes).2 →
      DartReachable F
        (rayExitAnchorDartMap F (rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes))
        (rayExitAnchorDartMap F
          (rayExitVerticalStrictLtFrontierUpperSite c u hgapCU hnonRes))
  intro hgapCU hidx
  let p := rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes
  let q := rayExitVerticalStrictLtFrontierUpperSite c u hgapCU hnonRes
  have hupCU : u.1 = c.1 + unitVec2 1 := by
    dsimp [c, u]
    exact rayExitVerticalStrictLtFrontierUpperSite_eq_frontierSite_add_e1
      a b hup hgap hnon
  have hidxU :
      rayExitIndex F u.1 u.2 =
        rayExitIndex F b.1 b.2 -
          rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon := by
    simpa [u] using rayExitIndex_ltFrontierUpperSite_eq a b hgap hnon
  have hltCU : rayExitIndex F c.1 c.2 < rayExitIndex F u.1 u.2 := by
    rw [hidxU]
    dsimp [c] at hresGap ⊢
    omega
  by_cases hstrip : RayExitVerticalStrictGtGapStrip F p q
  · simpa [p, q] using
      dartReachable_rayExitAnchorDartMap_ltFrontierUpperSite_of_residualGtStrip
        c u hupCU hltCU hgapCU hnonRes hidx hstrip
  · exact hnonStrip a b hup hlt hgap hnon hresGap hnonRes hgapCU hidx hstrip

/-- Non-strip data recover the residual-gap input. -/
theorem
    rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteResidualGap_of_nonStrip
    (hnonStrip :
      RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteResidualNonStripReachable
        F) :
    RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteResidualGapReachable
      F :=
  ⟨rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteResidualLtGap_of_nonStrip
      hnonStrip.1,
    rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteResidualGtGap_of_nonStrip
      hnonStrip.2⟩

/-- Non-strip data recover the combined residual-gap input. -/
theorem
    rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualUpperSiteResidualGap_of_nonStrip
    (hnonStrip :
      RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualUpperSiteResidualNonStripReachable
        F) :
    RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualUpperSiteResidualGapReachable
      F :=
  ⟨rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteResidualGap_of_nonStrip
      hnonStrip.1,
    hnonStrip.2⟩

/-- Gap-reduced residual-index data recover the increasing residual upper-prefix-site input because
the adjacent local residual case is automatic. -/
theorem
    rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteResidualLtReachable_of_gap
    (hgapReach :
      RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteResidualLtGapReachable
        F) :
    RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteResidualLtReachable
      F := by
  intro a b hup hlt hgap hnon hresGap hnonRes
  let c := rayExitVerticalStrictLtFrontierSite a b hgap hnon
  let u := rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon
  change (hgapCU : rayExitIndex F c.1 c.2 + 1 < rayExitIndex F u.1 u.2) →
    rayExitIndex F (rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes).1
        (rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes).2 <
      rayExitIndex F u.1 u.2 -
        rayExitVerticalStrictLtFirstFrontierIndex c u hgapCU hnonRes →
      DartReachable F
        (rayExitAnchorDartMap F (rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes))
        (rayExitAnchorDartMap F
          (rayExitVerticalStrictLtFrontierUpperSite c u hgapCU hnonRes))
  intro hgapCU hidx
  let p := rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes
  let q := rayExitVerticalStrictLtFrontierUpperSite c u hgapCU hnonRes
  have hupCU : u.1 = c.1 + unitVec2 1 := by
    dsimp [c, u]
    exact rayExitVerticalStrictLtFrontierUpperSite_eq_frontierSite_add_e1
      a b hup hgap hnon
  have hidxU :
      rayExitIndex F u.1 u.2 =
        rayExitIndex F b.1 b.2 -
          rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon := by
    simpa [u] using rayExitIndex_ltFrontierUpperSite_eq a b hgap hnon
  have hltCU : rayExitIndex F c.1 c.2 < rayExitIndex F u.1 u.2 := by
    rw [hidxU]
    dsimp [c] at hresGap ⊢
    omega
  by_cases hsucc :
      rayExitIndex F u.1 u.2 -
          rayExitVerticalStrictLtFirstFrontierIndex c u hgapCU hnonRes =
        rayExitIndex F p.1 p.2 + 1
  · simpa [p, q] using
      dartReachable_rayExitAnchorDartMap_ltFrontierUpperSite_of_residualLtSucc
        c u hupCU hltCU hgapCU hnonRes hsucc
  · exact hgapReach a b hup hlt hgap hnon hresGap hnonRes hgapCU (by
      dsimp [p] at hidx hsucc ⊢
      by_contra hnot
      have hle :
          rayExitIndex F u.1 u.2 -
              rayExitVerticalStrictLtFirstFrontierIndex c u hgapCU hnonRes ≤
            rayExitIndex F (rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes).1
                (rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes).2 + 1 :=
        Nat.le_of_not_gt hnot
      have hge :
          rayExitIndex F (rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes).1
                (rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes).2 + 1 ≤
            rayExitIndex F u.1 u.2 -
              rayExitVerticalStrictLtFirstFrontierIndex c u hgapCU hnonRes :=
        Nat.succ_le_of_lt hidx
      exact hsucc (le_antisymm hle hge))

/-- Gap-reduced residual-index data recover the decreasing residual upper-prefix-site input because
the adjacent local residual case is automatic. -/
theorem
    rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteResidualGtReachable_of_gap
    (hgapReach :
      RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteResidualGtGapReachable
        F) :
    RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteResidualGtReachable
      F := by
  intro a b hup hlt hgap hnon hresGap hnonRes
  let c := rayExitVerticalStrictLtFrontierSite a b hgap hnon
  let u := rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon
  change (hgapCU : rayExitIndex F c.1 c.2 + 1 < rayExitIndex F u.1 u.2) →
    rayExitIndex F u.1 u.2 -
        rayExitVerticalStrictLtFirstFrontierIndex c u hgapCU hnonRes <
      rayExitIndex F (rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes).1
        (rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes).2 →
      DartReachable F
        (rayExitAnchorDartMap F (rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes))
        (rayExitAnchorDartMap F
          (rayExitVerticalStrictLtFrontierUpperSite c u hgapCU hnonRes))
  intro hgapCU hidx
  let p := rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes
  let q := rayExitVerticalStrictLtFrontierUpperSite c u hgapCU hnonRes
  have hupCU : u.1 = c.1 + unitVec2 1 := by
    dsimp [c, u]
    exact rayExitVerticalStrictLtFrontierUpperSite_eq_frontierSite_add_e1
      a b hup hgap hnon
  have hidxU :
      rayExitIndex F u.1 u.2 =
        rayExitIndex F b.1 b.2 -
          rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon := by
    simpa [u] using rayExitIndex_ltFrontierUpperSite_eq a b hgap hnon
  have hltCU : rayExitIndex F c.1 c.2 < rayExitIndex F u.1 u.2 := by
    rw [hidxU]
    dsimp [c] at hresGap ⊢
    omega
  by_cases hsucc :
      rayExitIndex F p.1 p.2 =
        rayExitIndex F u.1 u.2 -
            rayExitVerticalStrictLtFirstFrontierIndex c u hgapCU hnonRes + 1
  · simpa [p, q] using
      dartReachable_rayExitAnchorDartMap_ltFrontierUpperSite_of_residualGtSucc
        c u hupCU hltCU hgapCU hnonRes hsucc
  · exact hgapReach a b hup hlt hgap hnon hresGap hnonRes hgapCU (by
      dsimp [p] at hidx hsucc ⊢
      by_contra hnot
      have hle :
          rayExitIndex F (rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes).1
              (rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes).2 ≤
            rayExitIndex F u.1 u.2 -
                rayExitVerticalStrictLtFirstFrontierIndex c u hgapCU hnonRes + 1 :=
        Nat.le_of_not_gt hnot
      have hge :
          rayExitIndex F u.1 u.2 -
                rayExitVerticalStrictLtFirstFrontierIndex c u hgapCU hnonRes + 1 ≤
            rayExitIndex F (rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes).1
              (rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes).2 :=
        Nat.succ_le_of_lt hidx
      exact hsucc (le_antisymm hle hge))

/-- Gap-reduced residual-index data recover the residual-index ordered residual upper-prefix-site
input. -/
theorem
    rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteResidualOrdered_of_gap
    (hgapReach :
      RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteResidualGapReachable
        F) :
    RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteResidualOrderedReachable
      F :=
  ⟨rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteResidualLtReachable_of_gap
      hgapReach.1,
    rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteResidualGtReachable_of_gap
      hgapReach.2⟩

/-- Gap-reduced residual-index data recover the combined residual-index ordered residual
upper-prefix-site input. -/
theorem
    rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualUpperSiteResidualOrdered_of_gap
    (hgapReach :
      RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualUpperSiteResidualGapReachable
        F) :
    RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualUpperSiteResidualOrderedReachable
      F :=
  ⟨rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteResidualOrdered_of_gap
      hgapReach.1,
    hgapReach.2⟩

/-- Lower-first residual frontier data recover the lower-first residual bridge input. -/
theorem
    rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtBridgeReachable_of_frontier
    (hfrontier :
      RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtNonStripFrontierReachable F) :
    RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtNonStripBridgeReachable F := by
  intro a b hup hlt hgap hnon hresGap hnonRes
  let c := rayExitVerticalStrictLtFrontierSite a b hgap hnon
  let u := rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon
  change (hupCU : u.1 = c.1 + unitVec2 1) →
    (hltCU : rayExitIndex F c.1 c.2 < rayExitIndex F u.1 u.2) →
      DartReachable F (rayExitVerticalStrictLtBridgeDart c u hupCU hltCU)
        (rayExitAnchorDartMap F u)
  intro hupCU hltCU
  have hidxU :
      rayExitIndex F u.1 u.2 =
        rayExitIndex F b.1 b.2 -
          rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon := by
    simpa [u] using rayExitIndex_ltFrontierUpperSite_eq a b hgap hnon
  have hgapCU : rayExitIndex F c.1 c.2 + 1 < rayExitIndex F u.1 u.2 := by
    rw [hidxU]
    dsimp [c] at hresGap ⊢
    omega
  exact
    (dartReachable_of_turnChain
      (nextDartTurnChain_ltBridgeDart_ltFrontierDart c u hupCU hltCU hgapCU
        hnonRes)).trans
      (hfrontier a b hup hlt hgap hnon hresGap hnonRes hgapCU)

/-- Upper-first residual frontier data recover the upper-first residual bridge input. -/
theorem
    rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualGtBridgeReachable_of_frontier
    (hfrontier :
      RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualGtNonStripFrontierReachable F) :
    RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualGtNonStripBridgeReachable F := by
  intro a b hup hlt hgap hnon hresGap hnonRes
  let c := rayExitVerticalStrictLtFrontierSite a b hgap hnon
  let u := rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon
  change (hupCU : u.1 = c.1 + unitVec2 1) →
    (hgtCU : rayExitIndex F u.1 u.2 < rayExitIndex F c.1 c.2) →
      DartReachable F (rayExitAnchorDartMap F c)
        (rayExitVerticalStrictGtBridgeDart c u hupCU hgtCU)
  intro hupCU hgtCU
  have hidxU :
      rayExitIndex F u.1 u.2 =
        rayExitIndex F b.1 b.2 -
          rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon := by
    simpa [u] using rayExitIndex_ltFrontierUpperSite_eq a b hgap hnon
  have hgapCU : rayExitIndex F u.1 u.2 + 1 < rayExitIndex F c.1 c.2 := by
    rw [hidxU]
    dsimp [c] at hresGap ⊢
    omega
  exact
    (hfrontier a b hup hlt hgap hnon hresGap hnonRes hupCU hgtCU hgapCU).1.trans
      (hfrontier a b hup hlt hgap hnon hresGap hnonRes hupCU hgtCU hgapCU).2

/-- Residual frontier data recover the residual bridge input. -/
theorem rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualBridgeReachable_of_frontier
    (hfrontier :
      RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualNonStripFrontierReachable F) :
    RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualNonStripBridgeReachable F :=
  ⟨rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtBridgeReachable_of_frontier
      hfrontier.1,
    rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualGtBridgeReachable_of_frontier
      hfrontier.2⟩

/-- Lower-first residual bridge data recover the lower-first residual non-strip input because the
lower frontier site's ray-exit anchor reaches the lower bridge dart automatically. -/
theorem rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtNonStripReachable_of_bridge
    (hbridge :
      RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtNonStripBridgeReachable F) :
    RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtNonStripReachable F := by
  intro a b hup hlt hgap hnon hresGap hnonRes
  let c := rayExitVerticalStrictLtFrontierSite a b hgap hnon
  let u := rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon
  have hupCU : u.1 = c.1 + unitVec2 1 := by
    dsimp [c, u]
    exact rayExitVerticalStrictLtFrontierUpperSite_eq_frontierSite_add_e1
      a b hup hgap hnon
  have hidxU :
      rayExitIndex F u.1 u.2 =
        rayExitIndex F b.1 b.2 -
          rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon := by
    simpa [u] using rayExitIndex_ltFrontierUpperSite_eq a b hgap hnon
  have hltCU : rayExitIndex F c.1 c.2 < rayExitIndex F u.1 u.2 := by
    rw [hidxU]
    dsimp [c] at hresGap ⊢
    omega
  exact (dartReachable_rayExitAnchorDartMap_ltBridgeDart c u hupCU hltCU).trans
    (hbridge a b hup hlt hgap hnon hresGap hnonRes hupCU hltCU)

/-- Upper-first residual bridge data recover the upper-first residual non-strip input because the
upper-prefix site's ray-exit anchor reaches the upper bridge dart automatically. -/
theorem rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualGtNonStripReachable_of_bridge
    (hbridge :
      RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualGtNonStripBridgeReachable F) :
    RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualGtNonStripReachable F := by
  intro a b hup hlt hgap hnon hresGap hnonRes
  let c := rayExitVerticalStrictLtFrontierSite a b hgap hnon
  let u := rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon
  have hupCU : u.1 = c.1 + unitVec2 1 := by
    dsimp [c, u]
    exact rayExitVerticalStrictLtFrontierUpperSite_eq_frontierSite_add_e1
      a b hup hgap hnon
  have hidxU :
      rayExitIndex F u.1 u.2 =
        rayExitIndex F b.1 b.2 -
          rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon := by
    simpa [u] using rayExitIndex_ltFrontierUpperSite_eq a b hgap hnon
  have hgtCU : rayExitIndex F u.1 u.2 < rayExitIndex F c.1 c.2 := by
    rw [hidxU]
    dsimp [c] at hresGap ⊢
    omega
  exact (hbridge a b hup hlt hgap hnon hresGap hnonRes hupCU hgtCU).trans
    (dartReachable_rayExitAnchorDartMap_gtBridgeDart c u hupCU hgtCU).symm

/-- Residual bridge data recover the residual non-strip input. -/
theorem rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualNonStripReachable_of_bridge
    (hbridge :
      RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualNonStripBridgeReachable F) :
    RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualNonStripReachable F :=
  ⟨rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtNonStripReachable_of_bridge
      hbridge.1,
    rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualGtNonStripReachable_of_bridge
      hbridge.2⟩

/-- Residual-index ordered lower frontier-site-to-upper-prefix data recover the local-index
ordered form by prefix-index stability on the upper ray. -/
theorem rayExitVerticalStrictLtFrontierUpperSiteAnchorOrderedReachable_of_residualOrdered
    (hresidual :
      RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualOrderedReachable F) :
    RayExitVerticalStrictLtFrontierUpperSiteAnchorOrderedReachable F := by
  constructor
  · intro a b hup hlt hgap hnon hidx
    rw [rayExitIndex_ltFrontierUpperSite_eq a b hgap hnon] at hidx
    exact hresidual.1 a b hup hlt hgap hnon hidx
  · intro a b hup hlt hgap hnon hidx
    rw [rayExitIndex_ltFrontierUpperSite_eq a b hgap hnon] at hidx
    exact hresidual.2 a b hup hlt hgap hnon hidx

/-- Ordered lower frontier-site-to-upper-prefix data recover the strict reachable form by local
ray-exit index trichotomy. -/
theorem rayExitVerticalStrictLtFrontierUpperSiteAnchorStrictReachable_of_orderedReachable
    (hordered : RayExitVerticalStrictLtFrontierUpperSiteAnchorOrderedReachable F) :
    RayExitVerticalStrictLtFrontierUpperSiteAnchorStrictReachable F := by
  intro a b hup hlt hgap hnon hidx
  rcases lt_or_gt_of_ne hidx with hltLocal | hgtLocal
  · exact hordered.1 a b hup hlt hgap hnon hltLocal
  · exact hordered.2 a b hup hlt hgap hnon hgtLocal

/-- Strict lower frontier-site-to-upper-prefix data recover the reachable form: if the two
intermediate sites have equal ray-exit indices, their anchor darts share a dual vertex. -/
theorem rayExitVerticalStrictLtFrontierUpperSiteAnchorReachable_of_strictReachable
    (hstrict : RayExitVerticalStrictLtFrontierUpperSiteAnchorStrictReachable F) :
    RayExitVerticalStrictLtFrontierUpperSiteAnchorReachable F := by
  intro a b hup hlt hgap hnon
  let c := rayExitVerticalStrictLtFrontierSite a b hgap hnon
  let u := rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon
  by_cases hidx : rayExitIndex F c.1 c.2 = rayExitIndex F u.1 u.2
  · have hupCU : u.1 = c.1 + unitVec2 1 := by
      dsimp [c, u]
      exact rayExitVerticalStrictLtFrontierUpperSite_eq_frontierSite_add_e1
        a b hup hgap hnon
    obtain ⟨_, hvc, hvu⟩ :=
      rayExitAnchorDartMap_add_e1_shared_of_index_eq c u hupCU hidx.symm
    exact dartReachable_of_shared hvc hvu
  · exact hstrict a b hup hlt hgap hnon hidx

/-- The existing ray-exit anchoring input sends the lower frontier dart to the ray-exit anchor of
the packaged first lower re-entry site. -/
theorem dartReachable_rayExitVerticalStrictLtFrontierDart_frontierSiteAnchor
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (a b : {x : Fin 2 → ℤ // x ∈ F})
    (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2)
    (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) :
    DartReachable F (rayExitVerticalStrictLtFrontierDart a b hgap hnon)
      (rayExitAnchorDartMap F (rayExitVerticalStrictLtFrontierSite a b hgap hnon)) := by
  let d := rayExitVerticalStrictLtFrontierDart a b hgap hnon
  have hsite :
      (⟨d.left, d.left_mem⟩ : {x : Fin 2 → ℤ // x ∈ F}) =
        rayExitVerticalStrictLtFrontierSite a b hgap hnon := by
    apply Subtype.ext
    dsimp [d]
    exact rayExitVerticalStrictLtFrontierDart_left_frontierSite a b hgap hnon
  simpa [d, hsite] using hanchor d

/-- Residual lower post-frontier site-anchor data recover the residual lower frontier input once
the existing anchoring input supplies the residual frontier-dart-to-site-anchor leg. -/
theorem
    rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtFrontierReachable_of_site
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hsite :
      RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtNonStripFrontierSiteReachable F) :
    RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtNonStripFrontierReachable F := by
  intro a b hup hlt hgap hnon hresGap hnonRes
  let c := rayExitVerticalStrictLtFrontierSite a b hgap hnon
  let u := rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon
  change (hgapCU : rayExitIndex F c.1 c.2 + 1 < rayExitIndex F u.1 u.2) →
    DartReachable F (rayExitVerticalStrictLtFrontierDart c u hgapCU hnonRes)
      (rayExitAnchorDartMap F u)
  intro hgapCU
  exact
    (dartReachable_rayExitVerticalStrictLtFrontierDart_frontierSiteAnchor hanchor c u
      hgapCU hnonRes).trans
      (hsite a b hup hlt hgap hnon hresGap hnonRes hgapCU)

/-- Residual site-anchor data recover the residual frontier input once the existing anchoring
input supplies the lower residual frontier-dart-to-site-anchor leg. -/
theorem rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualFrontierReachable_of_site
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hsite :
      RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualNonStripFrontierSiteReachable F) :
    RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualNonStripFrontierReachable F :=
  ⟨rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtFrontierReachable_of_site
      hanchor hsite.1,
    hsite.2⟩

/-- Residual upper-prefix-site data recover the lower residual site-anchor input by prefix
stability on the residual upper ray. -/
theorem
    rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtFrontierSiteReachable_of_upperSite
    (hupper :
      RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtNonStripFrontierUpperSiteReachable
        F) :
    RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtNonStripFrontierSiteReachable F := by
  intro a b hup hlt hgap hnon hresGap hnonRes
  let c := rayExitVerticalStrictLtFrontierSite a b hgap hnon
  let u := rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon
  change (hgapCU : rayExitIndex F c.1 c.2 + 1 < rayExitIndex F u.1 u.2) →
    DartReachable F
      (rayExitAnchorDartMap F (rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes))
      (rayExitAnchorDartMap F u)
  intro hgapCU
  have hleg := hupper a b hup hlt hgap hnon hresGap hnonRes hgapCU
  rw [rayExitAnchorDartMap_ltFrontierUpperSite_eq c u hgapCU hnonRes] at hleg
  exact hleg

/-- Residual upper-prefix-site data recover the residual site-anchor input. -/
theorem rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualSiteReachable_of_upperSite
    (hupper :
      RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualNonStripFrontierUpperSiteReachable
        F) :
    RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualNonStripFrontierSiteReachable F :=
  ⟨rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtFrontierSiteReachable_of_upperSite
      hupper.1,
    hupper.2⟩

/-- Residual-index ordered residual upper-prefix-site data recover the local-index ordered form by
prefix-index stability on the local residual upper ray. -/
theorem
    rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteOrdered_of_residual
    (hresidual :
      RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteResidualOrderedReachable
        F) :
    RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteOrderedReachable
      F := by
  constructor
  · intro a b hup hlt hgap hnon hresGap hnonRes
    let c := rayExitVerticalStrictLtFrontierSite a b hgap hnon
    let u := rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon
    change (hgapCU : rayExitIndex F c.1 c.2 + 1 < rayExitIndex F u.1 u.2) →
      rayExitIndex F (rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes).1
          (rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes).2 <
        rayExitIndex F (rayExitVerticalStrictLtFrontierUpperSite c u hgapCU hnonRes).1
          (rayExitVerticalStrictLtFrontierUpperSite c u hgapCU hnonRes).2 →
        DartReachable F
          (rayExitAnchorDartMap F (rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes))
          (rayExitAnchorDartMap F
            (rayExitVerticalStrictLtFrontierUpperSite c u hgapCU hnonRes))
    intro hgapCU hidx
    rw [rayExitIndex_ltFrontierUpperSite_eq c u hgapCU hnonRes] at hidx
    exact hresidual.1 a b hup hlt hgap hnon hresGap hnonRes hgapCU hidx
  · intro a b hup hlt hgap hnon hresGap hnonRes
    let c := rayExitVerticalStrictLtFrontierSite a b hgap hnon
    let u := rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon
    change (hgapCU : rayExitIndex F c.1 c.2 + 1 < rayExitIndex F u.1 u.2) →
      rayExitIndex F (rayExitVerticalStrictLtFrontierUpperSite c u hgapCU hnonRes).1
          (rayExitVerticalStrictLtFrontierUpperSite c u hgapCU hnonRes).2 <
        rayExitIndex F (rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes).1
          (rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes).2 →
        DartReachable F
          (rayExitAnchorDartMap F (rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes))
          (rayExitAnchorDartMap F
            (rayExitVerticalStrictLtFrontierUpperSite c u hgapCU hnonRes))
    intro hgapCU hidx
    rw [rayExitIndex_ltFrontierUpperSite_eq c u hgapCU hnonRes] at hidx
    exact hresidual.2 a b hup hlt hgap hnon hresGap hnonRes hgapCU hidx

/-- Residual-index ordered residual upper-prefix-site data recover the combined ordered input. -/
theorem rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualUpperSiteOrdered_of_residual
    (hresidual :
      RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualUpperSiteResidualOrderedReachable
        F) :
    RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualUpperSiteOrderedReachable
      F :=
  ⟨rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteOrdered_of_residual
      hresidual.1,
    hresidual.2⟩

/-- Ordered residual upper-prefix-site data recover the strict residual upper-prefix-site input by
local residual ray-exit index trichotomy. -/
theorem
    rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteStrict_of_ordered
    (hordered :
      RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteOrderedReachable
        F) :
    RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteStrictReachable
      F := by
  intro a b hup hlt hgap hnon hresGap hnonRes
  let c := rayExitVerticalStrictLtFrontierSite a b hgap hnon
  let u := rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon
  change (hgapCU : rayExitIndex F c.1 c.2 + 1 < rayExitIndex F u.1 u.2) →
    rayExitIndex F (rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes).1
        (rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes).2 ≠
      rayExitIndex F (rayExitVerticalStrictLtFrontierUpperSite c u hgapCU hnonRes).1
        (rayExitVerticalStrictLtFrontierUpperSite c u hgapCU hnonRes).2 →
      DartReachable F
        (rayExitAnchorDartMap F (rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes))
        (rayExitAnchorDartMap F
          (rayExitVerticalStrictLtFrontierUpperSite c u hgapCU hnonRes))
  intro hgapCU hidx
  rcases lt_or_gt_of_ne hidx with hltLocal | hgtLocal
  · exact hordered.1 a b hup hlt hgap hnon hresGap hnonRes hgapCU hltLocal
  · exact hordered.2 a b hup hlt hgap hnon hresGap hnonRes hgapCU hgtLocal

/-- Ordered residual upper-prefix-site data recover the strict combined input, leaving the
upper-first residual frontier legs unchanged. -/
theorem rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualUpperSiteStrict_of_ordered
    (hordered :
      RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualUpperSiteOrderedReachable
        F) :
    RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualUpperSiteStrictReachable
      F :=
  ⟨rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteStrict_of_ordered
      hordered.1,
    hordered.2⟩

/-- Strict residual upper-prefix-site data recover the lower residual upper-prefix-site input:
equal residual ray-exit indices give shared anchor vertices, while unequal indices are delegated
to the strict input. -/
theorem
    rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteReachable_of_strict
    (hstrict :
      RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteStrictReachable
        F) :
    RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtNonStripFrontierUpperSiteReachable
      F := by
  intro a b hup hlt hgap hnon hresGap hnonRes
  let c := rayExitVerticalStrictLtFrontierSite a b hgap hnon
  let u := rayExitVerticalStrictLtFrontierUpperSite a b hgap hnon
  change (hgapCU : rayExitIndex F c.1 c.2 + 1 < rayExitIndex F u.1 u.2) →
    DartReachable F
      (rayExitAnchorDartMap F (rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes))
      (rayExitAnchorDartMap F
        (rayExitVerticalStrictLtFrontierUpperSite c u hgapCU hnonRes))
  intro hgapCU
  let p := rayExitVerticalStrictLtFrontierSite c u hgapCU hnonRes
  let q := rayExitVerticalStrictLtFrontierUpperSite c u hgapCU hnonRes
  by_cases hidx : rayExitIndex F p.1 p.2 = rayExitIndex F q.1 q.2
  · have hupCU : u.1 = c.1 + unitVec2 1 := by
      dsimp [c, u]
      exact rayExitVerticalStrictLtFrontierUpperSite_eq_frontierSite_add_e1
        a b hup hgap hnon
    have hupPQ : q.1 = p.1 + unitVec2 1 := by
      dsimp [p, q]
      exact rayExitVerticalStrictLtFrontierUpperSite_eq_frontierSite_add_e1
        c u hupCU hgapCU hnonRes
    obtain ⟨_, hvp, hvq⟩ :=
      rayExitAnchorDartMap_add_e1_shared_of_index_eq p q hupPQ hidx.symm
    exact dartReachable_of_shared hvp hvq
  · exact hstrict a b hup hlt hgap hnon hresGap hnonRes hgapCU hidx

/-- Strict residual upper-prefix-site data recover the residual upper-prefix-site input. -/
theorem rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualUpperSiteReachable_of_strict
    (hstrict :
      RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualUpperSiteStrictReachable
        F) :
    RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualNonStripFrontierUpperSiteReachable
      F :=
  ⟨rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualLtUpperSiteReachable_of_strict
      hstrict.1,
    hstrict.2⟩

/-- The lower `DartReachable` frontier-split input follows from the automatic lower
bridge-to-frontier turn chain, the existing anchoring input at the frontier dart, and the remaining
frontier-site-anchor turn chain. -/
theorem rayExitVerticalStrictLtBridgeFrontierChain_of_frontierSiteAnchorTurnChain
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hsite : RayExitVerticalStrictLtFrontierSiteAnchorTurnChain F) :
    RayExitVerticalStrictLtBridgeFrontierChain F := by
  intro a b hup hlt hgap hnon
  exact ⟨dartReachable_of_turnChain
      (nextDartTurnChain_ltBridgeDart_ltFrontierDart a b hup hlt hgap hnon),
    (dartReachable_rayExitVerticalStrictLtFrontierDart_frontierSiteAnchor hanchor
      a b hgap hnon).trans
      (dartReachable_of_turnChain (hsite a b hup hlt hgap hnon))⟩

/-- The lower `DartReachable` frontier-split input follows from the automatic lower
bridge-to-frontier turn chain, the existing anchoring input at the frontier dart, and a reachable
frontier-site-anchor to upper-prefix-site-anchor leg. -/
theorem rayExitVerticalStrictLtBridgeFrontierChain_of_upperSiteAnchorReachable
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hreach : RayExitVerticalStrictLtFrontierUpperSiteAnchorReachable F) :
    RayExitVerticalStrictLtBridgeFrontierChain F := by
  intro a b hup hlt hgap hnon
  have hleg := hreach a b hup hlt hgap hnon
  rw [rayExitAnchorDartMap_ltFrontierUpperSite_eq a b hgap hnon] at hleg
  exact ⟨dartReachable_of_turnChain
      (nextDartTurnChain_ltBridgeDart_ltFrontierDart a b hup hlt hgap hnon),
    (dartReachable_rayExitVerticalStrictLtFrontierDart_frontierSiteAnchor hanchor
      a b hgap hnon).trans hleg⟩

/-- Lower frontier-anchor data recover the full lower turn-chain input, because the lower
bridge-to-frontier leg is now automatic. -/
theorem rayExitVerticalStrictLtBridgeFrontierTurnChain_of_frontierAnchorTurnChain
    (hfrontier : RayExitVerticalStrictLtFrontierAnchorTurnChain F) :
    RayExitVerticalStrictLtBridgeFrontierTurnChain F := by
  intro a b hup hlt hgap hnon
  exact ⟨nextDartTurnChain_ltBridgeDart_ltFrontierDart a b hup hlt hgap hnon,
    hfrontier a b hup hlt hgap hnon⟩

/-! ## Lower-reduced route input -/

/-- Full non-strip turn-chain data with only the lower bridge-to-frontier leg discharged.
The upper-exits-first input remains the existing turn-chain input. -/
def RayExitVerticalStrictBridgeFrontierLtReducedTurnChainStep
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  RayExitVerticalStrictLtFrontierAnchorTurnChain F ∧
    RayExitVerticalStrictGtBridgeFrontierTurnChain F

/-- Full non-strip turn-chain data with the lower frontier-anchor leg split through the
frontier site's own ray-exit anchor.  The upper-exits-first input is unchanged. -/
def RayExitVerticalStrictBridgeFrontierLtAnchorSplitTurnChainStep
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  RayExitVerticalStrictLtFrontierAnchorSplitTurnChain F ∧
    RayExitVerticalStrictGtBridgeFrontierTurnChain F

/-- Full non-strip data with the lower frontier-dart-to-frontier-site-anchor leg consumed by the
existing anchoring input.  The remaining lower local turn-chain input starts at the frontier site's
ray-exit anchor, while the upper-exits-first input is unchanged. -/
def RayExitVerticalStrictBridgeFrontierLtSiteAnchorTurnChainStep
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  RayExitVerticalStrictLtFrontierSiteAnchorTurnChain F ∧
    RayExitVerticalStrictGtBridgeFrontierTurnChain F

/-- Full non-strip data with the remaining lower site-anchor leg split through the upper ray point
at the first lower frontier index.  The upper-exits-first input is unchanged. -/
def RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorTurnChainStep
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  RayExitVerticalStrictLtFrontierUpperSiteAnchorTurnChain F ∧
    RayExitVerticalStrictGtBridgeFrontierTurnChain F

/-- Full non-strip data with the remaining lower site-anchor leg required only as
`DartReachable` through the upper-prefix site.  The upper-exits-first input is unchanged. -/
def RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  RayExitVerticalStrictLtFrontierUpperSiteAnchorReachable F ∧
    RayExitVerticalStrictGtBridgeFrontierTurnChain F

/-- Full non-strip data with only the unequal-index lower frontier-site to upper-prefix-site
anchor leg left as a `DartReachable` input.  Equal indices are automatic by shared vertices, and
the upper-exits-first input is unchanged. -/
def RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorStrictReachableStep
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  RayExitVerticalStrictLtFrontierUpperSiteAnchorStrictReachable F ∧
    RayExitVerticalStrictGtBridgeFrontierTurnChain F

/-- Full non-strip data with the unequal-index lower frontier-site to upper-prefix-site anchor leg
split by local ray-exit index order.  The upper-exits-first input is unchanged. -/
def RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorOrderedReachableStep
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  RayExitVerticalStrictLtFrontierUpperSiteAnchorOrderedReachable F ∧
    RayExitVerticalStrictGtBridgeFrontierTurnChain F

/-- Full non-strip data with the lower ordered leg written in residual-index form.  The
upper-exits-first input is unchanged. -/
def RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualOrderedReachableStep
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualOrderedReachable F ∧
    RayExitVerticalStrictGtBridgeFrontierTurnChain F

/-- Full non-strip data with the lower residual-index ordered leg reduced to genuine residual
gaps.  The adjacent residual cases are automatic, and the upper-exits-first input is unchanged. -/
def RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualGapReachableStep
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualGapReachable F ∧
    RayExitVerticalStrictGtBridgeFrontierTurnChain F

/-- Full non-strip data with the lower residual-index ordered leg reduced to non-strip residual
gaps.  The adjacent and straight-strip residual cases are automatic, and the upper-exits-first
input is unchanged. -/
def RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripReachableStep
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualNonStripReachable F ∧
    RayExitVerticalStrictGtBridgeFrontierTurnChain F

/-- Full non-strip data with the lower residual non-strip leg reduced to the local residual bridge
input.  The automatic endpoint anchor-to-bridge steps are not part of this input, and the
upper-exits-first input is unchanged. -/
def RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripBridgeReachableStep
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualNonStripBridgeReachable F ∧
    RayExitVerticalStrictGtBridgeFrontierTurnChain F

/-- Full non-strip data with the lower residual bridge input split through the first local
residual frontier dart.  The upper-exits-first input is unchanged. -/
def RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripFrontierReachableStep
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualNonStripFrontierReachable F ∧
    RayExitVerticalStrictGtBridgeFrontierTurnChain F

/-- Full non-strip data with the lower residual post-frontier leg split through the residual
frontier-site anchor.  The upper-exits-first input is unchanged. -/
def RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripFrontierSiteStep
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualNonStripFrontierSiteReachable F ∧
    RayExitVerticalStrictGtBridgeFrontierTurnChain F

/-- Full non-strip data with the lower residual post-frontier leg ending at the residual
upper-prefix-site anchor.  The upper-exits-first input is unchanged. -/
def RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripFrontierUpperSiteStep
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualNonStripFrontierUpperSiteReachable
      F ∧
    RayExitVerticalStrictGtBridgeFrontierTurnChain F

/-- Full non-strip data with the lower residual upper-prefix-site leg reduced to its strict
unequal-index subcase.  The upper-exits-first input is unchanged. -/
def RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteStrictStep
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualUpperSiteStrictReachable
      F ∧
    RayExitVerticalStrictGtBridgeFrontierTurnChain F

/-- Full non-strip data with the strict residual upper-prefix-site leg split by local residual
ray-exit index order.  The upper-exits-first input is unchanged. -/
def RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteOrderedStep
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualUpperSiteOrderedReachable
      F ∧
    RayExitVerticalStrictGtBridgeFrontierTurnChain F

/-- Full non-strip data with the residual upper-prefix-site ordered leg written in residual-index
form.  The upper-exits-first input is unchanged. -/
def
RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualOrderedStep
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualUpperSiteResidualOrderedReachable
      F ∧
    RayExitVerticalStrictGtBridgeFrontierTurnChain F

/-- Full non-strip data with adjacent residual-index cases of the residual upper-prefix-site ordered
leg discharged.  The upper-exits-first input is unchanged. -/
def
RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualGapStep
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualUpperSiteResidualGapReachable
      F ∧
    RayExitVerticalStrictGtBridgeFrontierTurnChain F

/-- Full non-strip data with straight residual strips of the residual upper-prefix-site residual
leg discharged.  The upper-exits-first input is unchanged. -/
def
RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualNonStripStep
    (F : Finset (Fin 2 → ℤ)) : Prop :=
  RayExitVerticalStrictLtFrontierUpperSiteAnchorResidualUpperSiteResidualNonStripReachable
      F ∧
    RayExitVerticalStrictGtBridgeFrontierTurnChain F

/-- Lower-reduced data recover the existing full turn-chain input. -/
theorem rayExitVerticalStrictBridgeFrontierTurnChainStep_of_ltReducedTurnChainStep
    (hreduced : RayExitVerticalStrictBridgeFrontierLtReducedTurnChainStep F) :
    RayExitVerticalStrictBridgeFrontierTurnChainStep F :=
  ⟨rayExitVerticalStrictLtBridgeFrontierTurnChain_of_frontierAnchorTurnChain hreduced.1,
    hreduced.2⟩

/-- Lower frontier-anchor split data recover the lower-reduced turn-chain input. -/
theorem rayExitVerticalStrictBridgeFrontierLtReducedTurnChainStep_of_ltAnchorSplit
    (hsplit : RayExitVerticalStrictBridgeFrontierLtAnchorSplitTurnChainStep F) :
    RayExitVerticalStrictBridgeFrontierLtReducedTurnChainStep F :=
  ⟨rayExitVerticalStrictLtFrontierAnchorTurnChain_of_splitTurnChain hsplit.1, hsplit.2⟩

/-- Lower frontier-anchor split data recover the existing full turn-chain input. -/
theorem rayExitVerticalStrictBridgeFrontierTurnChainStep_of_ltAnchorSplit
    (hsplit : RayExitVerticalStrictBridgeFrontierLtAnchorSplitTurnChainStep F) :
    RayExitVerticalStrictBridgeFrontierTurnChainStep F :=
  rayExitVerticalStrictBridgeFrontierTurnChainStep_of_ltReducedTurnChainStep
    (rayExitVerticalStrictBridgeFrontierLtReducedTurnChainStep_of_ltAnchorSplit hsplit)

/-- The site-anchor lower input and unchanged upper turn-chain input recover the `DartReachable`
frontier-split input once the existing anchoring input is supplied. -/
theorem rayExitVerticalStrictBridgeFrontierChainStep_of_ltSiteAnchorTurnChainStep
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hsite : RayExitVerticalStrictBridgeFrontierLtSiteAnchorTurnChainStep F) :
    RayExitVerticalStrictBridgeFrontierChainStep F :=
  ⟨rayExitVerticalStrictLtBridgeFrontierChain_of_frontierSiteAnchorTurnChain hanchor hsite.1,
    rayExitVerticalStrictGtBridgeFrontierChain_of_nextDartChain
      (rayExitVerticalStrictGtBridgeFrontierNextDartChain_of_turnChain hsite.2)⟩

/-- Upper-prefix site-anchor data recover the lower site-anchor input. -/
theorem rayExitVerticalStrictBridgeFrontierLtSiteAnchorTurnChainStep_of_ltUpperSiteAnchor
    (hupper : RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorTurnChainStep F) :
    RayExitVerticalStrictBridgeFrontierLtSiteAnchorTurnChainStep F :=
  ⟨rayExitVerticalStrictLtFrontierSiteAnchorTurnChain_of_upperSiteAnchorTurnChain hupper.1,
    hupper.2⟩

/-- Upper-prefix site-anchor data recover the `DartReachable` frontier-split input once the
existing anchoring input is supplied. -/
theorem rayExitVerticalStrictBridgeFrontierChainStep_of_ltUpperSiteAnchorTurnChainStep
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hupper : RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorTurnChainStep F) :
    RayExitVerticalStrictBridgeFrontierChainStep F :=
  rayExitVerticalStrictBridgeFrontierChainStep_of_ltSiteAnchorTurnChainStep hanchor
    (rayExitVerticalStrictBridgeFrontierLtSiteAnchorTurnChainStep_of_ltUpperSiteAnchor hupper)

/-- Strict lower frontier-site-to-upper-prefix reachable data recover the reachable-step input. -/
theorem
    rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep_of_strictReachable
    (hstrict : RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorStrictReachableStep F) :
    RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep F :=
  ⟨rayExitVerticalStrictLtFrontierUpperSiteAnchorReachable_of_strictReachable hstrict.1,
    hstrict.2⟩

/-- Ordered lower frontier-site-to-upper-prefix reachable data recover the strict-reachable-step
input. -/
theorem rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorStrictReachableStep_of_ordered
    (hordered : RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorOrderedReachableStep F) :
    RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorStrictReachableStep F :=
  ⟨rayExitVerticalStrictLtFrontierUpperSiteAnchorStrictReachable_of_orderedReachable
      hordered.1,
    hordered.2⟩

/-- Ordered lower frontier-site-to-upper-prefix reachable data recover the reachable-step input. -/
theorem rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep_of_ordered
    (hordered : RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorOrderedReachableStep F) :
    RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep F :=
  rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep_of_strictReachable
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorStrictReachableStep_of_ordered
      hordered)

/-- Residual-index ordered lower frontier-site-to-upper-prefix reachable data recover the
local-index ordered-step input. -/
theorem rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorOrderedReachableStep_of_residual
    (hresidual :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualOrderedReachableStep F) :
    RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorOrderedReachableStep F :=
  ⟨rayExitVerticalStrictLtFrontierUpperSiteAnchorOrderedReachable_of_residualOrdered
      hresidual.1,
    hresidual.2⟩

/-- Gap-reduced residual lower frontier-site-to-upper-prefix reachable data recover the
residual-index ordered-step input. -/
theorem rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualOrderedReachableStep_of_gap
    (hgapReach :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualGapReachableStep F) :
    RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualOrderedReachableStep F :=
  ⟨rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualOrderedReachable_of_gap
      hgapReach.1,
    hgapReach.2⟩

/-- Non-strip residual lower frontier-site-to-upper-prefix reachable data recover the residual-gap
step input. -/
theorem rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualGapReachableStep_of_nonStrip
    (hnonStrip :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripReachableStep F) :
    RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualGapReachableStep F :=
  ⟨rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualGapReachable_of_nonStrip
      hnonStrip.1,
    hnonStrip.2⟩

/-- Non-strip residual lower frontier-site-to-upper-prefix reachable data recover the
residual-index ordered-step input. -/
theorem
    rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualOrderedReachableStep_of_nonStrip
    (hnonStrip :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripReachableStep F) :
    RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualOrderedReachableStep F :=
  rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualOrderedReachableStep_of_gap
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualGapReachableStep_of_nonStrip
      hnonStrip)

/-- Residual bridge data recover the residual non-strip step input. -/
theorem rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripReachableStep_of_bridge
    (hbridge :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripBridgeReachableStep F) :
    RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripReachableStep F :=
  ⟨rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualNonStripReachable_of_bridge
      hbridge.1,
    hbridge.2⟩

/-- Residual bridge data recover the residual-gap step input. -/
theorem rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualGapReachableStep_of_bridge
    (hbridge :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripBridgeReachableStep F) :
    RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualGapReachableStep F :=
  rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualGapReachableStep_of_nonStrip
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripReachableStep_of_bridge
      hbridge)

/-- Residual frontier data recover the residual bridge step input. -/
theorem
    rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualBridgeReachableStep_of_frontier
    (hfrontier :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripFrontierReachableStep
        F) :
    RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripBridgeReachableStep F :=
  ⟨rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualBridgeReachable_of_frontier
      hfrontier.1,
    hfrontier.2⟩

/-- Residual frontier data recover the residual non-strip step input. -/
theorem
    rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripReachableStep_of_frontier
    (hfrontier :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripFrontierReachableStep
        F) :
    RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripReachableStep F :=
  rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripReachableStep_of_bridge
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualBridgeReachableStep_of_frontier
      hfrontier)

/-- Residual frontier data recover the residual-gap step input. -/
theorem
    rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualGapReachableStep_of_frontier
    (hfrontier :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripFrontierReachableStep
        F) :
    RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualGapReachableStep F :=
  rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualGapReachableStep_of_bridge
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualBridgeReachableStep_of_frontier
      hfrontier)

/-- Residual site-anchor data recover the residual frontier step input once the existing anchoring
input supplies the residual frontier-dart-to-site-anchor leg. -/
theorem
    rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualFrontierStep_of_site
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hsite :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripFrontierSiteStep F) :
    RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripFrontierReachableStep F :=
  ⟨rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualFrontierReachable_of_site
      hanchor hsite.1,
    hsite.2⟩

/-- Residual site-anchor data recover the residual bridge step input once the existing anchoring
input supplies the residual frontier-dart-to-site-anchor leg. -/
theorem
    rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualBridgeStep_of_site
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hsite :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripFrontierSiteStep F) :
    RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripBridgeReachableStep F :=
  rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualBridgeReachableStep_of_frontier
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualFrontierStep_of_site hanchor
      hsite)

/-- Residual-index ordered lower frontier-site-to-upper-prefix reachable data recover the
reachable-step input. -/
theorem rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep_of_residual
    (hresidual :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualOrderedReachableStep F) :
    RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep F :=
  rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep_of_ordered
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorOrderedReachableStep_of_residual
      hresidual)

/-- Gap-reduced residual lower frontier-site-to-upper-prefix reachable data recover the
reachable-step input. -/
theorem rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep_of_residualGap
    (hgapReach :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualGapReachableStep F) :
    RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep F :=
  rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep_of_residual
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualOrderedReachableStep_of_gap
      hgapReach)

/-- Non-strip residual lower frontier-site-to-upper-prefix reachable data recover the
reachable-step input. -/
theorem rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep_of_residualNonStrip
    (hnonStrip :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripReachableStep F) :
    RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep F :=
  rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep_of_residualGap
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualGapReachableStep_of_nonStrip
      hnonStrip)

/-- Residual bridge data recover the reachable-step input. -/
theorem rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep_of_residualBridge
    (hbridge :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripBridgeReachableStep F) :
    RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep F :=
  rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep_of_residualNonStrip
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripReachableStep_of_bridge
      hbridge)

/-- Residual frontier data recover the reachable-step input. -/
theorem
    rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep_of_residualFrontier
    (hfrontier :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripFrontierReachableStep
        F) :
    RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep F :=
  rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep_of_residualBridge
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualBridgeReachableStep_of_frontier
      hfrontier)

/-- Residual site-anchor data recover the reachable-step input once the existing anchoring input
supplies the residual frontier-dart-to-site-anchor leg. -/
theorem rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep_of_residualSite
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hsite :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripFrontierSiteStep F) :
    RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep F :=
  rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep_of_residualFrontier
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualFrontierStep_of_site hanchor
      hsite)

/-- Residual upper-prefix-site data recover the residual site-anchor step input. -/
theorem rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualSiteStep_of_upperSite
    (hupper :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripFrontierUpperSiteStep
        F) :
    RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripFrontierSiteStep F :=
  ⟨rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualSiteReachable_of_upperSite
      hupper.1,
    hupper.2⟩

/-- Residual upper-prefix-site data recover the reachable-step input once the existing anchoring
input supplies the residual frontier-dart-to-site-anchor leg. -/
theorem
    rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep_of_residualUpperSite
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hupper :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripFrontierUpperSiteStep
        F) :
    RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep F :=
  rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep_of_residualSite hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualSiteStep_of_upperSite hupper)

/-- Strict residual upper-prefix-site data recover the residual upper-prefix-site step input. -/
theorem
    rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteStep_of_strict
    (hstrict :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteStrictStep
        F) :
    RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripFrontierUpperSiteStep F :=
  ⟨rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualUpperSiteReachable_of_strict
      hstrict.1,
    hstrict.2⟩

/-- Ordered residual upper-prefix-site data recover the strict residual upper-prefix-site step
input. -/
theorem
    rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteStrictStep_of_ordered
    (hordered :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteOrderedStep
        F) :
    RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteStrictStep
      F :=
  ⟨rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualUpperSiteStrict_of_ordered
      hordered.1,
    hordered.2⟩

/-- Residual-index ordered residual upper-prefix-site data recover the ordered step input. -/
theorem
    rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteOrderedStep_of_residual
    (hresidual :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualOrderedStep
        F) :
    RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteOrderedStep
      F :=
  ⟨rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualUpperSiteOrdered_of_residual
      hresidual.1,
    hresidual.2⟩

/-- Gap-reduced residual-index residual upper-prefix-site data recover the residual-index ordered
step input. -/
theorem
    rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualStep_of_gap
    (hgap :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualGapStep
        F) :
    RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualOrderedStep
      F :=
  ⟨rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualUpperSiteResidualOrdered_of_gap
      hgap.1,
    hgap.2⟩

/-- Non-strip residual-index residual upper-prefix-site data recover the residual-gap step input. -/
theorem
    rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualGap_of_resNS
    (hnonStrip :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualNonStripStep
        F) :
    RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualGapStep
      F :=
  ⟨rayExitVerticalStrictLtFrontierUpperSiteAnchorResidualUpperSiteResidualGap_of_nonStrip
      hnonStrip.1,
    hnonStrip.2⟩

/-- Non-strip residual-index residual upper-prefix-site data recover the residual-index ordered
step input. -/
theorem
    rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualStep_of_nonStrip
    (hnonStrip :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualNonStripStep
        F) :
    RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualOrderedStep
      F :=
  rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualStep_of_gap
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualGap_of_resNS
      hnonStrip)

/-- Residual-index ordered residual upper-prefix-site data recover the strict step input. -/
theorem
    rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteStrictStep_of_residual
    (hresidual :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualOrderedStep
        F) :
    RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteStrictStep
      F :=
  rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteStrictStep_of_ordered
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteOrderedStep_of_residual
      hresidual)

/-- Gap-reduced residual-index residual upper-prefix-site data recover the strict step input. -/
theorem
    rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteStrictStep_of_residualGap
    (hgap :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualGapStep
        F) :
    RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteStrictStep
      F :=
  rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteStrictStep_of_residual
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualStep_of_gap
      hgap)

/-- Non-strip residual-index residual upper-prefix-site data recover the strict step input. -/
theorem
    rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteStrictStep_of_resNonStrip
    (hnonStrip :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualNonStripStep
        F) :
    RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteStrictStep
      F :=
  rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteStrictStep_of_residual
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualStep_of_nonStrip
      hnonStrip)

/-- Ordered residual upper-prefix-site data recover the residual upper-prefix-site step input. -/
theorem
    rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteStep_of_ordered
    (hordered :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteOrderedStep
        F) :
    RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripFrontierUpperSiteStep F :=
  rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteStep_of_strict
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteStrictStep_of_ordered
      hordered)

/-- Residual-index ordered residual upper-prefix-site data recover the residual upper-prefix-site
step input. -/
theorem
    rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteStep_of_residual
    (hresidual :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualOrderedStep
        F) :
    RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripFrontierUpperSiteStep F :=
  rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteStep_of_ordered
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteOrderedStep_of_residual
      hresidual)

/-- Gap-reduced residual-index residual upper-prefix-site data recover the residual
upper-prefix-site step input. -/
theorem
    rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteStep_of_residualGap
    (hgap :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualGapStep
        F) :
    RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripFrontierUpperSiteStep F :=
  rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteStep_of_residual
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualStep_of_gap
      hgap)

/-- Non-strip residual-index residual upper-prefix-site data recover the residual
upper-prefix-site step input. -/
theorem
    rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteStep_of_resNonStrip
    (hnonStrip :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualNonStripStep
        F) :
    RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripFrontierUpperSiteStep F :=
  rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteStep_of_residual
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualStep_of_nonStrip
      hnonStrip)

/-- Strict residual upper-prefix-site data recover the reachable-step input once the existing
anchoring input supplies the residual frontier-dart-to-site-anchor leg. -/
theorem
    rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep_of_residualUpperStrict
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hstrict :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteStrictStep
        F) :
    RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep F :=
  rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep_of_residualUpperSite hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteStep_of_strict
      hstrict)

/-- Ordered residual upper-prefix-site data recover the reachable-step input once the existing
anchoring input supplies the residual frontier-dart-to-site-anchor leg. -/
theorem
    rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep_of_residualUpperOrdered
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hordered :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteOrderedStep
        F) :
    RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep F :=
  rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep_of_residualUpperStrict
    hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteStrictStep_of_ordered
      hordered)

/-- Residual-index ordered residual upper-prefix-site data recover the reachable-step input once
the existing anchoring input supplies the residual frontier-dart-to-site-anchor leg. -/
theorem
    rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep_of_residualUpperResidual
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hresidual :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualOrderedStep
        F) :
    RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep F :=
  rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep_of_residualUpperOrdered
    hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteOrderedStep_of_residual
      hresidual)

/-- Gap-reduced residual-index residual upper-prefix-site data recover the reachable-step input once
the existing anchoring input supplies the residual frontier-dart-to-site-anchor leg. -/
theorem
    rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep_of_residualUpperResidualGap
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hgap :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualGapStep
        F) :
    RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep F :=
  rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep_of_residualUpperResidual
    hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualStep_of_gap
      hgap)

/-- Non-strip residual-index residual upper-prefix-site data recover the reachable-step input once
the existing anchoring input supplies the residual frontier-dart-to-site-anchor leg. -/
theorem
    rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep_of_residualUpperResNonStrip
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hnonStrip :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualNonStripStep
        F) :
    RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep F :=
  rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep_of_residualUpperResidual
    hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualStep_of_nonStrip
      hnonStrip)

/-- Lower upper-prefix reachable data recover the `DartReachable` frontier-split input once the
existing anchoring input is supplied. -/
theorem rayExitVerticalStrictBridgeFrontierChainStep_of_ltUpperSiteAnchorReachableStep
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hreach : RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep F) :
    RayExitVerticalStrictBridgeFrontierChainStep F :=
  ⟨rayExitVerticalStrictLtBridgeFrontierChain_of_upperSiteAnchorReachable hanchor hreach.1,
    rayExitVerticalStrictGtBridgeFrontierChain_of_nextDartChain
      (rayExitVerticalStrictGtBridgeFrontierNextDartChain_of_turnChain hreach.2)⟩

/-- Residual upper-prefix-site data recover the `DartReachable` frontier-split input once the
existing anchoring input is supplied. -/
theorem rayExitVerticalStrictBridgeFrontierChainStep_of_ltUpperSiteAnchorResidualUpperSite
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hupper :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripFrontierUpperSiteStep
        F) :
    RayExitVerticalStrictBridgeFrontierChainStep F :=
  rayExitVerticalStrictBridgeFrontierChainStep_of_ltUpperSiteAnchorReachableStep hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep_of_residualUpperSite
      hanchor hupper)

/-- Strict residual upper-prefix-site data recover the `DartReachable` frontier-split input once
the existing anchoring input is supplied. -/
theorem rayExitVerticalStrictBridgeFrontierChainStep_of_ltUpperSiteAnchorResidualUpperStrict
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hstrict :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteStrictStep
        F) :
    RayExitVerticalStrictBridgeFrontierChainStep F :=
  rayExitVerticalStrictBridgeFrontierChainStep_of_ltUpperSiteAnchorResidualUpperSite hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteStep_of_strict
      hstrict)

/-- Ordered residual upper-prefix-site data recover the `DartReachable` frontier-split input once
the existing anchoring input is supplied. -/
theorem rayExitVerticalStrictBridgeFrontierChainStep_of_ltUpperSiteAnchorResidualUpperOrdered
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hordered :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteOrderedStep
        F) :
    RayExitVerticalStrictBridgeFrontierChainStep F :=
  rayExitVerticalStrictBridgeFrontierChainStep_of_ltUpperSiteAnchorResidualUpperStrict hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteStrictStep_of_ordered
      hordered)

/-- Residual-index ordered residual upper-prefix-site data recover the `DartReachable`
frontier-split input once the existing anchoring input is supplied. -/
theorem rayExitVerticalStrictBridgeFrontierChainStep_of_ltUpperSiteAnchorResidualUpperResidual
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hresidual :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualOrderedStep
        F) :
    RayExitVerticalStrictBridgeFrontierChainStep F :=
  rayExitVerticalStrictBridgeFrontierChainStep_of_ltUpperSiteAnchorResidualUpperOrdered hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteOrderedStep_of_residual
      hresidual)

/-- Gap-reduced residual-index residual upper-prefix-site data recover the `DartReachable`
frontier-split input once the existing anchoring input is supplied. -/
theorem rayExitVerticalStrictBridgeFrontierChainStep_of_ltUpperSiteAnchorResidualUpperResidualGap
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hgap :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualGapStep
        F) :
    RayExitVerticalStrictBridgeFrontierChainStep F :=
  rayExitVerticalStrictBridgeFrontierChainStep_of_ltUpperSiteAnchorResidualUpperResidual hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualStep_of_gap
      hgap)

/-- Non-strip residual-index residual upper-prefix-site data recover the `DartReachable`
frontier-split input once the existing anchoring input is supplied. -/
theorem
    rayExitVerticalStrictBridgeFrontierChainStep_of_ltUpperSiteAnchorResidualUpperResNonStrip
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hnonStrip :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualNonStripStep
        F) :
    RayExitVerticalStrictBridgeFrontierChainStep F :=
  rayExitVerticalStrictBridgeFrontierChainStep_of_ltUpperSiteAnchorResidualUpperResidual hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualStep_of_nonStrip
      hnonStrip)

/-- Strict lower upper-prefix reachable data recover the `DartReachable` frontier-split input once
the existing anchoring input is supplied. -/
theorem rayExitVerticalStrictBridgeFrontierChainStep_of_ltUpperSiteAnchorStrictReachable
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hstrict : RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorStrictReachableStep F) :
    RayExitVerticalStrictBridgeFrontierChainStep F :=
  rayExitVerticalStrictBridgeFrontierChainStep_of_ltUpperSiteAnchorReachableStep hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep_of_strictReachable
      hstrict)

/-- Ordered lower upper-prefix reachable data recover the `DartReachable` frontier-split input
once the existing anchoring input is supplied. -/
theorem rayExitVerticalStrictBridgeFrontierChainStep_of_ltUpperSiteAnchorOrderedReachable
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hordered : RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorOrderedReachableStep F) :
    RayExitVerticalStrictBridgeFrontierChainStep F :=
  rayExitVerticalStrictBridgeFrontierChainStep_of_ltUpperSiteAnchorStrictReachable hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorStrictReachableStep_of_ordered
      hordered)

/-- Residual-index ordered lower upper-prefix reachable data recover the `DartReachable`
frontier-split input once the existing anchoring input is supplied. -/
theorem rayExitVerticalStrictBridgeFrontierChainStep_of_ltUpperSiteAnchorResidualOrdered
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hresidual :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualOrderedReachableStep F) :
    RayExitVerticalStrictBridgeFrontierChainStep F :=
  rayExitVerticalStrictBridgeFrontierChainStep_of_ltUpperSiteAnchorOrderedReachable hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorOrderedReachableStep_of_residual
      hresidual)

/-- Gap-reduced residual lower upper-prefix reachable data recover the `DartReachable`
frontier-split input once the existing anchoring input is supplied. -/
theorem rayExitVerticalStrictBridgeFrontierChainStep_of_ltUpperSiteAnchorResidualGap
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hgapReach :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualGapReachableStep F) :
    RayExitVerticalStrictBridgeFrontierChainStep F :=
  rayExitVerticalStrictBridgeFrontierChainStep_of_ltUpperSiteAnchorResidualOrdered hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualOrderedReachableStep_of_gap
      hgapReach)

/-- Non-strip residual lower upper-prefix reachable data recover the `DartReachable`
frontier-split input once the existing anchoring input is supplied. -/
theorem rayExitVerticalStrictBridgeFrontierChainStep_of_ltUpperSiteAnchorResidualNonStrip
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hnonStrip :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripReachableStep F) :
    RayExitVerticalStrictBridgeFrontierChainStep F :=
  rayExitVerticalStrictBridgeFrontierChainStep_of_ltUpperSiteAnchorResidualGap hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualGapReachableStep_of_nonStrip
      hnonStrip)

/-- Residual bridge data recover the `DartReachable` frontier-split input once the existing
anchoring input is supplied. -/
theorem rayExitVerticalStrictBridgeFrontierChainStep_of_ltUpperSiteAnchorResidualBridge
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hbridge :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripBridgeReachableStep F) :
    RayExitVerticalStrictBridgeFrontierChainStep F :=
  rayExitVerticalStrictBridgeFrontierChainStep_of_ltUpperSiteAnchorResidualNonStrip hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripReachableStep_of_bridge
      hbridge)

/-- Residual frontier data recover the `DartReachable` frontier-split input once the existing
anchoring input is supplied. -/
theorem rayExitVerticalStrictBridgeFrontierChainStep_of_ltUpperSiteAnchorResidualFrontier
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hfrontier :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripFrontierReachableStep
        F) :
    RayExitVerticalStrictBridgeFrontierChainStep F :=
  rayExitVerticalStrictBridgeFrontierChainStep_of_ltUpperSiteAnchorResidualBridge hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualBridgeReachableStep_of_frontier
      hfrontier)

/-- Residual site-anchor data recover the `DartReachable` frontier-split input once the existing
anchoring input is supplied. -/
theorem rayExitVerticalStrictBridgeFrontierChainStep_of_ltUpperSiteAnchorResidualSite
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hsite :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripFrontierSiteStep F) :
    RayExitVerticalStrictBridgeFrontierChainStep F :=
  rayExitVerticalStrictBridgeFrontierChainStep_of_ltUpperSiteAnchorResidualFrontier hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualFrontierStep_of_site hanchor
      hsite)

/-- Pairwise dart reachability from lower-reduced turn-chain non-strip data and within-`F`
connectivity. -/
theorem dartReachable_of_rayExitVerticalStrictBridgeFrontierLtReducedTurnChain
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hreduced : RayExitVerticalStrictBridgeFrontierLtReducedTurnChainStep F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b)
    (d e : BoundaryDart F) : DartReachable F d e :=
  dartReachable_of_rayExitVerticalStrictBridgeFrontierTurnChain hanchor
    (rayExitVerticalStrictBridgeFrontierTurnChainStep_of_ltReducedTurnChainStep hreduced)
    hconn d e

/-- Pairwise dart reachability from lower frontier-anchor split data and within-`F`
connectivity. -/
theorem dartReachable_of_rayExitVerticalStrictBridgeFrontierLtAnchorSplitTurnChain
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hsplit : RayExitVerticalStrictBridgeFrontierLtAnchorSplitTurnChainStep F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b)
    (d e : BoundaryDart F) : DartReachable F d e :=
  dartReachable_of_rayExitVerticalStrictBridgeFrontierLtReducedTurnChain hanchor
    (rayExitVerticalStrictBridgeFrontierLtReducedTurnChainStep_of_ltAnchorSplit hsplit)
    hconn d e

/-- Pairwise dart reachability from lower frontier-site-anchor data and within-`F` connectivity.
The first lower frontier-anchor leg is supplied by the existing anchoring hypothesis. -/
theorem dartReachable_of_rayExitVerticalStrictBridgeFrontierLtSiteAnchorTurnChain
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hsite : RayExitVerticalStrictBridgeFrontierLtSiteAnchorTurnChainStep F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b)
    (d e : BoundaryDart F) : DartReachable F d e :=
  dartReachable_of_rayExitVerticalStrictBridgeFrontierChain hanchor
    (rayExitVerticalStrictBridgeFrontierChainStep_of_ltSiteAnchorTurnChainStep hanchor hsite)
    hconn d e

/-- Pairwise dart reachability from lower upper-prefix site-anchor data and within-`F`
connectivity. -/
theorem dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorTurnChain
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hupper : RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorTurnChainStep F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b)
    (d e : BoundaryDart F) : DartReachable F d e :=
  dartReachable_of_rayExitVerticalStrictBridgeFrontierLtSiteAnchorTurnChain hanchor
    (rayExitVerticalStrictBridgeFrontierLtSiteAnchorTurnChainStep_of_ltUpperSiteAnchor hupper)
    hconn d e

/-- Pairwise dart reachability from lower upper-prefix reachable data and within-`F`
connectivity. -/
theorem dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachable
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hreach : RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b)
    (d e : BoundaryDart F) : DartReachable F d e :=
  dartReachable_of_rayExitVerticalStrictBridgeFrontierChain hanchor
    (rayExitVerticalStrictBridgeFrontierChainStep_of_ltUpperSiteAnchorReachableStep
      hanchor hreach)
    hconn d e

/-- Pairwise dart reachability from lower upper-prefix strict reachable data and within-`F`
connectivity. -/
theorem dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorStrictReachable
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hstrict : RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorStrictReachableStep F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b)
    (d e : BoundaryDart F) : DartReachable F d e :=
  dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachable hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep_of_strictReachable
      hstrict)
    hconn d e

/-- Pairwise dart reachability from lower upper-prefix ordered reachable data and within-`F`
connectivity. -/
theorem dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorOrderedReachable
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hordered : RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorOrderedReachableStep F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b)
    (d e : BoundaryDart F) : DartReachable F d e :=
  dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorStrictReachable hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorStrictReachableStep_of_ordered
      hordered)
    hconn d e

/-- Pairwise dart reachability from residual-index lower upper-prefix ordered reachable data and
within-`F` connectivity. -/
theorem dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualOrdered
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hresidual :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualOrderedReachableStep F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b)
    (d e : BoundaryDart F) : DartReachable F d e :=
  dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorOrderedReachable hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorOrderedReachableStep_of_residual
      hresidual)
    hconn d e

/-- Pairwise dart reachability from gap-reduced residual-index lower upper-prefix reachable data
and within-`F` connectivity. -/
theorem dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualGap
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hgapReach :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualGapReachableStep F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b)
    (d e : BoundaryDart F) : DartReachable F d e :=
  dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualOrdered
    hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualOrderedReachableStep_of_gap
      hgapReach)
    hconn d e

/-- Pairwise dart reachability from non-strip residual-index lower upper-prefix reachable data and
within-`F` connectivity. -/
theorem dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStrip
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hnonStrip :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripReachableStep F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b)
    (d e : BoundaryDart F) : DartReachable F d e :=
  dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualGap
    hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualGapReachableStep_of_nonStrip
      hnonStrip)
    hconn d e

/-- Pairwise dart reachability from residual bridge data and within-`F` connectivity. -/
theorem dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualBridge
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hbridge :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripBridgeReachableStep F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b)
    (d e : BoundaryDart F) : DartReachable F d e :=
  dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStrip
    hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripReachableStep_of_bridge
      hbridge)
    hconn d e

/-- Pairwise dart reachability from residual frontier data and within-`F` connectivity. -/
theorem dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualFrontier
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hfrontier :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripFrontierReachableStep
        F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b)
    (d e : BoundaryDart F) : DartReachable F d e :=
  dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualBridge
    hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualBridgeReachableStep_of_frontier
      hfrontier)
    hconn d e

/-- Pairwise dart reachability from residual site-anchor data and within-`F` connectivity. -/
theorem dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualSite
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hsite :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripFrontierSiteStep F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b)
    (d e : BoundaryDart F) : DartReachable F d e :=
  dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualFrontier
    hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualFrontierStep_of_site hanchor
      hsite)
    hconn d e

/-- Pairwise dart reachability from residual upper-prefix-site data and within-`F`
connectivity. -/
theorem dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSite
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hupper :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripFrontierUpperSiteStep
        F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b)
    (d e : BoundaryDart F) : DartReachable F d e :=
  dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualSite hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualSiteStep_of_upperSite hupper)
    hconn d e

/-- Pairwise dart reachability from strict residual upper-prefix-site data and within-`F`
connectivity. -/
theorem
    dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperStrict
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hstrict :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteStrictStep
        F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b)
    (d e : BoundaryDart F) : DartReachable F d e :=
  dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSite hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteStep_of_strict
      hstrict)
    hconn d e

/-- Pairwise dart reachability from ordered residual upper-prefix-site data and within-`F`
connectivity. -/
theorem
    dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperOrdered
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hordered :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteOrderedStep
        F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b)
    (d e : BoundaryDart F) : DartReachable F d e :=
  dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperStrict
    hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteStrictStep_of_ordered
      hordered)
    hconn d e

/-- Pairwise dart reachability from residual-index ordered residual upper-prefix-site data and
within-`F` connectivity. -/
theorem
    dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperResidual
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hresidual :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualOrderedStep
        F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b)
    (d e : BoundaryDart F) : DartReachable F d e :=
  dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperOrdered
    hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteOrderedStep_of_residual
      hresidual)
    hconn d e

/-- Pairwise dart reachability from gap-reduced residual-index residual upper-prefix-site data and
within-`F` connectivity. -/
theorem
    dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperResidualGap
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hgap :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualGapStep
        F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b)
    (d e : BoundaryDart F) : DartReachable F d e :=
  dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperResidual
    hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualStep_of_gap
      hgap)
    hconn d e

/-- Pairwise dart reachability from non-strip residual-index residual upper-prefix-site data and
within-`F` connectivity. -/
theorem
    dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperResNonStrip
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hnonStrip :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualNonStripStep
        F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b)
    (d e : BoundaryDart F) : DartReachable F d e :=
  dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperResidual
    hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualStep_of_nonStrip
      hnonStrip)
    hconn d e

/-- The common-box dual cut is edge-connected from lower-reduced turn-chain non-strip data. -/
theorem dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtReducedTurnChain
    (hsub : dualSupport F ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hreduced : RayExitVerticalStrictBridgeFrontierLtReducedTurnChainStep F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierTurnChain hsub
    hanchor
    (rayExitVerticalStrictBridgeFrontierTurnChainStep_of_ltReducedTurnChainStep hreduced)
    hconn

/-- The common-box dual cut is edge-connected from lower frontier-anchor split data. -/
theorem dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtAnchorSplit
    (hsub : dualSupport F ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hsplit : RayExitVerticalStrictBridgeFrontierLtAnchorSplitTurnChainStep F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtReducedTurnChain
    hsub hanchor
    (rayExitVerticalStrictBridgeFrontierLtReducedTurnChainStep_of_ltAnchorSplit hsplit)
    hconn

/-- The common-box dual cut is edge-connected from lower frontier-site-anchor data.  The
frontier-dart-to-frontier-site-anchor leg is consumed by the existing anchoring hypothesis. -/
theorem dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtSiteAnchor
    (hsub : dualSupport F ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hsite : RayExitVerticalStrictBridgeFrontierLtSiteAnchorTurnChainStep F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierChain hsub hanchor
    (rayExitVerticalStrictBridgeFrontierChainStep_of_ltSiteAnchorTurnChainStep hanchor hsite)
    hconn

/-- The common-box dual cut is edge-connected from lower upper-prefix site-anchor data. -/
theorem dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchor
    (hsub : dualSupport F ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hupper : RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorTurnChainStep F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtSiteAnchor hsub hanchor
    (rayExitVerticalStrictBridgeFrontierLtSiteAnchorTurnChainStep_of_ltUpperSiteAnchor hupper)
    hconn

/-- The common-box dual cut is edge-connected from lower upper-prefix reachable data. -/
theorem dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteReachable
    (hsub : dualSupport F ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hreach : RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierChain hsub hanchor
    (rayExitVerticalStrictBridgeFrontierChainStep_of_ltUpperSiteAnchorReachableStep
      hanchor hreach)
    hconn

/-- The common-box dual cut is edge-connected from lower upper-prefix strict reachable data. -/
theorem dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteStrict
    (hsub : dualSupport F ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hstrict : RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorStrictReachableStep F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteReachable
    hsub hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep_of_strictReachable
      hstrict)
    hconn

/-- The common-box dual cut is edge-connected from lower upper-prefix ordered reachable data. -/
theorem dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteOrdered
    (hsub : dualSupport F ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hordered : RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorOrderedReachableStep F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteStrict
    hsub hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorStrictReachableStep_of_ordered
      hordered)
    hconn

/-- The common-box dual cut is edge-connected from residual-index lower upper-prefix ordered
reachable data. -/
theorem dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteResidual
    (hsub : dualSupport F ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hresidual :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualOrderedReachableStep F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteOrdered
    hsub hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorOrderedReachableStep_of_residual
      hresidual)
    hconn

/-- The common-box dual cut is edge-connected from gap-reduced residual-index lower upper-prefix
reachable data. -/
theorem dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteResidualGap
    (hsub : dualSupport F ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hgapReach :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualGapReachableStep F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteResidual
    hsub hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualOrderedReachableStep_of_gap
      hgapReach)
    hconn

/-- The common-box dual cut is edge-connected from non-strip residual-index lower upper-prefix
reachable data. -/
theorem
    dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteResidualNonStrip
    (hsub : dualSupport F ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hnonStrip :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripReachableStep F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteResidualGap
    hsub hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualGapReachableStep_of_nonStrip
      hnonStrip)
    hconn

/-- The common-box dual cut is edge-connected from residual bridge data. -/
theorem
    dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteResidualBridge
    (hsub : dualSupport F ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hbridge :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripBridgeReachableStep F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteResidualNonStrip
    hsub hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripReachableStep_of_bridge
      hbridge)
    hconn

/-- The common-box dual cut is edge-connected from residual frontier data. -/
theorem
    dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteResidualFrontier
    (hsub : dualSupport F ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hfrontier :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripFrontierReachableStep
        F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteResidualBridge
    hsub hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualBridgeReachableStep_of_frontier
      hfrontier)
    hconn

/-- The common-box dual cut is edge-connected from residual site-anchor data. -/
theorem
    dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteResidualSite
    (hsub : dualSupport F ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hsite :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripFrontierSiteStep F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteResidualFrontier
    hsub hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualFrontierStep_of_site hanchor
      hsite)
    hconn

/-- The common-box dual cut is edge-connected from residual upper-prefix-site data. -/
theorem
    dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteResidualUpper
    (hsub : dualSupport F ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hupper :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripFrontierUpperSiteStep
        F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteResidualSite
    hsub hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualSiteStep_of_upperSite hupper)
    hconn

/-- The common-box dual cut is edge-connected from strict residual upper-prefix-site data. -/
theorem
    dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperResidualStrict
    (hsub : dualSupport F ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hstrict :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteStrictStep
        F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteResidualUpper
    hsub hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteStep_of_strict
      hstrict)
    hconn

/-- The common-box dual cut is edge-connected from ordered residual upper-prefix-site data. -/
theorem
    dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperResidualOrdered
    (hsub : dualSupport F ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hordered :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteOrderedStep
        F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperResidualStrict
    hsub hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteStrictStep_of_ordered
      hordered)
    hconn

/-- The common-box dual cut is edge-connected from residual-index ordered residual
upper-prefix-site data. -/
theorem
    dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperResidualResidual
    (hsub : dualSupport F ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hresidual :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualOrderedStep
        F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperResidualOrdered
    hsub hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteOrderedStep_of_residual
      hresidual)
    hconn

/-- The common-box dual cut is edge-connected from gap-reduced residual-index residual
upper-prefix-site data. -/
theorem
    dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperResidualResidualGap
    (hsub : dualSupport F ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hgap :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualGapStep
        F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperResidualResidual
    hsub hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualStep_of_gap
      hgap)
    hconn

/-- The common-box dual cut is edge-connected from non-strip residual-index residual
upper-prefix-site data. -/
theorem
    dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperResidualResNonStrip
    (hsub : dualSupport F ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hnonStrip :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualNonStripStep
        F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperResidualResidual
    hsub hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualStep_of_nonStrip
      hnonStrip)
    hconn

/-- Pairwise dart reachability from lower-reduced turn-chain non-strip data and connectedness of
the underlying box droplet. -/
theorem dartReachable_of_rayExitVerticalStrictBridgeFrontierLtReducedTurnChain_connected
    {S : Finset ↑Λ}
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hreduced : RayExitVerticalStrictBridgeFrontierLtReducedTurnChainStep
      (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (d e : BoundaryDart (S.image Subtype.val)) :
    DartReachable (S.image Subtype.val) d e :=
  dartReachable_of_rayExitVerticalStrictBridgeFrontierTurnChain_connected hanchor
    (rayExitVerticalStrictBridgeFrontierTurnChainStep_of_ltReducedTurnChainStep hreduced)
    hconn d e

/-- Pairwise dart reachability from lower frontier-anchor split data and connectedness of the
underlying box droplet. -/
theorem dartReachable_of_rayExitVerticalStrictBridgeFrontierLtAnchorSplit_connected
    {S : Finset ↑Λ}
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hsplit : RayExitVerticalStrictBridgeFrontierLtAnchorSplitTurnChainStep
      (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (d e : BoundaryDart (S.image Subtype.val)) :
    DartReachable (S.image Subtype.val) d e :=
  dartReachable_of_rayExitVerticalStrictBridgeFrontierLtReducedTurnChain_connected hanchor
    (rayExitVerticalStrictBridgeFrontierLtReducedTurnChainStep_of_ltAnchorSplit hsplit)
    hconn d e

/-- Pairwise dart reachability from lower frontier-site-anchor data and connectedness of the
underlying box droplet. -/
theorem dartReachable_of_rayExitVerticalStrictBridgeFrontierLtSiteAnchor_connected
    {S : Finset ↑Λ}
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hsite : RayExitVerticalStrictBridgeFrontierLtSiteAnchorTurnChainStep
      (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (d e : BoundaryDart (S.image Subtype.val)) :
    DartReachable (S.image Subtype.val) d e :=
  dartReachable_of_rayExitVerticalStrictBridgeFrontierChain_connected hanchor
    (rayExitVerticalStrictBridgeFrontierChainStep_of_ltSiteAnchorTurnChainStep hanchor hsite)
    hconn d e

/-- Pairwise dart reachability from lower upper-prefix site-anchor data and connectedness of the
underlying box droplet. -/
theorem dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchor_connected
    {S : Finset ↑Λ}
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hupper : RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorTurnChainStep
      (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (d e : BoundaryDart (S.image Subtype.val)) :
    DartReachable (S.image Subtype.val) d e :=
  dartReachable_of_rayExitVerticalStrictBridgeFrontierLtSiteAnchor_connected hanchor
    (rayExitVerticalStrictBridgeFrontierLtSiteAnchorTurnChainStep_of_ltUpperSiteAnchor hupper)
    hconn d e

/-- Pairwise dart reachability from lower upper-prefix reachable data and connectedness of the
underlying box droplet. -/
theorem dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteReachable_connected
    {S : Finset ↑Λ}
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hreach : RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep
      (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (d e : BoundaryDart (S.image Subtype.val)) :
    DartReachable (S.image Subtype.val) d e :=
  dartReachable_of_rayExitVerticalStrictBridgeFrontierChain_connected hanchor
    (rayExitVerticalStrictBridgeFrontierChainStep_of_ltUpperSiteAnchorReachableStep
      hanchor hreach)
    hconn d e

/-- Pairwise dart reachability from lower upper-prefix strict reachable data and connectedness of
the underlying box droplet. -/
theorem dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteStrict_connected
    {S : Finset ↑Λ}
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hstrict : RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorStrictReachableStep
      (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (d e : BoundaryDart (S.image Subtype.val)) :
    DartReachable (S.image Subtype.val) d e :=
  dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteReachable_connected hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep_of_strictReachable
      hstrict)
    hconn d e

/-- Pairwise dart reachability from lower upper-prefix ordered reachable data and connectedness of
the underlying box droplet. -/
theorem dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteOrdered_connected
    {S : Finset ↑Λ}
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hordered : RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorOrderedReachableStep
      (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (d e : BoundaryDart (S.image Subtype.val)) :
    DartReachable (S.image Subtype.val) d e :=
  dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteStrict_connected hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorStrictReachableStep_of_ordered
      hordered)
    hconn d e

/-- Pairwise dart reachability from residual-index lower upper-prefix ordered reachable data and
connectedness of the underlying box droplet. -/
theorem dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteResidual_connected
    {S : Finset ↑Λ}
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hresidual : RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualOrderedReachableStep
      (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (d e : BoundaryDart (S.image Subtype.val)) :
    DartReachable (S.image Subtype.val) d e :=
  dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteOrdered_connected hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorOrderedReachableStep_of_residual
      hresidual)
    hconn d e

/-- Pairwise dart reachability from gap-reduced residual-index lower upper-prefix reachable data
and connectedness of the underlying box droplet. -/
theorem dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteResidualGap_connected
    {S : Finset ↑Λ}
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hgapReach :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualGapReachableStep
        (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (d e : BoundaryDart (S.image Subtype.val)) :
    DartReachable (S.image Subtype.val) d e :=
  dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteResidual_connected hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualOrderedReachableStep_of_gap
      hgapReach)
    hconn d e

/-- Pairwise dart reachability from non-strip residual-index lower upper-prefix reachable data and
connectedness of the underlying box droplet. -/
theorem dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteResidualNonStrip_connected
    {S : Finset ↑Λ}
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hnonStrip :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripReachableStep
        (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (d e : BoundaryDart (S.image Subtype.val)) :
    DartReachable (S.image Subtype.val) d e :=
  dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteResidualGap_connected hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualGapReachableStep_of_nonStrip
      hnonStrip)
    hconn d e

/-- Pairwise dart reachability from residual bridge data and connectedness of the underlying box
droplet. -/
theorem dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteResidualBridge_connected
    {S : Finset ↑Λ}
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hbridge :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripBridgeReachableStep
        (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (d e : BoundaryDart (S.image Subtype.val)) :
    DartReachable (S.image Subtype.val) d e :=
  dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteResidualNonStrip_connected
    hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripReachableStep_of_bridge
      hbridge)
    hconn d e

/-- Pairwise dart reachability from residual frontier data and connectedness of the underlying
box droplet. -/
theorem dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteResidualFrontier_connected
    {S : Finset ↑Λ}
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hfrontier :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripFrontierReachableStep
        (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (d e : BoundaryDart (S.image Subtype.val)) :
    DartReachable (S.image Subtype.val) d e :=
  dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteResidualBridge_connected
    hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualBridgeReachableStep_of_frontier
      hfrontier)
    hconn d e

/-- Pairwise dart reachability from residual site-anchor data and connectedness of the underlying
box droplet. -/
theorem dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteResidualSite_connected
    {S : Finset ↑Λ}
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hsite :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripFrontierSiteStep
        (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (d e : BoundaryDart (S.image Subtype.val)) :
    DartReachable (S.image Subtype.val) d e :=
  dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteResidualFrontier_connected
    hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualFrontierStep_of_site hanchor
      hsite)
    hconn d e

/-- Pairwise dart reachability from residual upper-prefix-site data and connectedness of the
underlying box droplet. -/
theorem
    dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteResidualUpper_connected
    {S : Finset ↑Λ}
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hupper :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripFrontierUpperSiteStep
        (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (d e : BoundaryDart (S.image Subtype.val)) :
    DartReachable (S.image Subtype.val) d e :=
  dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteResidualSite_connected
    hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualSiteStep_of_upperSite hupper)
    hconn d e

/-- Pairwise dart reachability from strict residual upper-prefix-site data and connectedness of
the underlying box droplet. -/
theorem
    dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteResidualUpperStrict_connected
    {S : Finset ↑Λ}
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hstrict :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteStrictStep
        (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (d e : BoundaryDart (S.image Subtype.val)) :
    DartReachable (S.image Subtype.val) d e :=
  dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteResidualUpper_connected
    hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteStep_of_strict
      hstrict)
    hconn d e

/-- Pairwise dart reachability from ordered residual upper-prefix-site data and connectedness of
the underlying box droplet. -/
theorem
    dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteResidualUpperOrdered_connected
    {S : Finset ↑Λ}
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hordered :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteOrderedStep
        (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (d e : BoundaryDart (S.image Subtype.val)) :
    DartReachable (S.image Subtype.val) d e :=
  dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteResidualUpperStrict_connected
    hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteStrictStep_of_ordered
      hordered)
    hconn d e

/-- Pairwise dart reachability from residual-index ordered residual upper-prefix-site data and
connectedness of the underlying box droplet. -/
theorem
    dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteResidualUpperResidual_connected
    {S : Finset ↑Λ}
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hresidual :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualOrderedStep
        (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (d e : BoundaryDart (S.image Subtype.val)) :
    DartReachable (S.image Subtype.val) d e :=
  dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteResidualUpperOrdered_connected
    hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteOrderedStep_of_residual
      hresidual)
    hconn d e

/-- Pairwise dart reachability from gap-reduced residual-index residual upper-prefix-site data and
connectedness of the underlying box droplet. -/
theorem
    dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteResidualUpperGap_connected
    {S : Finset ↑Λ}
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hgap :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualGapStep
        (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (d e : BoundaryDart (S.image Subtype.val)) :
    DartReachable (S.image Subtype.val) d e :=
  dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteResidualUpperResidual_connected
    hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualStep_of_gap
      hgap)
    hconn d e

/-- Pairwise dart reachability from non-strip residual-index residual upper-prefix-site data and
connectedness of the underlying box droplet. -/
theorem
    dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteResidualUpperNonStrip_connected
    {S : Finset ↑Λ}
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hnonStrip :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualNonStripStep
        (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (d e : BoundaryDart (S.image Subtype.val)) :
    DartReachable (S.image Subtype.val) d e :=
  dartReachable_of_rayExitVerticalStrictBridgeFrontierLtUpperSiteResidualUpperResidual_connected
    hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualStep_of_nonStrip
      hnonStrip)
    hconn d e

/-- The common-box dual cut is edge-connected from lower-reduced turn-chain non-strip data and
connectedness of the underlying box droplet. -/
theorem dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtReduced_connected
    {S : Finset ↑Λ}
    (hsub : dualSupport (S.image Subtype.val) ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hreduced : RayExitVerticalStrictBridgeFrontierLtReducedTurnChainStep
      (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierTurnChain_connected hsub
    hanchor
    (rayExitVerticalStrictBridgeFrontierTurnChainStep_of_ltReducedTurnChainStep hreduced)
    hconn

/-- The common-box dual cut is edge-connected from lower frontier-anchor split data and
connectedness of the underlying box droplet. -/
theorem dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtAnchorSplit_connected
    {S : Finset ↑Λ}
    (hsub : dualSupport (S.image Subtype.val) ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hsplit : RayExitVerticalStrictBridgeFrontierLtAnchorSplitTurnChainStep
      (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtReduced_connected
    hsub hanchor
    (rayExitVerticalStrictBridgeFrontierLtReducedTurnChainStep_of_ltAnchorSplit hsplit)
    hconn

/-- The common-box dual cut is edge-connected from lower frontier-site-anchor data and
connectedness of the underlying box droplet. -/
theorem dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtSiteAnchor_connected
    {S : Finset ↑Λ}
    (hsub : dualSupport (S.image Subtype.val) ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hsite : RayExitVerticalStrictBridgeFrontierLtSiteAnchorTurnChainStep
      (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierChain_connected hsub hanchor
    (rayExitVerticalStrictBridgeFrontierChainStep_of_ltSiteAnchorTurnChainStep hanchor hsite)
    hconn

/-- The common-box dual cut is edge-connected from lower upper-prefix site-anchor data and
connectedness of the underlying box droplet. -/
theorem dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperSite_connected
    {S : Finset ↑Λ}
    (hsub : dualSupport (S.image Subtype.val) ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hupper : RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorTurnChainStep
      (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtSiteAnchor_connected
    hsub hanchor
    (rayExitVerticalStrictBridgeFrontierLtSiteAnchorTurnChainStep_of_ltUpperSiteAnchor hupper)
    hconn

/-- The common-box dual cut is edge-connected from lower upper-prefix reachable data and
connectedness of the underlying box droplet. -/
theorem dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperReach_connected
    {S : Finset ↑Λ}
    (hsub : dualSupport (S.image Subtype.val) ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hreach : RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep
      (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierChain_connected
    hsub hanchor
    (rayExitVerticalStrictBridgeFrontierChainStep_of_ltUpperSiteAnchorReachableStep
      hanchor hreach)
    hconn

/-- The common-box dual cut is edge-connected from lower upper-prefix strict reachable data and
connectedness of the underlying box droplet. -/
theorem dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperStrict_connected
    {S : Finset ↑Λ}
    (hsub : dualSupport (S.image Subtype.val) ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hstrict : RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorStrictReachableStep
      (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperReach_connected
    hsub hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep_of_strictReachable
      hstrict)
    hconn

/-- The common-box dual cut is edge-connected from lower upper-prefix ordered reachable data and
connectedness of the underlying box droplet. -/
theorem dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperOrdered_connected
    {S : Finset ↑Λ}
    (hsub : dualSupport (S.image Subtype.val) ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hordered : RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorOrderedReachableStep
      (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperStrict_connected
    hsub hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorStrictReachableStep_of_ordered
      hordered)
    hconn

/-- The common-box dual cut is edge-connected from residual-index lower upper-prefix ordered
reachable data and connectedness of the underlying box droplet. -/
theorem dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperResidual_connected
    {S : Finset ↑Λ}
    (hsub : dualSupport (S.image Subtype.val) ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hresidual : RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualOrderedReachableStep
      (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperOrdered_connected
    hsub hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorOrderedReachableStep_of_residual
      hresidual)
    hconn

/-- The common-box dual cut is edge-connected from gap-reduced residual-index lower upper-prefix
reachable data and connectedness of the underlying box droplet. -/
theorem
    dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperResidualGap_connected
    {S : Finset ↑Λ}
    (hsub : dualSupport (S.image Subtype.val) ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hgapReach :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualGapReachableStep
        (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperResidual_connected
    hsub hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualOrderedReachableStep_of_gap
      hgapReach)
    hconn

/-- The common-box dual cut is edge-connected from non-strip residual-index lower upper-prefix
reachable data and connectedness of the underlying box droplet. -/
theorem
    dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperNonStrip_connected
    {S : Finset ↑Λ}
    (hsub : dualSupport (S.image Subtype.val) ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hnonStrip :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripReachableStep
        (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperResidualGap_connected
    hsub hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualGapReachableStep_of_nonStrip
      hnonStrip)
    hconn

/-- The common-box dual cut is edge-connected from residual bridge data and connectedness of the
underlying box droplet. -/
theorem
    dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperBridge_connected
    {S : Finset ↑Λ}
    (hsub : dualSupport (S.image Subtype.val) ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hbridge :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripBridgeReachableStep
        (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperNonStrip_connected
    hsub hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripReachableStep_of_bridge
      hbridge)
    hconn

/-- The common-box dual cut is edge-connected from residual frontier data and connectedness of the
underlying box droplet. -/
theorem
    dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperFrontier_connected
    {S : Finset ↑Λ}
    (hsub : dualSupport (S.image Subtype.val) ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hfrontier :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripFrontierReachableStep
        (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperBridge_connected
    hsub hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualBridgeReachableStep_of_frontier
      hfrontier)
    hconn

/-- The common-box dual cut is edge-connected from residual site-anchor data and connectedness of
the underlying box droplet. -/
theorem
    dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperResidualSite_connected
    {S : Finset ↑Λ}
    (hsub : dualSupport (S.image Subtype.val) ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hsite :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripFrontierSiteStep
        (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperFrontier_connected
    hsub hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualFrontierStep_of_site hanchor
      hsite)
    hconn

/-- The common-box dual cut is edge-connected from residual upper-prefix-site data and
connectedness of the underlying box droplet. -/
theorem
dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperResidualUpper_connected
    {S : Finset ↑Λ}
    (hsub : dualSupport (S.image Subtype.val) ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hupper :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripFrontierUpperSiteStep
        (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperResidualSite_connected
    hsub hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualSiteStep_of_upperSite hupper)
    hconn

/-- The common-box dual cut is edge-connected from strict residual upper-prefix-site data and
connectedness of the underlying box droplet. -/
theorem
dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperResidualStrict_connected
    {S : Finset ↑Λ}
    (hsub : dualSupport (S.image Subtype.val) ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hstrict :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteStrictStep
        (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperResidualUpper_connected
    hsub hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteStep_of_strict
      hstrict)
    hconn

/-- The common-box dual cut is edge-connected from ordered residual upper-prefix-site data and
connectedness of the underlying box droplet. -/
theorem
dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperResidualOrd_connected
    {S : Finset ↑Λ}
    (hsub : dualSupport (S.image Subtype.val) ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hordered :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteOrderedStep
        (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperResidualStrict_connected
    hsub hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteStrictStep_of_ordered
      hordered)
    hconn

/-- The common-box dual cut is edge-connected from residual-index ordered residual
upper-prefix-site data and connectedness of the underlying box droplet. -/
theorem
dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperResidualRes_connected
    {S : Finset ↑Λ}
    (hsub : dualSupport (S.image Subtype.val) ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hresidual :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualOrderedStep
        (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperResidualOrd_connected
    hsub hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteOrderedStep_of_residual
      hresidual)
    hconn

/-- Compatibility name for the residual-index ordered residual upper-prefix-site connected
wrapper. -/
theorem
dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperResidualResidual_connected
    {S : Finset ↑Λ}
    (hsub : dualSupport (S.image Subtype.val) ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hresidual :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualOrderedStep
        (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperResidualRes_connected
    hsub hanchor hresidual hconn

/-- The common-box dual cut is edge-connected from gap-reduced residual-index residual
upper-prefix-site data and connectedness of the underlying box droplet. -/
theorem
dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperResidualResGap_connected
    {S : Finset ↑Λ}
    (hsub : dualSupport (S.image Subtype.val) ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hgap :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualGapStep
        (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperResidualRes_connected
    hsub hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualStep_of_gap
      hgap)
    hconn

/-- The common-box dual cut is edge-connected from non-strip residual-index residual
upper-prefix-site data and connectedness of the underlying box droplet. -/
theorem
dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperResidualResNS_connected
    {S : Finset ↑Λ}
    (hsub : dualSupport (S.image Subtype.val) ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hnonStrip :
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualNonStripStep
        (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierLtUpperResidualRes_connected
    hsub hanchor
    (rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualStep_of_nonStrip
      hnonStrip)
    hconn

/-- **The Peierls contour count from lower-reduced turn-chain non-strip strict ray-exit data and
connected droplets**: the lower bridge-to-frontier leg is automatic. -/
theorem peierls_contour_count_rayExit_verticalStrictBridgeFrontierLtReducedTurnChain_connected
    {i : Fin 2 → ℤ} {g : ↑Λ} {r : ℕ}
    (hpre : (Ambient.inducedGraph (latticeGraph 2) Λ).Preconnected)
    (D : Finset (Finset ↑Λ))
    (hdual : ∀ S ∈ D, dualSupport (S.image Subtype.val) ⊆ Λd)
    (hi : ∀ S ∈ D, i ∈ S.image Subtype.val)
    (hne : ∀ S ∈ D, NeighbourClosed Λ S)
    (hg : ∀ S ∈ D, g ∉ S)
    (hdata : ∀ S (_ : S ∈ D),
      (∀ d : BoundaryDart (S.image Subtype.val),
        DartReachable (S.image Subtype.val) d
          (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩)) ∧
      RayExitVerticalStrictBridgeFrontierLtReducedTurnChainStep (S.image Subtype.val) ∧
      IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (hr : ∀ S ∈ D, (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) S).card = r) :
    D.card ≤ r * (2 * 2) ^ (2 * r) :=
  peierls_contour_count_rayExit_verticalStrictBridgeFrontierTurnChain_connected hpre D
    hdual hi hne hg
    (fun S hS =>
      ⟨(hdata S hS).1,
        rayExitVerticalStrictBridgeFrontierTurnChainStep_of_ltReducedTurnChainStep
          (hdata S hS).2.1,
        (hdata S hS).2.2⟩)
    hr

/-- **The Peierls contour count from lower frontier-anchor split non-strip strict ray-exit data and
connected droplets**: the lower bridge-to-frontier leg is automatic and the remaining lower
frontier-anchor leg is split through the frontier site's ray-exit anchor. -/
theorem peierls_contour_count_rayExit_verticalStrictBridgeFrontierLtAnchorSplit_connected
    {i : Fin 2 → ℤ} {g : ↑Λ} {r : ℕ}
    (hpre : (Ambient.inducedGraph (latticeGraph 2) Λ).Preconnected)
    (D : Finset (Finset ↑Λ))
    (hdual : ∀ S ∈ D, dualSupport (S.image Subtype.val) ⊆ Λd)
    (hi : ∀ S ∈ D, i ∈ S.image Subtype.val)
    (hne : ∀ S ∈ D, NeighbourClosed Λ S)
    (hg : ∀ S ∈ D, g ∉ S)
    (hdata : ∀ S (_ : S ∈ D),
      (∀ d : BoundaryDart (S.image Subtype.val),
        DartReachable (S.image Subtype.val) d
          (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩)) ∧
      RayExitVerticalStrictBridgeFrontierLtAnchorSplitTurnChainStep (S.image Subtype.val) ∧
      IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (hr : ∀ S ∈ D, (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) S).card = r) :
    D.card ≤ r * (2 * 2) ^ (2 * r) :=
  peierls_contour_count_rayExit_verticalStrictBridgeFrontierLtReducedTurnChain_connected
    hpre D hdual hi hne hg
    (fun S hS =>
      ⟨(hdata S hS).1,
        rayExitVerticalStrictBridgeFrontierLtReducedTurnChainStep_of_ltAnchorSplit
          (hdata S hS).2.1,
        (hdata S hS).2.2⟩)
    hr

/-- **The Peierls contour count from lower frontier-site-anchor non-strip strict ray-exit data and
connected droplets**: the lower bridge-to-frontier leg is automatic and the frontier-dart to
frontier-site-anchor leg is supplied by the existing anchoring hypothesis, so the remaining lower
local turn input starts at the frontier site's ray-exit anchor. -/
theorem peierls_contour_count_rayExit_verticalStrictBridgeFrontierLtSiteAnchor_connected
    {i : Fin 2 → ℤ} {g : ↑Λ} {r : ℕ}
    (hpre : (Ambient.inducedGraph (latticeGraph 2) Λ).Preconnected)
    (D : Finset (Finset ↑Λ))
    (hdual : ∀ S ∈ D, dualSupport (S.image Subtype.val) ⊆ Λd)
    (hi : ∀ S ∈ D, i ∈ S.image Subtype.val)
    (hne : ∀ S ∈ D, NeighbourClosed Λ S)
    (hg : ∀ S ∈ D, g ∉ S)
    (hdata : ∀ S (_ : S ∈ D),
      (∀ d : BoundaryDart (S.image Subtype.val),
        DartReachable (S.image Subtype.val) d
          (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩)) ∧
      RayExitVerticalStrictBridgeFrontierLtSiteAnchorTurnChainStep
        (S.image Subtype.val) ∧
      IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (hr : ∀ S ∈ D, (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) S).card = r) :
    D.card ≤ r * (2 * 2) ^ (2 * r) :=
  peierls_contour_count_rayExit_verticalStrictBridgeFrontierChain_connected hpre D
    hdual hi hne hg
    (fun S hS =>
      ⟨(hdata S hS).1,
        rayExitVerticalStrictBridgeFrontierChainStep_of_ltSiteAnchorTurnChainStep
          (hdata S hS).1 (hdata S hS).2.1,
        (hdata S hS).2.2⟩)
    hr

/-- **The Peierls contour count from lower upper-prefix site-anchor non-strip strict ray-exit data
and connected droplets**: the lower site-anchor leg is split through the upper ray point at the
first lower frontier index, whose anchor is identified with the original upper site's anchor by
ray-prefix stability. -/
theorem peierls_contour_count_rayExit_verticalStrictBridgeFrontierLtUpperSiteAnchor_connected
    {i : Fin 2 → ℤ} {g : ↑Λ} {r : ℕ}
    (hpre : (Ambient.inducedGraph (latticeGraph 2) Λ).Preconnected)
    (D : Finset (Finset ↑Λ))
    (hdual : ∀ S ∈ D, dualSupport (S.image Subtype.val) ⊆ Λd)
    (hi : ∀ S ∈ D, i ∈ S.image Subtype.val)
    (hne : ∀ S ∈ D, NeighbourClosed Λ S)
    (hg : ∀ S ∈ D, g ∉ S)
    (hdata : ∀ S (_ : S ∈ D),
      (∀ d : BoundaryDart (S.image Subtype.val),
        DartReachable (S.image Subtype.val) d
          (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩)) ∧
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorTurnChainStep
        (S.image Subtype.val) ∧
      IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (hr : ∀ S ∈ D, (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) S).card = r) :
    D.card ≤ r * (2 * 2) ^ (2 * r) :=
  peierls_contour_count_rayExit_verticalStrictBridgeFrontierLtSiteAnchor_connected
    hpre D hdual hi hne hg
    (fun S hS =>
      ⟨(hdata S hS).1,
        rayExitVerticalStrictBridgeFrontierLtSiteAnchorTurnChainStep_of_ltUpperSiteAnchor
          (hdata S hS).2.1,
        (hdata S hS).2.2⟩)
    hr

/-- **The Peierls contour count from lower upper-prefix reachable non-strip strict ray-exit data
and connected droplets**: the lower site-anchor leg is only required as `DartReachable` through
the upper-prefix site. -/
theorem peierls_contour_count_rayExit_verticalStrictBridgeFrontierLtUpperReach_connected
    {i : Fin 2 → ℤ} {g : ↑Λ} {r : ℕ}
    (hpre : (Ambient.inducedGraph (latticeGraph 2) Λ).Preconnected)
    (D : Finset (Finset ↑Λ))
    (hdual : ∀ S ∈ D, dualSupport (S.image Subtype.val) ⊆ Λd)
    (hi : ∀ S ∈ D, i ∈ S.image Subtype.val)
    (hne : ∀ S ∈ D, NeighbourClosed Λ S)
    (hg : ∀ S ∈ D, g ∉ S)
    (hdata : ∀ S (_ : S ∈ D),
      (∀ d : BoundaryDart (S.image Subtype.val),
        DartReachable (S.image Subtype.val) d
          (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩)) ∧
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep
        (S.image Subtype.val) ∧
      IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (hr : ∀ S ∈ D, (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) S).card = r) :
    D.card ≤ r * (2 * 2) ^ (2 * r) :=
  peierls_contour_count_rayExit_verticalStrictBridgeFrontierChain_connected
    hpre D hdual hi hne hg
    (fun S hS =>
      ⟨(hdata S hS).1,
        rayExitVerticalStrictBridgeFrontierChainStep_of_ltUpperSiteAnchorReachableStep
          (hdata S hS).1 (hdata S hS).2.1,
        (hdata S hS).2.2⟩)
    hr

/-- **The Peierls contour count from lower upper-prefix strict reachable non-strip strict ray-exit
data and connected droplets**: equal ray-exit indices of the frontier and upper-prefix sites are
automatic by shared vertices; only the unequal-index subcase remains as lower local input. -/
theorem peierls_contour_count_rayExit_verticalStrictBridgeFrontierLtUpperStrict_connected
    {i : Fin 2 → ℤ} {g : ↑Λ} {r : ℕ}
    (hpre : (Ambient.inducedGraph (latticeGraph 2) Λ).Preconnected)
    (D : Finset (Finset ↑Λ))
    (hdual : ∀ S ∈ D, dualSupport (S.image Subtype.val) ⊆ Λd)
    (hi : ∀ S ∈ D, i ∈ S.image Subtype.val)
    (hne : ∀ S ∈ D, NeighbourClosed Λ S)
    (hg : ∀ S ∈ D, g ∉ S)
    (hdata : ∀ S (_ : S ∈ D),
      (∀ d : BoundaryDart (S.image Subtype.val),
        DartReachable (S.image Subtype.val) d
          (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩)) ∧
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorStrictReachableStep
        (S.image Subtype.val) ∧
      IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (hr : ∀ S ∈ D, (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) S).card = r) :
    D.card ≤ r * (2 * 2) ^ (2 * r) :=
  peierls_contour_count_rayExit_verticalStrictBridgeFrontierLtUpperReach_connected
    hpre D hdual hi hne hg
    (fun S hS =>
      ⟨(hdata S hS).1,
        rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorReachableStep_of_strictReachable
          (hdata S hS).2.1,
        (hdata S hS).2.2⟩)
    hr

/-- **The Peierls contour count from lower upper-prefix ordered reachable non-strip strict ray-exit
data and connected droplets**: after the equal-index subcase is automatic, the remaining lower
site-anchor leg is split by the local ray-exit index order. -/
theorem peierls_contour_count_rayExit_verticalStrictBridgeFrontierLtUpperOrdered_connected
    {i : Fin 2 → ℤ} {g : ↑Λ} {r : ℕ}
    (hpre : (Ambient.inducedGraph (latticeGraph 2) Λ).Preconnected)
    (D : Finset (Finset ↑Λ))
    (hdual : ∀ S ∈ D, dualSupport (S.image Subtype.val) ⊆ Λd)
    (hi : ∀ S ∈ D, i ∈ S.image Subtype.val)
    (hne : ∀ S ∈ D, NeighbourClosed Λ S)
    (hg : ∀ S ∈ D, g ∉ S)
    (hdata : ∀ S (_ : S ∈ D),
      (∀ d : BoundaryDart (S.image Subtype.val),
        DartReachable (S.image Subtype.val) d
          (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩)) ∧
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorOrderedReachableStep
        (S.image Subtype.val) ∧
      IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (hr : ∀ S ∈ D, (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) S).card = r) :
    D.card ≤ r * (2 * 2) ^ (2 * r) :=
  peierls_contour_count_rayExit_verticalStrictBridgeFrontierLtUpperStrict_connected
    hpre D hdual hi hne hg
    (fun S hS =>
      ⟨(hdata S hS).1,
        rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorStrictReachableStep_of_ordered
          (hdata S hS).2.1,
        (hdata S hS).2.2⟩)
    hr

/-- **The Peierls contour count from residual-index lower upper-prefix ordered reachable non-strip
strict ray-exit data and connected droplets**: the remaining lower ordered comparison is written
against the residual upper ray length after the lower frontier index. -/
theorem peierls_contour_count_rayExit_verticalStrictBridgeFrontierLtUpperResidual_connected
    {i : Fin 2 → ℤ} {g : ↑Λ} {r : ℕ}
    (hpre : (Ambient.inducedGraph (latticeGraph 2) Λ).Preconnected)
    (D : Finset (Finset ↑Λ))
    (hdual : ∀ S ∈ D, dualSupport (S.image Subtype.val) ⊆ Λd)
    (hi : ∀ S ∈ D, i ∈ S.image Subtype.val)
    (hne : ∀ S ∈ D, NeighbourClosed Λ S)
    (hg : ∀ S ∈ D, g ∉ S)
    (hdata : ∀ S (_ : S ∈ D),
      (∀ d : BoundaryDart (S.image Subtype.val),
        DartReachable (S.image Subtype.val) d
          (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩)) ∧
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualOrderedReachableStep
        (S.image Subtype.val) ∧
      IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (hr : ∀ S ∈ D, (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) S).card = r) :
    D.card ≤ r * (2 * 2) ^ (2 * r) :=
  peierls_contour_count_rayExit_verticalStrictBridgeFrontierLtUpperOrdered_connected
    hpre D hdual hi hne hg
    (fun S hS =>
      ⟨(hdata S hS).1,
        rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorOrderedReachableStep_of_residual
          (hdata S hS).2.1,
        (hdata S hS).2.2⟩)
    hr

/-- **The Peierls contour count from gap-reduced residual-index lower upper-prefix non-strip
strict ray-exit data and connected droplets**: adjacent residual comparisons are automatic by
the existing vertical bridge shared-vertex geometry. -/
theorem peierls_contour_count_rayExit_verticalStrictBridgeFrontierLtUpperResidualGap_connected
    {i : Fin 2 → ℤ} {g : ↑Λ} {r : ℕ}
    (hpre : (Ambient.inducedGraph (latticeGraph 2) Λ).Preconnected)
    (D : Finset (Finset ↑Λ))
    (hdual : ∀ S ∈ D, dualSupport (S.image Subtype.val) ⊆ Λd)
    (hi : ∀ S ∈ D, i ∈ S.image Subtype.val)
    (hne : ∀ S ∈ D, NeighbourClosed Λ S)
    (hg : ∀ S ∈ D, g ∉ S)
    (hdata : ∀ S (_ : S ∈ D),
      (∀ d : BoundaryDart (S.image Subtype.val),
        DartReachable (S.image Subtype.val) d
          (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩)) ∧
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualGapReachableStep
        (S.image Subtype.val) ∧
      IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (hr : ∀ S ∈ D, (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) S).card = r) :
    D.card ≤ r * (2 * 2) ^ (2 * r) :=
  peierls_contour_count_rayExit_verticalStrictBridgeFrontierLtUpperResidual_connected
    hpre D hdual hi hne hg
    (fun S hS =>
      ⟨(hdata S hS).1,
        rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualOrderedReachableStep_of_gap
          (hdata S hS).2.1,
        (hdata S hS).2.2⟩)
    hr

/-- **The Peierls contour count from non-strip residual-index lower upper-prefix non-strip strict
ray-exit data and connected droplets**: adjacent and straight-strip residual comparisons are
automatic, so the lower input starts only at non-strip residual gaps. -/
theorem
    peierls_contour_count_rayExit_verticalStrictBridgeFrontierLtUpperResidualNonStrip_connected
    {i : Fin 2 → ℤ} {g : ↑Λ} {r : ℕ}
    (hpre : (Ambient.inducedGraph (latticeGraph 2) Λ).Preconnected)
    (D : Finset (Finset ↑Λ))
    (hdual : ∀ S ∈ D, dualSupport (S.image Subtype.val) ⊆ Λd)
    (hi : ∀ S ∈ D, i ∈ S.image Subtype.val)
    (hne : ∀ S ∈ D, NeighbourClosed Λ S)
    (hg : ∀ S ∈ D, g ∉ S)
    (hdata : ∀ S (_ : S ∈ D),
      (∀ d : BoundaryDart (S.image Subtype.val),
        DartReachable (S.image Subtype.val) d
          (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩)) ∧
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripReachableStep
        (S.image Subtype.val) ∧
      IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (hr : ∀ S ∈ D, (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) S).card = r) :
    D.card ≤ r * (2 * 2) ^ (2 * r) :=
  peierls_contour_count_rayExit_verticalStrictBridgeFrontierLtUpperResidualGap_connected
    hpre D hdual hi hne hg
    (fun S hS =>
      ⟨(hdata S hS).1,
        rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualGapReachableStep_of_nonStrip
          (hdata S hS).2.1,
        (hdata S hS).2.2⟩)
    hr

/-- **The Peierls contour count from residual bridge lower upper-prefix non-strip strict
ray-exit data and connected droplets**: the endpoint anchor-to-bridge steps for the local residual
pair are automatic, so the lower input starts at the local residual bridge. -/
theorem
    peierls_contour_count_rayExit_verticalStrictBridgeFrontierLtUpperResidualBridge_connected
    {i : Fin 2 → ℤ} {g : ↑Λ} {r : ℕ}
    (hpre : (Ambient.inducedGraph (latticeGraph 2) Λ).Preconnected)
    (D : Finset (Finset ↑Λ))
    (hdual : ∀ S ∈ D, dualSupport (S.image Subtype.val) ⊆ Λd)
    (hi : ∀ S ∈ D, i ∈ S.image Subtype.val)
    (hne : ∀ S ∈ D, NeighbourClosed Λ S)
    (hg : ∀ S ∈ D, g ∉ S)
    (hdata : ∀ S (_ : S ∈ D),
      (∀ d : BoundaryDart (S.image Subtype.val),
        DartReachable (S.image Subtype.val) d
          (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩)) ∧
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripBridgeReachableStep
        (S.image Subtype.val) ∧
      IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (hr : ∀ S ∈ D, (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) S).card = r) :
    D.card ≤ r * (2 * 2) ^ (2 * r) :=
  peierls_contour_count_rayExit_verticalStrictBridgeFrontierLtUpperResidualNonStrip_connected
    hpre D hdual hi hne hg
    (fun S hS =>
      ⟨(hdata S hS).1,
        rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripReachableStep_of_bridge
          (hdata S hS).2.1,
        (hdata S hS).2.2⟩)
    hr

/-- **The Peierls contour count from residual frontier lower upper-prefix non-strip strict
ray-exit data and connected droplets**: the local residual bridge input is split through the
first residual re-entry frontier dart. -/
theorem
    peierls_contour_count_rayExit_verticalStrictBridgeFrontierLtUpperResidualFrontier_connected
    {i : Fin 2 → ℤ} {g : ↑Λ} {r : ℕ}
    (hpre : (Ambient.inducedGraph (latticeGraph 2) Λ).Preconnected)
    (D : Finset (Finset ↑Λ))
    (hdual : ∀ S ∈ D, dualSupport (S.image Subtype.val) ⊆ Λd)
    (hi : ∀ S ∈ D, i ∈ S.image Subtype.val)
    (hne : ∀ S ∈ D, NeighbourClosed Λ S)
    (hg : ∀ S ∈ D, g ∉ S)
    (hdata : ∀ S (_ : S ∈ D),
      (∀ d : BoundaryDart (S.image Subtype.val),
        DartReachable (S.image Subtype.val) d
          (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩)) ∧
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripFrontierReachableStep
        (S.image Subtype.val) ∧
      IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (hr : ∀ S ∈ D, (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) S).card = r) :
    D.card ≤ r * (2 * 2) ^ (2 * r) :=
  peierls_contour_count_rayExit_verticalStrictBridgeFrontierLtUpperResidualBridge_connected
    hpre D hdual hi hne hg
    (fun S hS =>
      ⟨(hdata S hS).1,
        rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualBridgeReachableStep_of_frontier
          (hdata S hS).2.1,
        (hdata S hS).2.2⟩)
    hr

/-- **The Peierls contour count from residual site-anchor lower upper-prefix non-strip strict
ray-exit data and connected droplets**: the lower post-frontier residual leg is split through the
residual frontier-site anchor, with the frontier dart to that anchor supplied by the existing
anchoring input. -/
theorem
    peierls_contour_count_rayExit_verticalStrictBridgeFrontierLtUpperResidualSite_connected
    {i : Fin 2 → ℤ} {g : ↑Λ} {r : ℕ}
    (hpre : (Ambient.inducedGraph (latticeGraph 2) Λ).Preconnected)
    (D : Finset (Finset ↑Λ))
    (hdual : ∀ S ∈ D, dualSupport (S.image Subtype.val) ⊆ Λd)
    (hi : ∀ S ∈ D, i ∈ S.image Subtype.val)
    (hne : ∀ S ∈ D, NeighbourClosed Λ S)
    (hg : ∀ S ∈ D, g ∉ S)
    (hdata : ∀ S (_ : S ∈ D),
      (∀ d : BoundaryDart (S.image Subtype.val),
        DartReachable (S.image Subtype.val) d
          (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩)) ∧
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripFrontierSiteStep
        (S.image Subtype.val) ∧
      IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (hr : ∀ S ∈ D, (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) S).card = r) :
    D.card ≤ r * (2 * 2) ^ (2 * r) :=
  peierls_contour_count_rayExit_verticalStrictBridgeFrontierLtUpperResidualFrontier_connected
    hpre D hdual hi hne hg
    (fun S hS =>
      ⟨(hdata S hS).1,
        rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualFrontierStep_of_site
          (hdata S hS).1 (hdata S hS).2.1,
        (hdata S hS).2.2⟩)
    hr

/-- **The Peierls contour count from residual upper-prefix-site lower upper-prefix non-strip
strict ray-exit data and connected droplets**: the remaining lower residual post-frontier leg ends
at the residual upper-prefix site's ray-exit anchor, which is identified with the original
residual upper anchor by prefix stability. -/
theorem
    peierls_contour_count_rayExit_verticalStrictBridgeFrontierLtUpperResidualUpper_connected
    {i : Fin 2 → ℤ} {g : ↑Λ} {r : ℕ}
    (hpre : (Ambient.inducedGraph (latticeGraph 2) Λ).Preconnected)
    (D : Finset (Finset ↑Λ))
    (hdual : ∀ S ∈ D, dualSupport (S.image Subtype.val) ⊆ Λd)
    (hi : ∀ S ∈ D, i ∈ S.image Subtype.val)
    (hne : ∀ S ∈ D, NeighbourClosed Λ S)
    (hg : ∀ S ∈ D, g ∉ S)
    (hdata : ∀ S (_ : S ∈ D),
      (∀ d : BoundaryDart (S.image Subtype.val),
        DartReachable (S.image Subtype.val) d
          (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩)) ∧
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualNonStripFrontierUpperSiteStep
        (S.image Subtype.val) ∧
      IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (hr : ∀ S ∈ D, (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) S).card = r) :
    D.card ≤ r * (2 * 2) ^ (2 * r) :=
  peierls_contour_count_rayExit_verticalStrictBridgeFrontierLtUpperResidualSite_connected
    hpre D hdual hi hne hg
    (fun S hS =>
      ⟨(hdata S hS).1,
        rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualSiteStep_of_upperSite
          (hdata S hS).2.1,
        (hdata S hS).2.2⟩)
    hr

/-- **The Peierls contour count from strict residual upper-prefix-site lower upper-prefix
non-strip strict ray-exit data and connected droplets**: the equal-index subcase of the remaining
lower residual upper-prefix-site leg is automatic by shared-vertex geometry. -/
theorem
    peierls_contour_count_rayExit_verticalStrictBridgeFrontierLtUpperResidualUpperStrict_connected
    {i : Fin 2 → ℤ} {g : ↑Λ} {r : ℕ}
    (hpre : (Ambient.inducedGraph (latticeGraph 2) Λ).Preconnected)
    (D : Finset (Finset ↑Λ))
    (hdual : ∀ S ∈ D, dualSupport (S.image Subtype.val) ⊆ Λd)
    (hi : ∀ S ∈ D, i ∈ S.image Subtype.val)
    (hne : ∀ S ∈ D, NeighbourClosed Λ S)
    (hg : ∀ S ∈ D, g ∉ S)
    (hdata : ∀ S (_ : S ∈ D),
      (∀ d : BoundaryDart (S.image Subtype.val),
        DartReachable (S.image Subtype.val) d
          (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩)) ∧
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteStrictStep
        (S.image Subtype.val) ∧
      IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (hr : ∀ S ∈ D, (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) S).card = r) :
    D.card ≤ r * (2 * 2) ^ (2 * r) :=
  peierls_contour_count_rayExit_verticalStrictBridgeFrontierLtUpperResidualUpper_connected
    hpre D hdual hi hne hg
    (fun S hS =>
      ⟨(hdata S hS).1,
        rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteStep_of_strict
          (hdata S hS).2.1,
        (hdata S hS).2.2⟩)
    hr

/-- **The Peierls contour count from ordered residual upper-prefix-site lower upper-prefix
non-strip strict ray-exit data and connected droplets**: the remaining strict lower residual
upper-prefix-site leg is split by local residual ray-exit index order. -/
theorem
    peierls_contour_count_rayExit_verticalStrictBridgeFrontierLtUpperResidualUpperOrdered_connected
    {i : Fin 2 → ℤ} {g : ↑Λ} {r : ℕ}
    (hpre : (Ambient.inducedGraph (latticeGraph 2) Λ).Preconnected)
    (D : Finset (Finset ↑Λ))
    (hdual : ∀ S ∈ D, dualSupport (S.image Subtype.val) ⊆ Λd)
    (hi : ∀ S ∈ D, i ∈ S.image Subtype.val)
    (hne : ∀ S ∈ D, NeighbourClosed Λ S)
    (hg : ∀ S ∈ D, g ∉ S)
    (hdata : ∀ S (_ : S ∈ D),
      (∀ d : BoundaryDart (S.image Subtype.val),
        DartReachable (S.image Subtype.val) d
          (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩)) ∧
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteOrderedStep
        (S.image Subtype.val) ∧
      IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (hr : ∀ S ∈ D, (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) S).card = r) :
    D.card ≤ r * (2 * 2) ^ (2 * r) :=
  peierls_contour_count_rayExit_verticalStrictBridgeFrontierLtUpperResidualUpperStrict_connected
    hpre D hdual hi hne hg
    (fun S hS =>
      ⟨(hdata S hS).1,
        rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteStrictStep_of_ordered
          (hdata S hS).2.1,
        (hdata S hS).2.2⟩)
    hr

/-- **The Peierls contour count from residual-index ordered residual upper-prefix-site lower
upper-prefix non-strip strict ray-exit data and connected droplets**: the local upper-prefix
site index in the remaining ordered leg is rewritten as a residual upper ray length. -/
theorem
    peierls_contour_count_rayExit_verticalStrictBridgeFrontierLtUpperResidualUpperResidual_connected
    {i : Fin 2 → ℤ} {g : ↑Λ} {r : ℕ}
    (hpre : (Ambient.inducedGraph (latticeGraph 2) Λ).Preconnected)
    (D : Finset (Finset ↑Λ))
    (hdual : ∀ S ∈ D, dualSupport (S.image Subtype.val) ⊆ Λd)
    (hi : ∀ S ∈ D, i ∈ S.image Subtype.val)
    (hne : ∀ S ∈ D, NeighbourClosed Λ S)
    (hg : ∀ S ∈ D, g ∉ S)
    (hdata : ∀ S (_ : S ∈ D),
      (∀ d : BoundaryDart (S.image Subtype.val),
        DartReachable (S.image Subtype.val) d
          (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩)) ∧
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualOrderedStep
        (S.image Subtype.val) ∧
      IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (hr : ∀ S ∈ D, (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) S).card = r) :
    D.card ≤ r * (2 * 2) ^ (2 * r) :=
  peierls_contour_count_rayExit_verticalStrictBridgeFrontierLtUpperResidualUpperOrdered_connected
    hpre D hdual hi hne hg
    (fun S hS =>
      ⟨(hdata S hS).1,
        rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteOrderedStep_of_residual
          (hdata S hS).2.1,
        (hdata S hS).2.2⟩)
    hr

/-- **The Peierls contour count from gap-reduced residual-index residual upper-prefix-site lower
upper-prefix non-strip strict ray-exit data and connected droplets**: adjacent local residual
comparisons are automatic by the existing vertical bridge shared-vertex geometry. -/
theorem
    peierls_contour_count_rayExit_verticalStrictBridgeFrontierLtUpperResidualUpperResGap_connected
    {i : Fin 2 → ℤ} {g : ↑Λ} {r : ℕ}
    (hpre : (Ambient.inducedGraph (latticeGraph 2) Λ).Preconnected)
    (D : Finset (Finset ↑Λ))
    (hdual : ∀ S ∈ D, dualSupport (S.image Subtype.val) ⊆ Λd)
    (hi : ∀ S ∈ D, i ∈ S.image Subtype.val)
    (hne : ∀ S ∈ D, NeighbourClosed Λ S)
    (hg : ∀ S ∈ D, g ∉ S)
    (hdata : ∀ S (_ : S ∈ D),
      (∀ d : BoundaryDart (S.image Subtype.val),
        DartReachable (S.image Subtype.val) d
          (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩)) ∧
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualGapStep
        (S.image Subtype.val) ∧
      IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (hr : ∀ S ∈ D, (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) S).card = r) :
    D.card ≤ r * (2 * 2) ^ (2 * r) :=
  peierls_contour_count_rayExit_verticalStrictBridgeFrontierLtUpperResidualUpperResidual_connected
    hpre D hdual hi hne hg
    (fun S hS =>
      ⟨(hdata S hS).1,
        rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualStep_of_gap
          (hdata S hS).2.1,
        (hdata S hS).2.2⟩)
    hr

/-- **The Peierls contour count from non-strip residual-index residual upper-prefix-site lower
upper-prefix non-strip strict ray-exit data and connected droplets**: straight local residual
strips are automatic by the existing finite strip-chain lemmas. -/
theorem
    peierls_contour_count_rayExit_verticalStrictBridgeFrontierLtUpperResidualUpperResNS_connected
    {i : Fin 2 → ℤ} {g : ↑Λ} {r : ℕ}
    (hpre : (Ambient.inducedGraph (latticeGraph 2) Λ).Preconnected)
    (D : Finset (Finset ↑Λ))
    (hdual : ∀ S ∈ D, dualSupport (S.image Subtype.val) ⊆ Λd)
    (hi : ∀ S ∈ D, i ∈ S.image Subtype.val)
    (hne : ∀ S ∈ D, NeighbourClosed Λ S)
    (hg : ∀ S ∈ D, g ∉ S)
    (hdata : ∀ S (_ : S ∈ D),
      (∀ d : BoundaryDart (S.image Subtype.val),
        DartReachable (S.image Subtype.val) d
          (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩)) ∧
      RayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualNonStripStep
        (S.image Subtype.val) ∧
      IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (hr : ∀ S ∈ D, (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) S).card = r) :
    D.card ≤ r * (2 * 2) ^ (2 * r) :=
  peierls_contour_count_rayExit_verticalStrictBridgeFrontierLtUpperResidualUpperResGap_connected
    hpre D hdual hi hne hg
    (fun S hS =>
      ⟨(hdata S hS).1,
        rayExitVerticalStrictBridgeFrontierLtUpperSiteAnchorResidualUpperSiteResidualGap_of_resNS
          (hdata S hS).2.1,
        (hdata S hS).2.2⟩)
    hr

end IsingModel

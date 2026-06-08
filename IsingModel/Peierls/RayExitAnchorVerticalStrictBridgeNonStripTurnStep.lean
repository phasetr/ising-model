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

end IsingModel

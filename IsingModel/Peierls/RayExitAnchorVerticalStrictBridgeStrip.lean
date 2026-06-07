import IsingModel.Peierls.RayExitAnchorVerticalStrictBridgeGap

/-!
# Strip chains for strict vertical ray-exit gaps (FV §3.7.2)

`RayExitAnchorVerticalStrictBridgeGap.lean` leaves only genuine first-exit gaps after the
adjacent-index cases have been discharged.  This file proves the next concrete subcase: when the
gap interval itself is a straight strip of boundary darts, the post-bridge chain is a finite
shared-vertex chain.

This is deliberately weaker than ray monotonicity after first exit.  The strip hypotheses are
local to the finite interval between the two first-exit indices, and the remaining non-strip
frontier geometry stays explicit.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- The horizontal `+e₀` strip dart at level `n + 1` in the lower-exits-first gap.

The dart crosses between the upper ray point, which is still in `F`, and the lower ray point,
which is assumed outside `F` for this strip step. -/
noncomputable def rayExitVerticalStrictLtStripDart
    (a b : {x : Fin 2 → ℤ // x ∈ F}) (hup : b.1 = a.1 + unitVec2 1)
    (n : ℕ) (hupper : n + 1 ≤ rayExitIndex F b.1 b.2)
    (hlower : ray0 a.1 (n + 1) ∉ F) : BoundaryDart F := by
  have hL : leftSite (ray0 a.1 n) 0 = ray0 b.1 (n + 1) := by
    rw [hup, ray0_add_unitVec2_one, ray0_succ]
    funext j
    fin_cases j <;>
      simp [leftSite, unitVec2, Pi.add_apply]
  have hR : rightSite (ray0 a.1 n) 0 = ray0 a.1 (n + 1) := by
    rw [ray0_succ]
    funext j
    fin_cases j <;>
      simp [rightSite, leftSite, Dir2.turnLeft, Dir2.vec, unitVec2, Pi.add_apply,
        Pi.sub_apply]
  refine ⟨ray0 a.1 n, 0, ?_, ?_⟩
  · rw [hL]
    exact rayExitIndex_below b.1 b.2 (n + 1) hupper
  · rw [hR]
    exact hlower

/-- A lower strip dart starts at the lower ray point with index `n`. -/
@[simp] theorem rayExitVerticalStrictLtStripDart_tail
    (a b : {x : Fin 2 → ℤ // x ∈ F}) (hup : b.1 = a.1 + unitVec2 1)
    (n : ℕ) (hupper : n + 1 ≤ rayExitIndex F b.1 b.2)
    (hlower : ray0 a.1 (n + 1) ∉ F) :
    (rayExitVerticalStrictLtStripDart a b hup n hupper hlower).tail = ray0 a.1 n :=
  rfl

/-- A lower strip dart points in direction `+e₀`. -/
@[simp] theorem rayExitVerticalStrictLtStripDart_dir
    (a b : {x : Fin 2 → ℤ // x ∈ F}) (hup : b.1 = a.1 + unitVec2 1)
    (n : ℕ) (hupper : n + 1 ≤ rayExitIndex F b.1 b.2)
    (hlower : ray0 a.1 (n + 1) ∉ F) :
    (rayExitVerticalStrictLtStripDart a b hup n hupper hlower).dir = 0 :=
  rfl

/-- A lower strip dart ends at the lower ray point with index `n + 1`. -/
@[simp] theorem rayExitVerticalStrictLtStripDart_head
    (a b : {x : Fin 2 → ℤ // x ∈ F}) (hup : b.1 = a.1 + unitVec2 1)
    (n : ℕ) (hupper : n + 1 ≤ rayExitIndex F b.1 b.2)
    (hlower : ray0 a.1 (n + 1) ∉ F) :
    (rayExitVerticalStrictLtStripDart a b hup n hupper hlower).head = ray0 a.1 (n + 1) := by
  change ray0 a.1 n + Dir2.vec 0 = ray0 a.1 (n + 1)
  rw [ray0_succ]
  simp [Dir2.vec]

/-- The endpoint lower bridge reaches the strip dart at the same index. -/
theorem dartReachable_ltBridgeDart_ltStripDart_base
    (a b : {x : Fin 2 → ℤ // x ∈ F}) (hup : b.1 = a.1 + unitVec2 1)
    (hlt : rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2)
    (hupper : rayExitIndex F a.1 a.2 + 1 ≤ rayExitIndex F b.1 b.2)
    (hlower : ray0 a.1 (rayExitIndex F a.1 a.2 + 1) ∉ F) :
    DartReachable F (rayExitVerticalStrictLtBridgeDart a b hup hlt)
      (rayExitVerticalStrictLtStripDart a b hup (rayExitIndex F a.1 a.2) hupper hlower) := by
  refine dartReachable_of_shared (v := ray0 a.1 (rayExitIndex F a.1 a.2)) ?_ ?_
  · rw [rayExitVerticalStrictLtBridgeDart_tail]
    exact Sym2.mem_mk_left _ _
  · rw [rayExitVerticalStrictLtStripDart_tail]
    exact Sym2.mem_mk_left _ _

/-- Consecutive lower strip darts share the intermediate lower ray point. -/
theorem dartReachable_ltStripDart_succ
    (a b : {x : Fin 2 → ℤ // x ∈ F}) (hup : b.1 = a.1 + unitVec2 1)
    (n : ℕ)
    (hupper₁ : n + 1 ≤ rayExitIndex F b.1 b.2)
    (hlower₁ : ray0 a.1 (n + 1) ∉ F)
    (hupper₂ : n + 2 ≤ rayExitIndex F b.1 b.2)
    (hlower₂ : ray0 a.1 (n + 2) ∉ F) :
    DartReachable F (rayExitVerticalStrictLtStripDart a b hup n hupper₁ hlower₁)
      (rayExitVerticalStrictLtStripDart a b hup (n + 1) hupper₂ hlower₂) := by
  refine dartReachable_of_shared (v := ray0 a.1 (n + 1)) ?_ ?_
  · rw [rayExitVerticalStrictLtStripDart_head]
    exact Sym2.mem_mk_right _ _
  · rw [rayExitVerticalStrictLtStripDart_tail]
    exact Sym2.mem_mk_left _ _

/-- The last lower strip dart reaches the upper ray-exit anchor. -/
theorem dartReachable_ltStripDart_rayExitAnchorDartMap_terminal
    (a b : {x : Fin 2 → ℤ // x ∈ F}) (hup : b.1 = a.1 + unitVec2 1)
    (n : ℕ) (hn : n + 1 = rayExitIndex F b.1 b.2)
    (hupper : n + 1 ≤ rayExitIndex F b.1 b.2)
    (hlower : ray0 a.1 (n + 1) ∉ F) :
    DartReachable F (rayExitVerticalStrictLtStripDart a b hup n hupper hlower)
      (rayExitAnchorDartMap F b) := by
  refine dartReachable_of_shared (v := ray0 a.1 (n + 1)) ?_ ?_
  · rw [rayExitVerticalStrictLtStripDart_head]
    exact Sym2.mem_mk_right _ _
  · have htail : (rayExitAnchorDartMap F b).tail = ray0 a.1 (n + 1) := by
      calc
        (rayExitAnchorDartMap F b).tail =
            ray0 b.1 (rayExitIndex F b.1 b.2) - unitVec2 1 := by
              rw [rayExitAnchorDartMap_tail]
        _ = ray0 b.1 (n + 1) - unitVec2 1 := by rw [← hn]
        _ = ray0 (a.1 + unitVec2 1) (n + 1) - unitVec2 1 := by rw [hup]
        _ = (ray0 a.1 (n + 1) + unitVec2 1) - unitVec2 1 := by
              rw [ray0_add_unitVec2_one]
        _ = ray0 a.1 (n + 1) := add_unitVec2_sub_unitVec2 _ _
    rw [htail]
    exact Sym2.mem_mk_left _ _

/-- A finite lower strip of horizontal darts is a `DartReachable` chain. -/
theorem dartReachable_ltStripDart_iterate
    (a b : {x : Fin 2 → ℤ // x ∈ F}) (hup : b.1 = a.1 + unitVec2 1)
    (n m : ℕ)
    (hupper : n + m + 1 ≤ rayExitIndex F b.1 b.2)
    (hstrip : ∀ t, n + 1 ≤ t → t ≤ n + m + 1 → ray0 a.1 t ∉ F) :
    DartReachable F
      (rayExitVerticalStrictLtStripDart a b hup n
        (by omega) (hstrip (n + 1) (by omega) (by omega)))
      (rayExitVerticalStrictLtStripDart a b hup (n + m)
        hupper (hstrip (n + m + 1) (by omega) (by omega))) := by
  induction m with
  | zero =>
      exact DartReachable.refl _
  | succ m ih =>
      have hupperPrev : n + m + 1 ≤ rayExitIndex F b.1 b.2 := by omega
      have hstripPrev : ∀ t, n + 1 ≤ t → t ≤ n + m + 1 → ray0 a.1 t ∉ F := by
        intro t ht0 ht1
        exact hstrip t ht0 (by omega)
      have hreach := ih hupperPrev hstripPrev
      exact hreach.trans
        (dartReachable_ltStripDart_succ a b hup (n + m)
          hupperPrev (hstrip (n + m + 1) (by omega) (by omega))
          hupper (hstrip (n + (m + 1) + 1) (by omega) (by omega)))

/-- In the lower-exits-first genuine-gap case, a straight lower-outside strip closes the
post-bridge chain without any global ray-monotonicity assumption. -/
theorem dartReachable_ltBridgeDart_rayExitAnchorDartMap_of_strip
    (a b : {x : Fin 2 → ℤ // x ∈ F}) (hup : b.1 = a.1 + unitVec2 1)
    (hlt : rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2)
    (m : ℕ) (hm : rayExitIndex F b.1 b.2 = rayExitIndex F a.1 a.2 + m + 1)
    (hstrip : ∀ t,
      rayExitIndex F a.1 a.2 + 1 ≤ t →
        t ≤ rayExitIndex F b.1 b.2 → ray0 a.1 t ∉ F) :
    DartReachable F (rayExitVerticalStrictLtBridgeDart a b hup hlt)
      (rayExitAnchorDartMap F b) := by
  have hupperBase : rayExitIndex F a.1 a.2 + 1 ≤ rayExitIndex F b.1 b.2 := by omega
  have hbase := dartReachable_ltBridgeDart_ltStripDart_base a b hup hlt hupperBase
    (hstrip (rayExitIndex F a.1 a.2 + 1) (by omega) (by omega))
  have hupperLast : rayExitIndex F a.1 a.2 + m + 1 ≤ rayExitIndex F b.1 b.2 := by
    omega
  have hiter := dartReachable_ltStripDart_iterate a b hup (rayExitIndex F a.1 a.2) m
    hupperLast (fun t ht0 ht1 => hstrip t ht0 (by omega))
  have hterminal := dartReachable_ltStripDart_rayExitAnchorDartMap_terminal a b hup
    (rayExitIndex F a.1 a.2 + m) (by omega) hupperLast
    (hstrip (rayExitIndex F a.1 a.2 + m + 1) (by omega) (by omega))
  exact hbase.trans (hiter.trans hterminal)

/-- The horizontal `-e₀` strip dart at level `n + 1` in the upper-exits-first gap.

The dart crosses between the lower ray point, which is still in `F`, and the upper ray point,
which is assumed outside `F` for this strip step. -/
noncomputable def rayExitVerticalStrictGtStripDart
    (a b : {x : Fin 2 → ℤ // x ∈ F}) (hup : b.1 = a.1 + unitVec2 1)
    (n : ℕ) (hlower : n + 1 ≤ rayExitIndex F a.1 a.2)
    (hupper : ray0 b.1 (n + 1) ∉ F) : BoundaryDart F := by
  have hL : leftSite (ray0 a.1 (n + 1)) 2 = ray0 a.1 (n + 1) := by
    simp [leftSite]
  have hR : rightSite (ray0 a.1 (n + 1)) 2 = ray0 b.1 (n + 1) := by
    rw [hup, ray0_add_unitVec2_one]
    funext j
    fin_cases j <;>
      simp [rightSite, leftSite, Dir2.turnLeft, Dir2.vec, unitVec2, Pi.add_apply,
        Pi.sub_apply]
  refine ⟨ray0 a.1 (n + 1), 2, ?_, ?_⟩
  · rw [hL]
    exact rayExitIndex_below a.1 a.2 (n + 1) hlower
  · rw [hR]
    exact hupper

/-- An upper strip dart starts at the lower ray point with index `n + 1`. -/
@[simp] theorem rayExitVerticalStrictGtStripDart_tail
    (a b : {x : Fin 2 → ℤ // x ∈ F}) (hup : b.1 = a.1 + unitVec2 1)
    (n : ℕ) (hlower : n + 1 ≤ rayExitIndex F a.1 a.2)
    (hupper : ray0 b.1 (n + 1) ∉ F) :
    (rayExitVerticalStrictGtStripDart a b hup n hlower hupper).tail = ray0 a.1 (n + 1) :=
  rfl

/-- An upper strip dart points in direction `-e₀`. -/
@[simp] theorem rayExitVerticalStrictGtStripDart_dir
    (a b : {x : Fin 2 → ℤ // x ∈ F}) (hup : b.1 = a.1 + unitVec2 1)
    (n : ℕ) (hlower : n + 1 ≤ rayExitIndex F a.1 a.2)
    (hupper : ray0 b.1 (n + 1) ∉ F) :
    (rayExitVerticalStrictGtStripDart a b hup n hlower hupper).dir = 2 :=
  rfl

/-- An upper strip dart ends at the lower ray point with index `n`. -/
@[simp] theorem rayExitVerticalStrictGtStripDart_head
    (a b : {x : Fin 2 → ℤ // x ∈ F}) (hup : b.1 = a.1 + unitVec2 1)
    (n : ℕ) (hlower : n + 1 ≤ rayExitIndex F a.1 a.2)
    (hupper : ray0 b.1 (n + 1) ∉ F) :
    (rayExitVerticalStrictGtStripDart a b hup n hlower hupper).head = ray0 a.1 n := by
  change ray0 a.1 (n + 1) + Dir2.vec 2 = ray0 a.1 n
  rw [ray0_succ]
  funext j
  fin_cases j <;> simp [Dir2.vec, unitVec2, Pi.add_apply]

/-- The lower ray-exit anchor reaches the last upper strip dart. -/
theorem dartReachable_rayExitAnchorDartMap_gtStripDart_terminal
    (a b : {x : Fin 2 → ℤ // x ∈ F}) (hup : b.1 = a.1 + unitVec2 1)
    (n : ℕ) (hn : n + 1 = rayExitIndex F a.1 a.2)
    (hlower : n + 1 ≤ rayExitIndex F a.1 a.2)
    (hupper : ray0 b.1 (n + 1) ∉ F) :
    DartReachable F (rayExitAnchorDartMap F a)
      (rayExitVerticalStrictGtStripDart a b hup n hlower hupper) := by
  refine dartReachable_of_shared (v := ray0 a.1 (n + 1)) ?_ ?_
  · have hhead : (rayExitAnchorDartMap F a).head = ray0 a.1 (n + 1) := by
      rw [rayExitAnchorDartMap_head, hn]
    rw [hhead]
    exact Sym2.mem_mk_right _ _
  · rw [rayExitVerticalStrictGtStripDart_tail]
    exact Sym2.mem_mk_left _ _

/-- Consecutive upper strip darts are reachable in the direction from the lower anchor down to the
upper endpoint bridge. -/
theorem dartReachable_gtStripDart_succ_reverse
    (a b : {x : Fin 2 → ℤ // x ∈ F}) (hup : b.1 = a.1 + unitVec2 1)
    (n : ℕ)
    (hlower₁ : n + 1 ≤ rayExitIndex F a.1 a.2)
    (hupper₁ : ray0 b.1 (n + 1) ∉ F)
    (hlower₂ : n + 2 ≤ rayExitIndex F a.1 a.2)
    (hupper₂ : ray0 b.1 (n + 2) ∉ F) :
    DartReachable F (rayExitVerticalStrictGtStripDart a b hup (n + 1) hlower₂ hupper₂)
      (rayExitVerticalStrictGtStripDart a b hup n hlower₁ hupper₁) := by
  refine dartReachable_of_shared (v := ray0 a.1 (n + 1)) ?_ ?_
  · rw [rayExitVerticalStrictGtStripDart_head]
    exact Sym2.mem_mk_right _ _
  · rw [rayExitVerticalStrictGtStripDart_tail]
    exact Sym2.mem_mk_left _ _

/-- The first upper strip dart reaches the forced upper endpoint bridge. -/
theorem dartReachable_gtStripDart_gtBridgeDart_base
    (a b : {x : Fin 2 → ℤ // x ∈ F}) (hup : b.1 = a.1 + unitVec2 1)
    (hgt : rayExitIndex F b.1 b.2 < rayExitIndex F a.1 a.2)
    (hlower : rayExitIndex F b.1 b.2 + 1 ≤ rayExitIndex F a.1 a.2)
    (hupper : ray0 b.1 (rayExitIndex F b.1 b.2 + 1) ∉ F) :
    DartReachable F
      (rayExitVerticalStrictGtStripDart a b hup (rayExitIndex F b.1 b.2) hlower hupper)
      (rayExitVerticalStrictGtBridgeDart a b hup hgt) := by
  refine dartReachable_of_shared (v := ray0 a.1 (rayExitIndex F b.1 b.2 + 1)) ?_ ?_
  · rw [rayExitVerticalStrictGtStripDart_tail]
    exact Sym2.mem_mk_left _ _
  · rw [rayExitVerticalStrictGtBridgeDart_tail]
    exact Sym2.mem_mk_left _ _

/-- A finite upper strip of horizontal darts is a `DartReachable` chain, oriented from larger
indices down to the first upper exit. -/
theorem dartReachable_gtStripDart_iterate_reverse
    (a b : {x : Fin 2 → ℤ // x ∈ F}) (hup : b.1 = a.1 + unitVec2 1)
    (n m : ℕ)
    (hlower : n + m + 1 ≤ rayExitIndex F a.1 a.2)
    (hstrip : ∀ t, n + 1 ≤ t → t ≤ n + m + 1 → ray0 b.1 t ∉ F) :
    DartReachable F
      (rayExitVerticalStrictGtStripDart a b hup (n + m)
        hlower (hstrip (n + m + 1) (by omega) (by omega)))
      (rayExitVerticalStrictGtStripDart a b hup n
        (by omega) (hstrip (n + 1) (by omega) (by omega))) := by
  induction m with
  | zero =>
      exact DartReachable.refl _
  | succ m ih =>
      have hlowerPrev : n + m + 1 ≤ rayExitIndex F a.1 a.2 := by omega
      have hstripPrev : ∀ t, n + 1 ≤ t → t ≤ n + m + 1 → ray0 b.1 t ∉ F := by
        intro t ht0 ht1
        exact hstrip t ht0 (by omega)
      have hreach := ih hlowerPrev hstripPrev
      exact (dartReachable_gtStripDart_succ_reverse a b hup (n + m)
        hlowerPrev (hstrip (n + m + 1) (by omega) (by omega))
        hlower (hstrip (n + (m + 1) + 1) (by omega) (by omega))).trans hreach

/-- In the upper-exits-first genuine-gap case, a straight upper-outside strip closes the
post-bridge chain without any global ray-monotonicity assumption. -/
theorem dartReachable_rayExitAnchorDartMap_gtBridgeDart_of_strip
    (a b : {x : Fin 2 → ℤ // x ∈ F}) (hup : b.1 = a.1 + unitVec2 1)
    (hgt : rayExitIndex F b.1 b.2 < rayExitIndex F a.1 a.2)
    (m : ℕ) (hm : rayExitIndex F a.1 a.2 = rayExitIndex F b.1 b.2 + m + 1)
    (hstrip : ∀ t,
      rayExitIndex F b.1 b.2 + 1 ≤ t →
        t ≤ rayExitIndex F a.1 a.2 → ray0 b.1 t ∉ F) :
    DartReachable F (rayExitAnchorDartMap F a)
      (rayExitVerticalStrictGtBridgeDart a b hup hgt) := by
  have hlowerLast : rayExitIndex F b.1 b.2 + m + 1 ≤ rayExitIndex F a.1 a.2 := by
    omega
  have hterminal := dartReachable_rayExitAnchorDartMap_gtStripDart_terminal a b hup
    (rayExitIndex F b.1 b.2 + m) (by omega) hlowerLast
    (hstrip (rayExitIndex F b.1 b.2 + m + 1) (by omega) (by omega))
  have hiter := dartReachable_gtStripDart_iterate_reverse a b hup
    (rayExitIndex F b.1 b.2) m hlowerLast (fun t ht0 ht1 => hstrip t ht0 (by omega))
  have hlowerBase : rayExitIndex F b.1 b.2 + 1 ≤ rayExitIndex F a.1 a.2 := by omega
  have hbase := dartReachable_gtStripDart_gtBridgeDart_base a b hup hgt hlowerBase
    (hstrip (rayExitIndex F b.1 b.2 + 1) (by omega) (by omega))
  exact hterminal.trans (hiter.trans hbase)

/-- The lower-exits-first genuine gap is a straight strip if every lower ray point between the two
first-exit indices is outside `F`. -/
def RayExitVerticalStrictLtGapStrip (F : Finset (Fin 2 → ℤ))
    (a b : {x : Fin 2 → ℤ // x ∈ F}) : Prop :=
  ∃ m : ℕ,
    rayExitIndex F b.1 b.2 = rayExitIndex F a.1 a.2 + m + 1 ∧
      ∀ t,
        rayExitIndex F a.1 a.2 + 1 ≤ t →
          t ≤ rayExitIndex F b.1 b.2 → ray0 a.1 t ∉ F

/-- The upper-exits-first genuine gap is a straight strip if every upper ray point between the two
first-exit indices is outside `F`. -/
def RayExitVerticalStrictGtGapStrip (F : Finset (Fin 2 → ℤ))
    (a b : {x : Fin 2 → ℤ // x ∈ F}) : Prop :=
  ∃ m : ℕ,
    rayExitIndex F a.1 a.2 = rayExitIndex F b.1 b.2 + m + 1 ∧
      ∀ t,
        rayExitIndex F b.1 b.2 + 1 ≤ t →
          t ≤ rayExitIndex F a.1 a.2 → ray0 b.1 t ∉ F

/-- Lower-exits-first bridge-gap data only for genuine gaps which are not straight strips. -/
def RayExitVerticalStrictLtBridgeNonStripGapChain (F : Finset (Fin 2 → ℤ)) : Prop :=
  ∀ a b : {x : Fin 2 → ℤ // x ∈ F},
    (hup : b.1 = a.1 + unitVec2 1) →
      (hlt : rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2) →
        rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2 →
          ¬ RayExitVerticalStrictLtGapStrip F a b →
            DartReachable F (rayExitVerticalStrictLtBridgeDart a b hup hlt)
              (rayExitAnchorDartMap F b)

/-- Upper-exits-first bridge-gap data only for genuine gaps which are not straight strips. -/
def RayExitVerticalStrictGtBridgeNonStripGapChain (F : Finset (Fin 2 → ℤ)) : Prop :=
  ∀ a b : {x : Fin 2 → ℤ // x ∈ F},
    (hup : b.1 = a.1 + unitVec2 1) →
      (hgt : rayExitIndex F b.1 b.2 < rayExitIndex F a.1 a.2) →
        rayExitIndex F b.1 b.2 + 1 < rayExitIndex F a.1 a.2 →
          ¬ RayExitVerticalStrictGtGapStrip F a b →
            DartReachable F (rayExitAnchorDartMap F a)
              (rayExitVerticalStrictGtBridgeDart a b hup hgt)

/-- The strip-reduced form of the strict vertical bridge-gap input. -/
def RayExitVerticalStrictBridgeNonStripGapChainStep (F : Finset (Fin 2 → ℤ)) : Prop :=
  RayExitVerticalStrictLtBridgeNonStripGapChain F ∧
    RayExitVerticalStrictGtBridgeNonStripGapChain F

/-- Non-strip lower gap data recover the full lower gap-chain input, because straight strips are
finite shared-vertex chains. -/
theorem rayExitVerticalStrictLtBridgeGapChain_of_nonStripGapChain
    (hfrontier : RayExitVerticalStrictLtBridgeNonStripGapChain F) :
    RayExitVerticalStrictLtBridgeGapChain F := by
  intro a b hup hlt hgap
  by_cases hstrip : RayExitVerticalStrictLtGapStrip F a b
  · rcases hstrip with ⟨m, hm, hout⟩
    exact dartReachable_ltBridgeDart_rayExitAnchorDartMap_of_strip a b hup hlt m hm hout
  · exact hfrontier a b hup hlt hgap hstrip

/-- Non-strip upper gap data recover the full upper gap-chain input, because straight strips are
finite shared-vertex chains. -/
theorem rayExitVerticalStrictGtBridgeGapChain_of_nonStripGapChain
    (hfrontier : RayExitVerticalStrictGtBridgeNonStripGapChain F) :
    RayExitVerticalStrictGtBridgeGapChain F := by
  intro a b hup hgt hgap
  by_cases hstrip : RayExitVerticalStrictGtGapStrip F a b
  · rcases hstrip with ⟨m, hm, hout⟩
    exact dartReachable_rayExitAnchorDartMap_gtBridgeDart_of_strip a b hup hgt m hm hout
  · exact hfrontier a b hup hgt hgap hstrip

/-- Non-strip bridge-gap data recover the full bridge-gap input. -/
theorem rayExitVerticalStrictBridgeGapChainStep_of_nonStripGapChainStep
    (hfrontier : RayExitVerticalStrictBridgeNonStripGapChainStep F) :
    RayExitVerticalStrictBridgeGapChainStep F :=
  ⟨rayExitVerticalStrictLtBridgeGapChain_of_nonStripGapChain hfrontier.1,
    rayExitVerticalStrictGtBridgeGapChain_of_nonStripGapChain hfrontier.2⟩

/-- Pairwise dart reachability from non-strip bridge-gap data and within-`F` connectivity. -/
theorem dartReachable_of_rayExitVerticalStrictBridgeNonStripGapChain
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hfrontier : RayExitVerticalStrictBridgeNonStripGapChainStep F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b)
    (d e : BoundaryDart F) : DartReachable F d e :=
  dartReachable_of_rayExitVerticalStrictBridgeGapChain hanchor
    (rayExitVerticalStrictBridgeGapChainStep_of_nonStripGapChainStep hfrontier) hconn d e

/-- The common-box dual cut is edge-connected from non-strip bridge-gap data. -/
theorem dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeNonStripGapChain
    {Λd : Finset (Fin 2 → ℤ)}
    (hsub : dualSupport F ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hfrontier : RayExitVerticalStrictBridgeNonStripGapChainStep F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeGapChain hsub hanchor
    (rayExitVerticalStrictBridgeGapChainStep_of_nonStripGapChainStep hfrontier) hconn

/-- **The Peierls contour count from non-strip strict ray-exit data**: adjacent-index cases and
straight strip gaps are automatic, so the remaining input only covers non-strip genuine gaps. -/
theorem peierls_contour_count_rayExit_verticalStrictBridgeNonStripGapChain
    {Λ Λd : Finset (Fin 2 → ℤ)} {i : Fin 2 → ℤ} {g : ↑Λ} {r : ℕ}
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
      RayExitVerticalStrictBridgeNonStripGapChainStep (S.image Subtype.val) ∧
      (∀ a ∈ S.image Subtype.val, ∀ b ∈ S.image Subtype.val,
        ReachableWithin (latticeGraph 2) (S.image Subtype.val) a b))
    (hr : ∀ S ∈ D, (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) S).card = r) :
    D.card ≤ r * (2 * 2) ^ (2 * r) :=
  peierls_contour_count_rayExit_verticalStrictBridgeGapChain hpre D hdual hi hne hg
    (fun S hS =>
      ⟨(hdata S hS).1,
        rayExitVerticalStrictBridgeGapChainStep_of_nonStripGapChainStep (hdata S hS).2.1,
        (hdata S hS).2.2⟩)
    hr

/-- Pairwise dart reachability from non-strip bridge-gap data and connectedness of the underlying
box droplet. -/
theorem dartReachable_of_rayExitVerticalStrictBridgeNonStripGapChain_connected
    {Λ : Finset (Fin 2 → ℤ)} {S : Finset ↑Λ}
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hfrontier : RayExitVerticalStrictBridgeNonStripGapChainStep (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (d e : BoundaryDart (S.image Subtype.val)) :
    DartReachable (S.image Subtype.val) d e :=
  dartReachable_of_rayExitVerticalStrictBridgeGapChain_connected hanchor
    (rayExitVerticalStrictBridgeGapChainStep_of_nonStripGapChainStep hfrontier) hconn d e

/-- The common-box dual cut is edge-connected from non-strip bridge-gap data and connectedness of
the underlying box droplet. -/
theorem dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeNonStripGapChain_connected
    {Λ Λd : Finset (Fin 2 → ℤ)} {S : Finset ↑Λ}
    (hsub : dualSupport (S.image Subtype.val) ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hfrontier : RayExitVerticalStrictBridgeNonStripGapChainStep (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeGapChain_connected hsub hanchor
    (rayExitVerticalStrictBridgeGapChainStep_of_nonStripGapChainStep hfrontier) hconn

/-- **The Peierls contour count from non-strip strict ray-exit data and connected droplets**:
straight strip gaps are automatic, and ordinary within-image connectivity is supplied from
`IsConnectedDroplet`. -/
theorem peierls_contour_count_rayExit_verticalStrictBridgeNonStripGapChain_connected
    {Λ Λd : Finset (Fin 2 → ℤ)} {i : Fin 2 → ℤ} {g : ↑Λ} {r : ℕ}
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
      RayExitVerticalStrictBridgeNonStripGapChainStep (S.image Subtype.val) ∧
      IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (hr : ∀ S ∈ D, (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) S).card = r) :
    D.card ≤ r * (2 * 2) ^ (2 * r) :=
  peierls_contour_count_rayExit_verticalStrictBridgeGapChain_connected hpre D hdual hi hne hg
    (fun S hS =>
      ⟨(hdata S hS).1,
        rayExitVerticalStrictBridgeGapChainStep_of_nonStripGapChainStep (hdata S hS).2.1,
        (hdata S hS).2.2⟩)
    hr

end IsingModel

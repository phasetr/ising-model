import IsingModel.Peierls.RayExitAnchorVerticalStrictOrdered

/-!
# First bridge darts for strict vertical ray-exit steps (FV §3.7.2)

The ordered strict vertical ray-exit split leaves two frontier-chain obligations.  This file
constructs the first boundary dart that is forced at the near end of each ordered case:

* if the lower ray exits first, the lower exit anchor shares a vertex with a horizontal `+e₀`
  boundary dart along the lower/upper interface;
* if the upper ray exits first, the upper exit anchor shares a vertex with a horizontal `-e₀`
  boundary dart along the same interface.

These are only endpoint bridge darts.  No monotonicity after the first exit is assumed, so this
file deliberately does not claim that the whole vertical strip is a straight chain.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- The bridge dart in the ordered strict case where the lower ray exits first.

For `b = a + e₁` and `k_a < k_b`, the lower successor `ray0 a (k_a+1)` is outside
`F`, while the upper successor `ray0 b (k_a+1)` is still in `F`.  The horizontal
`+e₀` dart based at the lower exit point is therefore a boundary dart. -/
noncomputable def rayExitVerticalStrictLtBridgeDart
    (a b : {x : Fin 2 → ℤ // x ∈ F}) (hup : b.1 = a.1 + unitVec2 1)
    (hlt : rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2) : BoundaryDart F := by
  let ka := rayExitIndex F a.1 a.2
  let kb := rayExitIndex F b.1 b.2
  have hle : ka + 1 ≤ kb := Nat.succ_le_of_lt hlt
  have hL : leftSite (ray0 a.1 ka) 0 = ray0 b.1 (ka + 1) := by
    rw [hup, ray0_add_unitVec2_one, ray0_succ]
    funext j
    fin_cases j <;>
      simp [leftSite, unitVec2, Pi.add_apply]
  have hR : rightSite (ray0 a.1 ka) 0 = ray0 a.1 (ka + 1) := by
    rw [ray0_succ]
    funext j
    fin_cases j <;>
      simp [rightSite, leftSite, Dir2.turnLeft, Dir2.vec, unitVec2, Pi.add_apply,
        Pi.sub_apply]
  refine ⟨ray0 a.1 ka, 0, ?_, ?_⟩
  · rw [hL]
    exact rayExitIndex_below b.1 b.2 (ka + 1) hle
  · rw [hR]
    exact rayExitIndex_succ_not_mem (F := F) a.1 a.2

/-- The lower-first bridge dart starts at the lower ray's exit point. -/
@[simp] theorem rayExitVerticalStrictLtBridgeDart_tail
    (a b : {x : Fin 2 → ℤ // x ∈ F}) (hup : b.1 = a.1 + unitVec2 1)
    (hlt : rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2) :
    (rayExitVerticalStrictLtBridgeDart a b hup hlt).tail =
      ray0 a.1 (rayExitIndex F a.1 a.2) :=
  rfl

/-- The lower-first bridge dart points in direction `+e₀`. -/
@[simp] theorem rayExitVerticalStrictLtBridgeDart_dir
    (a b : {x : Fin 2 → ℤ // x ∈ F}) (hup : b.1 = a.1 + unitVec2 1)
    (hlt : rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2) :
    (rayExitVerticalStrictLtBridgeDart a b hup hlt).dir = 0 :=
  rfl

/-- The lower-first bridge dart ends at the first point outside the lower ray. -/
@[simp] theorem rayExitVerticalStrictLtBridgeDart_head
    (a b : {x : Fin 2 → ℤ // x ∈ F}) (hup : b.1 = a.1 + unitVec2 1)
    (hlt : rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2) :
    (rayExitVerticalStrictLtBridgeDart a b hup hlt).head =
      ray0 a.1 (rayExitIndex F a.1 a.2 + 1) := by
  change ray0 a.1 (rayExitIndex F a.1 a.2) + Dir2.vec 0 =
    ray0 a.1 (rayExitIndex F a.1 a.2 + 1)
  rw [ray0_succ]
  simp [Dir2.vec]

/-- In the lower-first case, the lower ray-exit anchor shares its exit point with the
bridge dart. -/
theorem rayExitVerticalStrictLtBridgeDart_shared
    (a b : {x : Fin 2 → ℤ // x ∈ F}) (hup : b.1 = a.1 + unitVec2 1)
    (hlt : rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2) :
    ∃ v : Fin 2 → ℤ,
      v ∈ s((rayExitAnchorDartMap F a).tail, (rayExitAnchorDartMap F a).head) ∧
        v ∈ s((rayExitVerticalStrictLtBridgeDart a b hup hlt).tail,
          (rayExitVerticalStrictLtBridgeDart a b hup hlt).head) := by
  refine ⟨ray0 a.1 (rayExitIndex F a.1 a.2), rayExitAnchorDartMap_anchor_mem a, ?_⟩
  rw [rayExitVerticalStrictLtBridgeDart_tail]
  exact Sym2.mem_mk_left _ _

/-- The lower ray-exit anchor reaches the lower-first bridge dart by one shared-vertex step. -/
theorem dartReachable_rayExitAnchorDartMap_ltBridgeDart
    (a b : {x : Fin 2 → ℤ // x ∈ F}) (hup : b.1 = a.1 + unitVec2 1)
    (hlt : rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2) :
    DartReachable F (rayExitAnchorDartMap F a)
      (rayExitVerticalStrictLtBridgeDart a b hup hlt) := by
  obtain ⟨_, ha, hb⟩ := rayExitVerticalStrictLtBridgeDart_shared a b hup hlt
  exact dartReachable_of_shared ha hb

/-- The bridge dart in the ordered strict case where the upper ray exits first.

For `b = a + e₁` and `k_b < k_a`, the upper successor `ray0 b (k_b+1)` is outside
`F`, while the lower successor `ray0 a (k_b+1)` is still in `F`.  The horizontal
`-e₀` dart from the lower successor back to the lower exit coordinate is therefore a
boundary dart. -/
noncomputable def rayExitVerticalStrictGtBridgeDart
    (a b : {x : Fin 2 → ℤ // x ∈ F}) (hup : b.1 = a.1 + unitVec2 1)
    (hgt : rayExitIndex F b.1 b.2 < rayExitIndex F a.1 a.2) : BoundaryDart F := by
  let ka := rayExitIndex F a.1 a.2
  let kb := rayExitIndex F b.1 b.2
  have hle : kb + 1 ≤ ka := Nat.succ_le_of_lt hgt
  have hL : leftSite (ray0 a.1 (kb + 1)) 2 = ray0 a.1 (kb + 1) := by
    simp [leftSite]
  have hR : rightSite (ray0 a.1 (kb + 1)) 2 = ray0 b.1 (kb + 1) := by
    rw [hup, ray0_add_unitVec2_one]
    funext j
    fin_cases j <;>
      simp [rightSite, leftSite, Dir2.turnLeft, Dir2.vec, unitVec2, Pi.add_apply,
        Pi.sub_apply]
  refine ⟨ray0 a.1 (kb + 1), 2, ?_, ?_⟩
  · rw [hL]
    exact rayExitIndex_below a.1 a.2 (kb + 1) hle
  · rw [hR]
    exact rayExitIndex_succ_not_mem (F := F) b.1 b.2

/-- The upper-first bridge dart starts at the lower successor of the upper exit index. -/
@[simp] theorem rayExitVerticalStrictGtBridgeDart_tail
    (a b : {x : Fin 2 → ℤ // x ∈ F}) (hup : b.1 = a.1 + unitVec2 1)
    (hgt : rayExitIndex F b.1 b.2 < rayExitIndex F a.1 a.2) :
    (rayExitVerticalStrictGtBridgeDart a b hup hgt).tail =
      ray0 a.1 (rayExitIndex F b.1 b.2 + 1) :=
  rfl

/-- The upper-first bridge dart points in direction `-e₀`. -/
@[simp] theorem rayExitVerticalStrictGtBridgeDart_dir
    (a b : {x : Fin 2 → ℤ // x ∈ F}) (hup : b.1 = a.1 + unitVec2 1)
    (hgt : rayExitIndex F b.1 b.2 < rayExitIndex F a.1 a.2) :
    (rayExitVerticalStrictGtBridgeDart a b hup hgt).dir = 2 :=
  rfl

/-- The upper-first bridge dart ends at the lower site below the upper exit point. -/
@[simp] theorem rayExitVerticalStrictGtBridgeDart_head
    (a b : {x : Fin 2 → ℤ // x ∈ F}) (hup : b.1 = a.1 + unitVec2 1)
    (hgt : rayExitIndex F b.1 b.2 < rayExitIndex F a.1 a.2) :
    (rayExitVerticalStrictGtBridgeDart a b hup hgt).head =
      ray0 a.1 (rayExitIndex F b.1 b.2) := by
  change ray0 a.1 (rayExitIndex F b.1 b.2 + 1) + Dir2.vec 2 =
    ray0 a.1 (rayExitIndex F b.1 b.2)
  rw [ray0_succ]
  funext j
  fin_cases j <;> simp [Dir2.vec, unitVec2, Pi.add_apply]

/-- In the upper-first case, the upper ray-exit anchor shares its lower tail point with the
bridge dart. -/
theorem rayExitVerticalStrictGtBridgeDart_shared
    (a b : {x : Fin 2 → ℤ // x ∈ F}) (hup : b.1 = a.1 + unitVec2 1)
    (hgt : rayExitIndex F b.1 b.2 < rayExitIndex F a.1 a.2) :
    ∃ v : Fin 2 → ℤ,
      v ∈ s((rayExitAnchorDartMap F b).tail, (rayExitAnchorDartMap F b).head) ∧
        v ∈ s((rayExitVerticalStrictGtBridgeDart a b hup hgt).tail,
          (rayExitVerticalStrictGtBridgeDart a b hup hgt).head) := by
  refine ⟨ray0 a.1 (rayExitIndex F b.1 b.2), ?_, ?_⟩
  · have htail : (rayExitAnchorDartMap F b).tail = ray0 a.1 (rayExitIndex F b.1 b.2) := by
      rw [rayExitAnchorDartMap_tail]
      have hray : ray0 b.1 (rayExitIndex F b.1 b.2) =
          ray0 a.1 (rayExitIndex F b.1 b.2) + unitVec2 1 := by
        calc
          ray0 b.1 (rayExitIndex F b.1 b.2)
              = ray0 (a.1 + unitVec2 1) (rayExitIndex F b.1 b.2) :=
                congrArg (fun x => ray0 x (rayExitIndex F b.1 b.2)) hup
          _ = ray0 a.1 (rayExitIndex F b.1 b.2) + unitVec2 1 :=
                ray0_add_unitVec2_one a.1 (rayExitIndex F b.1 b.2)
      rw [hray, add_unitVec2_sub_unitVec2]
    rw [htail]
    exact Sym2.mem_mk_left _ _
  · rw [rayExitVerticalStrictGtBridgeDart_head]
    exact Sym2.mem_mk_right _ _

/-- The upper ray-exit anchor reaches the upper-first bridge dart by one shared-vertex step. -/
theorem dartReachable_rayExitAnchorDartMap_gtBridgeDart
    (a b : {x : Fin 2 → ℤ // x ∈ F}) (hup : b.1 = a.1 + unitVec2 1)
    (hgt : rayExitIndex F b.1 b.2 < rayExitIndex F a.1 a.2) :
    DartReachable F (rayExitAnchorDartMap F b)
      (rayExitVerticalStrictGtBridgeDart a b hup hgt) := by
  obtain ⟨_, hb, hbridge⟩ := rayExitVerticalStrictGtBridgeDart_shared a b hup hgt
  exact dartReachable_of_shared hb hbridge

end IsingModel

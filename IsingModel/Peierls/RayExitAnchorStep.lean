import IsingModel.Peierls.RayExitAnchorPrefix

/-!
# Horizontal ray-exit anchor shadow steps (FV §3.7.2)

The prefix-stability API in `RayExitAnchorPrefix.lean` shows that two sites on the same
`+e₀` ray before the first exit choose the same ray-exit anchor dart.  This file repackages the
one-step horizontal consequences in the shape used by the later `hshadow` input.

It only handles horizontal `±e₀` adjacent sites.  The vertical and frontier cases, and the
same-left-site anchoring input `hanchor`, remain separate geometric tasks.

* `rayExitAnchorDartMap_ray0_one_shared` — one ray step from `x` shares the anchor edge.
* `rayExitAnchorDartMap_add_e0_shared` — the `x → x + e₀` horizontal step.
* `rayExitAnchorDartMap_sub_e0_shared` — the `x → x - e₀` horizontal step by symmetry.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- The first ray step is the `+e₀` coordinate shift. -/
theorem ray0_one (x : Fin 2 → ℤ) : ray0 x 1 = x + unitVec2 0 := by
  simpa using ray0_succ x 0

/-- If the first ray step remains in `F`, it is before the chosen first exit. -/
theorem one_le_rayExitIndex_of_ray0_one_mem (x : {x : Fin 2 → ℤ // x ∈ F})
    (hx1 : ray0 x.1 1 ∈ F) : 1 ≤ rayExitIndex F x.1 x.2 := by
  by_contra hle
  have hzero : rayExitIndex F x.1 x.2 = 0 := by omega
  have hout : ray0 x.1 1 ∉ F := by
    simpa [hzero] using rayExitIndex_succ_not_mem (F := F) x.1 x.2
  exact hout hx1

/-- One step along the same `+e₀` ray shares the ray-exit anchor edge. -/
theorem rayExitAnchorDartMap_ray0_one_shared (x : {x : Fin 2 → ℤ // x ∈ F})
    (hx1 : ray0 x.1 1 ∈ F) :
    ∃ v : Fin 2 → ℤ,
      v ∈ s((rayExitAnchorDartMap F x).tail, (rayExitAnchorDartMap F x).head) ∧
        v ∈ s((rayExitAnchorDartMap F ⟨ray0 x.1 1, hx1⟩).tail,
          (rayExitAnchorDartMap F ⟨ray0 x.1 1, hx1⟩).head) := by
  have hle : 1 ≤ rayExitIndex F x.1 x.2 := one_le_rayExitIndex_of_ray0_one_mem x hx1
  obtain ⟨v, hvx, hvy⟩ := rayExitAnchorDartMap_prefix_shared x (t := 1) hle
  refine ⟨v, hvx, ?_⟩
  have hsub :
      (⟨ray0 x.1 1, rayExitIndex_below x.1 x.2 1 hle⟩ :
        {x : Fin 2 → ℤ // x ∈ F}) = ⟨ray0 x.1 1, hx1⟩ :=
    Subtype.ext rfl
  simpa [hsub] using hvy

/-- The forward horizontal `+e₀` step shares the ray-exit anchor edge. -/
theorem rayExitAnchorDartMap_add_e0_shared (x : {x : Fin 2 → ℤ // x ∈ F})
    (hx1 : x.1 + unitVec2 0 ∈ F) :
    ∃ v : Fin 2 → ℤ,
      v ∈ s((rayExitAnchorDartMap F x).tail, (rayExitAnchorDartMap F x).head) ∧
        v ∈ s((rayExitAnchorDartMap F ⟨x.1 + unitVec2 0, hx1⟩).tail,
          (rayExitAnchorDartMap F ⟨x.1 + unitVec2 0, hx1⟩).head) := by
  have hxray : ray0 x.1 1 ∈ F := by
    rwa [ray0_one]
  obtain ⟨v, hvx, hvy⟩ := rayExitAnchorDartMap_ray0_one_shared x hxray
  refine ⟨v, hvx, ?_⟩
  have hsub : (⟨ray0 x.1 1, hxray⟩ : {x : Fin 2 → ℤ // x ∈ F}) =
      ⟨x.1 + unitVec2 0, hx1⟩ :=
    Subtype.ext (ray0_one x.1)
  simpa [hsub] using hvy

/-- Subtracting and then adding the same coordinate unit vector returns the original site. -/
theorem sub_unitVec2_add_unitVec2 (x : Fin 2 → ℤ) (k : Fin 2) :
    x - unitVec2 k + unitVec2 k = x := by
  funext j
  simp [unitVec2, Pi.sub_apply, Pi.add_apply]

/-- The backward horizontal `-e₀` step shares the ray-exit anchor edge. -/
theorem rayExitAnchorDartMap_sub_e0_shared (x : {x : Fin 2 → ℤ // x ∈ F})
    (hx0 : x.1 - unitVec2 0 ∈ F) :
    ∃ v : Fin 2 → ℤ,
      v ∈ s((rayExitAnchorDartMap F x).tail, (rayExitAnchorDartMap F x).head) ∧
        v ∈ s((rayExitAnchorDartMap F ⟨x.1 - unitVec2 0, hx0⟩).tail,
          (rayExitAnchorDartMap F ⟨x.1 - unitVec2 0, hx0⟩).head) := by
  let y : {x : Fin 2 → ℤ // x ∈ F} := ⟨x.1 - unitVec2 0, hx0⟩
  have hy1 : y.1 + unitVec2 0 ∈ F := by
    simp [y]
  obtain ⟨v, hvy, hvx⟩ := rayExitAnchorDartMap_add_e0_shared (F := F) y hy1
  refine ⟨v, ?_, hvy⟩
  have hsub : (⟨y.1 + unitVec2 0, hy1⟩ : {x : Fin 2 → ℤ // x ∈ F}) = x := by
    apply Subtype.ext
    simp [y]
  simpa [hsub] using hvx

end IsingModel

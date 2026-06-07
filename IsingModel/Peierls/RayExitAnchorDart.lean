import IsingModel.Peierls.RayAnchorBox
import IsingModel.Peierls.RayExitBound
import IsingModel.Peierls.DualCutEdgeAdjacency

/-!
# Ray-exit anchor darts (FV §3.7.2)

For each site `a ∈ F`, the finite-region first-exit argument along the `+e₀` ray gives a
boundary dart at the first exit from `F`. This file packages that construction as a site-indexed
anchor map `rayExitAnchorDartMap : {x // x ∈ F} → BoundaryDart F`, a candidate shape for the
later anchored `DartReachable` data.

This does not prove the anchoring or one-edge shadow obligations. It only supplies a canonical
boundary dart chosen from each site by a ray-exit construction.

* `rayExitIndex` — the first `+e₀` exit index chosen from `a ∈ F`.
* `rayExitAnchorDart` — the concrete boundary dart whose head is the first-exit site.
* `rayExitAnchorDartMap` — the subtype-indexed map from sites of `F` to boundary darts.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- The chosen `+e₀` first-exit index from a site `a ∈ F`. -/
noncomputable def rayExitIndex (F : Finset (Fin 2 → ℤ)) (a : Fin 2 → ℤ)
    (ha : a ∈ F) : ℕ :=
  (exists_first_exit_below ha).choose

/-- Every ray point up to the chosen first-exit index stays in `F`. -/
theorem rayExitIndex_below (a : Fin 2 → ℤ) (ha : a ∈ F) :
    ∀ t, t ≤ rayExitIndex F a ha → ray0 a t ∈ F :=
  (exists_first_exit_below ha).choose_spec.1

/-- The chosen first-exit point is still in `F`. -/
theorem rayExitIndex_mem (a : Fin 2 → ℤ) (ha : a ∈ F) :
    ray0 a (rayExitIndex F a ha) ∈ F :=
  rayExitIndex_below a ha _ le_rfl

/-- The successor of the chosen ray-exit point lies outside `F`. -/
theorem rayExitIndex_succ_not_mem (a : Fin 2 → ℤ) (ha : a ∈ F) :
    ray0 a (rayExitIndex F a ha + 1) ∉ F :=
  (exists_first_exit_below ha).choose_spec.2

/-- The boundary dart obtained at the chosen `+e₀` ray exit from `a ∈ F`. -/
noncomputable def rayExitAnchorDart (F : Finset (Fin 2 → ℤ)) (a : Fin 2 → ℤ)
    (ha : a ∈ F) : BoundaryDart F :=
  e0ExitAnchorDart (rayExitIndex_mem (F := F) a ha) (by
    rw [← ray0_succ]
    exact rayExitIndex_succ_not_mem (F := F) a ha)

/-- The ray-exit anchor dart starts one `e₁` step below the chosen first-exit site. -/
@[simp] theorem rayExitAnchorDart_tail (a : Fin 2 → ℤ) (ha : a ∈ F) :
    (rayExitAnchorDart F a ha).tail = ray0 a (rayExitIndex F a ha) - unitVec2 1 :=
  e0ExitAnchorDart_tail (rayExitIndex_mem (F := F) a ha) (by
    rw [← ray0_succ]
    exact rayExitIndex_succ_not_mem (F := F) a ha)

/-- The ray-exit anchor dart points in direction `e₁`. -/
@[simp] theorem rayExitAnchorDart_dir (a : Fin 2 → ℤ) (ha : a ∈ F) :
    (rayExitAnchorDart F a ha).dir = 1 :=
  e0ExitAnchorDart_dir (rayExitIndex_mem (F := F) a ha) (by
    rw [← ray0_succ]
    exact rayExitIndex_succ_not_mem (F := F) a ha)

/-- The ray-exit anchor dart has head equal to the chosen first-exit site. -/
@[simp]
theorem rayExitAnchorDart_head (a : Fin 2 → ℤ) (ha : a ∈ F) :
    (rayExitAnchorDart F a ha).head = ray0 a (rayExitIndex F a ha) :=
  e0ExitAnchorDart_head (rayExitIndex_mem (F := F) a ha) (by
    rw [← ray0_succ]
    exact rayExitIndex_succ_not_mem (F := F) a ha)

/-- The chosen first-exit site lies on the ray-exit anchor dart's dual edge. -/
theorem rayExitAnchorDart_anchor_mem (a : Fin 2 → ℤ) (ha : a ∈ F) :
    ray0 a (rayExitIndex F a ha) ∈
      s((rayExitAnchorDart F a ha).tail, (rayExitAnchorDart F a ha).head) :=
  e0ExitAnchorDart_anchor_mem (rayExitIndex_mem (F := F) a ha) (by
    rw [← ray0_succ]
    exact rayExitIndex_succ_not_mem (F := F) a ha)

/-- The ray-exit anchor dart's dual edge lies in the whole dart dual cut. -/
theorem rayExitAnchorDart_dualEdge_mem (a : Fin 2 → ℤ) (ha : a ∈ F) :
    s((rayExitAnchorDart F a ha).tail, (rayExitAnchorDart F a ha).head) ∈ dartDualCut F :=
  dartDualEdge_mem_dartDualCut _

/-- The subtype-indexed ray-exit anchor map from sites of `F` to boundary darts. -/
noncomputable def rayExitAnchorDartMap (F : Finset (Fin 2 → ℤ)) :
    {x : Fin 2 → ℤ // x ∈ F} → BoundaryDart F :=
  fun x => rayExitAnchorDart F x.1 x.2

/-- The ray-exit anchor map is definitionally the chosen ray-exit anchor dart. -/
@[simp] theorem rayExitAnchorDartMap_apply (x : {x : Fin 2 → ℤ // x ∈ F}) :
    rayExitAnchorDartMap F x = rayExitAnchorDart F x.1 x.2 :=
  rfl

/-- The anchor map's dart has head equal to the chosen first-exit site from the input site. -/
@[simp]
theorem rayExitAnchorDartMap_head (x : {x : Fin 2 → ℤ // x ∈ F}) :
    (rayExitAnchorDartMap F x).head = ray0 x.1 (rayExitIndex F x.1 x.2) :=
  rayExitAnchorDart_head x.1 x.2

/-- The anchor map's dart starts one `e₁` step below the chosen first-exit site. -/
@[simp] theorem rayExitAnchorDartMap_tail (x : {x : Fin 2 → ℤ // x ∈ F}) :
    (rayExitAnchorDartMap F x).tail = ray0 x.1 (rayExitIndex F x.1 x.2) - unitVec2 1 :=
  rayExitAnchorDart_tail x.1 x.2

/-- The anchor map's dart points in direction `e₁`. -/
@[simp] theorem rayExitAnchorDartMap_dir (x : {x : Fin 2 → ℤ // x ∈ F}) :
    (rayExitAnchorDartMap F x).dir = 1 :=
  rayExitAnchorDart_dir x.1 x.2

/-- The chosen first-exit site lies on the anchor map's dual edge. -/
theorem rayExitAnchorDartMap_anchor_mem (x : {x : Fin 2 → ℤ // x ∈ F}) :
    ray0 x.1 (rayExitIndex F x.1 x.2) ∈
      s((rayExitAnchorDartMap F x).tail, (rayExitAnchorDartMap F x).head) :=
  rayExitAnchorDart_anchor_mem x.1 x.2

end IsingModel

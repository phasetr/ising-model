import IsingModel.Peierls.RayExitAnchoredRoute

/-!
# Ray-exit shadow route wrappers (FV §3.7.2)

`RayExitAnchoredRoute.lean` fixes the anchor map in the abstract anchored route to the concrete
ray-exit map `rayExitAnchorDartMap`.  This file narrows the per-edge transport input one step
further: instead of asking directly for `DartReachable` between the ray-exit anchors of adjacent
sites of `F`, it asks for a shared dual vertex of the two anchor edges.  The generic lemma
`dartReachable_of_shared` turns that local shadow into a `DartReachable` step.

The wrappers still keep the other inputs explicit:

* `hanchor` — every boundary dart reaches the ray-exit anchor of its left site.
* `hshadow` — adjacent sites of `F` have ray-exit anchor edges sharing a dual vertex.
* `hconn` — ordinary within-`F` connectivity, used to chain those local shadow steps.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F Λ Λd : Finset (Fin 2 → ℤ)}

/-- Pairwise dart reachability from ray-exit anchoring and shared-vertex shadow data. -/
theorem dartReachable_of_rayExitShadow
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hshadow : ∀ a b : {x : Fin 2 → ℤ // x ∈ F}, (latticeGraph 2).Adj a.1 b.1 →
      ∃ v : Fin 2 → ℤ,
        v ∈ s((rayExitAnchorDartMap F a).tail, (rayExitAnchorDartMap F a).head) ∧
        v ∈ s((rayExitAnchorDartMap F b).tail, (rayExitAnchorDartMap F b).head))
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b)
    (d e : BoundaryDart F) : DartReachable F d e :=
  dartReachable_of_rayExitAnchored hanchor
    (fun a b hab => by
      obtain ⟨_, hva, hvb⟩ := hshadow a b hab
      exact dartReachable_of_shared hva hvb)
    hconn d e

/-- The ambient dart dual cut is edge-connected from ray-exit shadow data. -/
theorem dartDualCut_isEdgeConnected_of_rayExitShadow
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hshadow : ∀ a b : {x : Fin 2 → ℤ // x ∈ F}, (latticeGraph 2).Adj a.1 b.1 →
      ∃ v : Fin 2 → ℤ,
        v ∈ s((rayExitAnchorDartMap F a).tail, (rayExitAnchorDartMap F a).head) ∧
        v ∈ s((rayExitAnchorDartMap F b).tail, (rayExitAnchorDartMap F b).head))
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b) :
    IsEdgeConnected (dartDualCut F) :=
  dartDualCut_isEdgeConnected_of_rayExitAnchored hanchor
    (fun a b hab => by
      obtain ⟨_, hva, hvb⟩ := hshadow a b hab
      exact dartReachable_of_shared hva hvb)
    hconn

/-- The subtype-lifted dual cut is edge-connected from ray-exit shadow data. -/
theorem dualCutSub_isEdgeConnected_of_rayExitShadow
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hshadow : ∀ a b : {x : Fin 2 → ℤ // x ∈ F}, (latticeGraph 2).Adj a.1 b.1 →
      ∃ v : Fin 2 → ℤ,
        v ∈ s((rayExitAnchorDartMap F a).tail, (rayExitAnchorDartMap F a).head) ∧
        v ∈ s((rayExitAnchorDartMap F b).tail, (rayExitAnchorDartMap F b).head))
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b) :
    IsEdgeConnected (dualCutSub F) :=
  dualCutSub_isEdgeConnected_of_rayExitAnchored hanchor
    (fun a b hab => by
      obtain ⟨_, hva, hvb⟩ := hshadow a b hab
      exact dartReachable_of_shared hva hvb)
    hconn

/-- The common-box dual cut is edge-connected from ray-exit shadow data. -/
theorem dualCutInBox_isEdgeConnected_of_rayExitShadow (hsub : dualSupport F ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hshadow : ∀ a b : {x : Fin 2 → ℤ // x ∈ F}, (latticeGraph 2).Adj a.1 b.1 →
      ∃ v : Fin 2 → ℤ,
        v ∈ s((rayExitAnchorDartMap F a).tail, (rayExitAnchorDartMap F a).head) ∧
        v ∈ s((rayExitAnchorDartMap F b).tail, (rayExitAnchorDartMap F b).head))
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitAnchored hsub hanchor
    (fun a b hab => by
      obtain ⟨_, hva, hvb⟩ := hshadow a b hab
      exact dartReachable_of_shared hva hvb)
    hconn

/-- **The Peierls contour count from ray-exit shadow data**: this specializes
`peierls_contour_count_rayExit_anchored` by replacing each per-edge `DartReachable` step with a
shared-vertex shadow for the two ray-exit anchor edges. -/
theorem peierls_contour_count_rayExit_shadow {i : Fin 2 → ℤ} {g : ↑Λ} {r : ℕ}
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
      (∀ a b : {x : Fin 2 → ℤ // x ∈ S.image Subtype.val},
        (latticeGraph 2).Adj a.1 b.1 →
          ∃ v : Fin 2 → ℤ,
            v ∈ s((rayExitAnchorDartMap (S.image Subtype.val) a).tail,
              (rayExitAnchorDartMap (S.image Subtype.val) a).head) ∧
            v ∈ s((rayExitAnchorDartMap (S.image Subtype.val) b).tail,
              (rayExitAnchorDartMap (S.image Subtype.val) b).head)) ∧
      (∀ a ∈ S.image Subtype.val, ∀ b ∈ S.image Subtype.val,
        ReachableWithin (latticeGraph 2) (S.image Subtype.val) a b))
    (hr : ∀ S ∈ D, (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) S).card = r) :
    D.card ≤ r * (2 * 2) ^ (2 * r) :=
  peierls_contour_count_rayExit_anchored hpre D hdual hi hne hg
    (fun S hS =>
      ⟨(hdata S hS).1, fun a b hab => by
        obtain ⟨_, hva, hvb⟩ := (hdata S hS).2.1 a b hab
        exact dartReachable_of_shared hva hvb, (hdata S hS).2.2⟩)
    hr

end IsingModel

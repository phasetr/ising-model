import IsingModel.Peierls.RayExitAnchoredRoute
import IsingModel.Peierls.RayExitAnchorAdjacency

/-!
# Ray-exit adjacency route with vertical obligations (FV §3.7.2)

`RayExitAnchorAdjacency.lean` reduces an adjacent pair of sites of `F` to a horizontal
shared-vertex case or to one of the two vertical shifts.  This file consumes that reduction in the
route-level API: horizontal steps are discharged by `dartReachable_of_shared`, and only the vertical
ray-exit anchor steps remain as explicit `DartReachable` obligations.

This is deliberately weaker than asking for a shared vertex in the vertical cases.  Vertical
ray-exit anchors can have different first-exit indices, so the later geometric input should supply
a reachable chain when needed rather than overclaiming direct edge intersection.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F Λ Λd : Finset (Fin 2 → ℤ)}

/-- The remaining vertical ray-exit anchor transport obligation: for an oriented vertical adjacent
pair of sites of `F`, the two ray-exit anchor darts are connected inside the dual cut. -/
def RayExitVerticalStep (F : Finset (Fin 2 → ℤ)) : Prop :=
  ∀ a b : {x : Fin 2 → ℤ // x ∈ F},
    b.1 = a.1 + unitVec2 1 ∨ b.1 = a.1 - unitVec2 1 →
      DartReachable F (rayExitAnchorDartMap F a) (rayExitAnchorDartMap F b)

/-- Adjacent ray-exit anchors are reachable once the two vertical coordinate cases are supplied.
The horizontal cases use the shared-vertex lemmas from `RayExitAnchorStep.lean`, via the adjacency
case reduction of `RayExitAnchorAdjacency.lean`. -/
theorem rayExitAnchorDartMap_adj_reachable_of_verticalStep
    (hvertical : RayExitVerticalStep F) (x y : {x : Fin 2 → ℤ // x ∈ F})
    (hxy : (latticeGraph 2).Adj x.1 y.1) :
    DartReachable F (rayExitAnchorDartMap F x) (rayExitAnchorDartMap F y) := by
  rcases rayExitAnchorDartMap_adj_shared_or_vertical x y hxy with hshared | hvert
  · obtain ⟨_, hvx, hvy⟩ := hshared
    exact dartReachable_of_shared hvx hvy
  · exact hvertical x y hvert

/-- Pairwise dart reachability from ray-exit anchoring, vertical-step data, and within-`F`
connectivity.  Horizontal adjacent-site transport is automatic; only vertical ray-exit transport
is left as geometry. -/
theorem dartReachable_of_rayExitAdjacency
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hvertical : RayExitVerticalStep F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b)
    (d e : BoundaryDart F) : DartReachable F d e :=
  dartReachable_of_rayExitAnchored hanchor
    (fun a b hab => rayExitAnchorDartMap_adj_reachable_of_verticalStep hvertical a b hab)
    hconn d e

/-- The ambient dart dual cut is edge-connected from ray-exit anchoring, vertical-step data, and
within-`F` connectivity. -/
theorem dartDualCut_isEdgeConnected_of_rayExitAdjacency
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hvertical : RayExitVerticalStep F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b) :
    IsEdgeConnected (dartDualCut F) :=
  dartDualCut_isEdgeConnected_of_rayExitAnchored hanchor
    (fun a b hab => rayExitAnchorDartMap_adj_reachable_of_verticalStep hvertical a b hab)
    hconn

/-- The subtype-lifted dual cut is edge-connected from ray-exit anchoring, vertical-step data, and
within-`F` connectivity. -/
theorem dualCutSub_isEdgeConnected_of_rayExitAdjacency
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hvertical : RayExitVerticalStep F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b) :
    IsEdgeConnected (dualCutSub F) :=
  dualCutSub_isEdgeConnected_of_rayExitAnchored hanchor
    (fun a b hab => rayExitAnchorDartMap_adj_reachable_of_verticalStep hvertical a b hab)
    hconn

/-- The common-box dual cut is edge-connected from ray-exit anchoring, vertical-step data, and
within-`F` connectivity. -/
theorem dualCutInBox_isEdgeConnected_of_rayExitAdjacency (hsub : dualSupport F ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hvertical : RayExitVerticalStep F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitAnchored hsub hanchor
    (fun a b hab => rayExitAnchorDartMap_adj_reachable_of_verticalStep hvertical a b hab)
    hconn

/-- **The Peierls contour count from ray-exit adjacency data**: horizontal adjacent-site steps are
closed by the ray-prefix shadow lemmas, while vertical ray-exit anchor steps remain as explicit
`DartReachable` data. -/
theorem peierls_contour_count_rayExit_adjacency {i : Fin 2 → ℤ} {g : ↑Λ} {r : ℕ}
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
      RayExitVerticalStep (S.image Subtype.val) ∧
      (∀ a ∈ S.image Subtype.val, ∀ b ∈ S.image Subtype.val,
        ReachableWithin (latticeGraph 2) (S.image Subtype.val) a b))
    (hr : ∀ S ∈ D, (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) S).card = r) :
    D.card ≤ r * (2 * 2) ^ (2 * r) :=
  peierls_contour_count_rayExit_anchored hpre D hdual hi hne hg
    (fun S hS =>
      ⟨(hdata S hS).1,
        fun a b hab =>
          rayExitAnchorDartMap_adj_reachable_of_verticalStep (hdata S hS).2.1 a b hab,
        (hdata S hS).2.2⟩)
    hr

end IsingModel

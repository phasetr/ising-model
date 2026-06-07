import IsingModel.Peierls.RayExitAnchorVerticalEqual
import IsingModel.Peierls.SingleOrbitConnTransfer

/-!
# Connected-droplet wrappers for strict vertical ray-exit data (FV §3.7.2)

`RayExitAnchorVerticalEqual.lean` narrows the vertical ray-exit transport input to the strict
upward unequal-index obligation `RayExitVerticalStrictStep`.  Its route wrappers still take the
ordinary within-image connectivity input explicitly.  For the Peierls contour count this
connectivity is already part of the box-droplet data: a connected droplet
`S : Finset ↑Λ` maps under `Subtype.val` to a connected finite set in the ambient lattice.

This file specializes `reachableWithin_image_of_isConnectedDroplet` to the strict ray-exit route,
so the remaining per-droplet data are exactly the same-left-site anchor reachability, the strict
vertical ray-exit step, and box connectedness.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {Λ Λd : Finset (Fin 2 → ℤ)}

/-- The within-image connectivity input supplied by a connected box droplet. -/
theorem rayExit_image_conn_of_isConnectedDroplet {S : Finset ↑Λ}
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (a : Fin 2 → ℤ) (ha : a ∈ S.image Subtype.val) (b : Fin 2 → ℤ)
    (hb : b ∈ S.image Subtype.val) :
    ReachableWithin (latticeGraph 2) (S.image Subtype.val) a b :=
  reachableWithin_image_of_isConnectedDroplet (latticeGraph 2) Λ S hconn a ha b hb

/-- Pairwise dart reachability from ray-exit anchoring, strict vertical data, and connectedness of
the underlying box droplet. -/
theorem dartReachable_of_rayExitVerticalStrict_connected {S : Finset ↑Λ}
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hstrict : RayExitVerticalStrictStep (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (d e : BoundaryDart (S.image Subtype.val)) :
    DartReachable (S.image Subtype.val) d e :=
  dartReachable_of_rayExitVerticalStrict hanchor hstrict
    (rayExit_image_conn_of_isConnectedDroplet hconn) d e

/-- The ambient dart dual cut is edge-connected from strict ray-exit data and connectedness of the
underlying box droplet. -/
theorem dartDualCut_isEdgeConnected_of_rayExitVerticalStrict_connected {S : Finset ↑Λ}
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hstrict : RayExitVerticalStrictStep (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S) :
    IsEdgeConnected (dartDualCut (S.image Subtype.val)) :=
  dartDualCut_isEdgeConnected_of_rayExitVerticalStrict hanchor hstrict
    (rayExit_image_conn_of_isConnectedDroplet hconn)

/-- The subtype-lifted dual cut is edge-connected from strict ray-exit data and connectedness of
the underlying box droplet. -/
theorem dualCutSub_isEdgeConnected_of_rayExitVerticalStrict_connected {S : Finset ↑Λ}
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hstrict : RayExitVerticalStrictStep (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S) :
    IsEdgeConnected (dualCutSub (S.image Subtype.val)) :=
  dualCutSub_isEdgeConnected_of_rayExitVerticalStrict hanchor hstrict
    (rayExit_image_conn_of_isConnectedDroplet hconn)

/-- The common-box dual cut is edge-connected from strict ray-exit data, dual support in the common
box, and connectedness of the underlying box droplet. -/
theorem dualCutInBox_isEdgeConnected_of_rayExitVerticalStrict_connected {S : Finset ↑Λ}
    (hsub : dualSupport (S.image Subtype.val) ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hstrict : RayExitVerticalStrictStep (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrict hsub hanchor hstrict
    (rayExit_image_conn_of_isConnectedDroplet hconn)

/-- **The Peierls contour count from strict ray-exit data and connected droplets**: the ordinary
within-image connectivity input is supplied from `IsConnectedDroplet` in the box. -/
theorem peierls_contour_count_rayExit_verticalStrict_connected {i : Fin 2 → ℤ} {g : ↑Λ} {r : ℕ}
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
      RayExitVerticalStrictStep (S.image Subtype.val) ∧
      IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (hr : ∀ S ∈ D, (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) S).card = r) :
    D.card ≤ r * (2 * 2) ^ (2 * r) :=
  peierls_contour_count_rayExit_verticalStrict hpre D hdual hi hne hg
    (fun S hS =>
      ⟨(hdata S hS).1, (hdata S hS).2.1,
        rayExit_image_conn_of_isConnectedDroplet (hdata S hS).2.2⟩)
    hr

end IsingModel

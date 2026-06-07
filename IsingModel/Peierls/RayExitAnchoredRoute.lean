import IsingModel.Peierls.PeierlsContourCount
import IsingModel.Peierls.RayExitAnchorDart

/-!
# Ray-exit specialization of the anchored route (FV §3.7.2)

The anchored `DartReachable` interface isolates the global edge-connectedness target behind an
anchor map `φ : {x // x ∈ F} → BoundaryDart F`.  `RayExitAnchorDart.lean` supplies a canonical
candidate map by sending every site of `F` to the boundary dart at the first `+e₀` ray exit.

This file specializes the abstract anchored route to that concrete ray-exit map.  It still keeps
the genuine geometric obligations explicit:

* `hanchor` — every boundary dart reaches the ray-exit anchor of its left site.
* `hstep` — adjacent sites of `F` have reachable ray-exit anchors.
* `hconn` — ordinary within-`F` connectivity, used to chain those local steps.

The wrappers here make those inputs explicit for dart-dual-cut, subtype, common-box, and Peierls
contour-count connectivity.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F Λ Λd : Finset (Fin 2 → ℤ)}

/-- Pairwise dart reachability from ray-exit anchoring data. -/
theorem dartReachable_of_rayExitAnchored
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hstep : ∀ a b : {x : Fin 2 → ℤ // x ∈ F}, (latticeGraph 2).Adj a.1 b.1 →
      DartReachable F (rayExitAnchorDartMap F a) (rayExitAnchorDartMap F b))
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b)
    (d e : BoundaryDart F) : DartReachable F d e :=
  dartReachable_of_anchored (rayExitAnchorDartMap F) hanchor hstep hconn d e

/-- The ambient dart dual cut is edge-connected from ray-exit anchoring data. -/
theorem dartDualCut_isEdgeConnected_of_rayExitAnchored
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hstep : ∀ a b : {x : Fin 2 → ℤ // x ∈ F}, (latticeGraph 2).Adj a.1 b.1 →
      DartReachable F (rayExitAnchorDartMap F a) (rayExitAnchorDartMap F b))
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b) :
    IsEdgeConnected (dartDualCut F) :=
  dartDualCut_isEdgeConnected_of_anchored (rayExitAnchorDartMap F) hanchor hstep hconn

/-- The subtype-lifted dual cut is edge-connected from ray-exit anchoring data. -/
theorem dualCutSub_isEdgeConnected_of_rayExitAnchored
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hstep : ∀ a b : {x : Fin 2 → ℤ // x ∈ F}, (latticeGraph 2).Adj a.1 b.1 →
      DartReachable F (rayExitAnchorDartMap F a) (rayExitAnchorDartMap F b))
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b) :
    IsEdgeConnected (dualCutSub F) :=
  dualCutSub_isEdgeConnected_of_anchored (rayExitAnchorDartMap F) hanchor hstep hconn

/-- The common-box dual cut is edge-connected from ray-exit anchoring data. -/
theorem dualCutInBox_isEdgeConnected_of_rayExitAnchored (hsub : dualSupport F ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hstep : ∀ a b : {x : Fin 2 → ℤ // x ∈ F}, (latticeGraph 2).Adj a.1 b.1 →
      DartReachable F (rayExitAnchorDartMap F a) (rayExitAnchorDartMap F b))
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_anchored hsub (rayExitAnchorDartMap F) hanchor hstep hconn

/-- **The Peierls contour count from ray-exit anchored dart reachability data**: this specializes
`peierls_contour_count_anchored` by fixing the anchor map of each droplet to
`rayExitAnchorDartMap`.  The same-left-site anchoring and one-edge step obligations remain explicit
inputs, while the count consumer no longer quantifies over an arbitrary `φ`. -/
theorem peierls_contour_count_rayExit_anchored {i : Fin 2 → ℤ} {g : ↑Λ} {r : ℕ}
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
          DartReachable (S.image Subtype.val)
            (rayExitAnchorDartMap (S.image Subtype.val) a)
            (rayExitAnchorDartMap (S.image Subtype.val) b)) ∧
      (∀ a ∈ S.image Subtype.val, ∀ b ∈ S.image Subtype.val,
        ReachableWithin (latticeGraph 2) (S.image Subtype.val) a b))
    (hr : ∀ S ∈ D, (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) S).card = r) :
    D.card ≤ r * (2 * 2) ^ (2 * r) :=
  peierls_contour_count_anchored hpre D hdual hi hne hg
    (fun S hS => ⟨rayExitAnchorDartMap (S.image Subtype.val), hdata S hS⟩) hr

end IsingModel

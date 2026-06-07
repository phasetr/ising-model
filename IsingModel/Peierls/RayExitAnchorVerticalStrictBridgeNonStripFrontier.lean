import IsingModel.Peierls.RayExitAnchorVerticalStrictBridgeNonStrip

/-!
# Frontier-split inputs for non-strip strict ray-exit gaps (FV §3.7.2)

`RayExitAnchorVerticalStrictBridgeNonStrip.lean` gives a canonical first re-entry dart for each
non-strip genuine gap.  This file refines the remaining non-strip bridge-gap input so that later
geometry only has to connect through that first frontier dart.

For lower-exits-first gaps, the input is split into a chain from the endpoint bridge dart to the
lower first re-entry dart, followed by a chain from that frontier dart to the upper ray-exit
anchor.  For upper-exits-first gaps, the orientation matches the existing upper route: lower
ray-exit anchor to the upper first re-entry dart, then that frontier dart to the upper endpoint
bridge.

This is an interface reduction.  It does not prove the local `nextDart` frontier chain and does
not assume monotonicity after the first exit.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F Λ Λd : Finset (Fin 2 → ℤ)}

/-! ## Frontier-split non-strip chain data -/

/-- Lower-exits-first non-strip chain data split at the first lower-ray re-entry dart. -/
def RayExitVerticalStrictLtBridgeFrontierChain (F : Finset (Fin 2 → ℤ)) : Prop :=
  ∀ a b : {x : Fin 2 → ℤ // x ∈ F},
    (hup : b.1 = a.1 + unitVec2 1) →
      (hlt : rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2) →
        (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2) →
          (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) →
            DartReachable F (rayExitVerticalStrictLtBridgeDart a b hup hlt)
              (rayExitVerticalStrictLtFrontierDart a b hgap hnon) ∧
            DartReachable F (rayExitVerticalStrictLtFrontierDart a b hgap hnon)
              (rayExitAnchorDartMap F b)

/-- Upper-exits-first non-strip chain data split at the first upper-ray re-entry dart. -/
def RayExitVerticalStrictGtBridgeFrontierChain (F : Finset (Fin 2 → ℤ)) : Prop :=
  ∀ a b : {x : Fin 2 → ℤ // x ∈ F},
    (hup : b.1 = a.1 + unitVec2 1) →
      (hgt : rayExitIndex F b.1 b.2 < rayExitIndex F a.1 a.2) →
        (hgap : rayExitIndex F b.1 b.2 + 1 < rayExitIndex F a.1 a.2) →
          (hnon : ¬ RayExitVerticalStrictGtGapStrip F a b) →
            DartReachable F (rayExitAnchorDartMap F a)
              (rayExitVerticalStrictGtFrontierDart a b hgap hnon) ∧
            DartReachable F (rayExitVerticalStrictGtFrontierDart a b hgap hnon)
              (rayExitVerticalStrictGtBridgeDart a b hup hgt)

/-- The frontier-split form of the non-strip bridge-gap input. -/
def RayExitVerticalStrictBridgeFrontierChainStep (F : Finset (Fin 2 → ℤ)) : Prop :=
  RayExitVerticalStrictLtBridgeFrontierChain F ∧
    RayExitVerticalStrictGtBridgeFrontierChain F

/-- Lower frontier-split data recover the lower non-strip chain input by transitivity through the
first lower-ray re-entry dart. -/
theorem rayExitVerticalStrictLtBridgeNonStripGapChain_of_frontierChain
    (hfrontier : RayExitVerticalStrictLtBridgeFrontierChain F) :
    RayExitVerticalStrictLtBridgeNonStripGapChain F := by
  intro a b hup hlt hgap hnon
  exact ((hfrontier a b hup hlt hgap hnon).1).trans
    ((hfrontier a b hup hlt hgap hnon).2)

/-- Upper frontier-split data recover the upper non-strip chain input by transitivity through the
first upper-ray re-entry dart. -/
theorem rayExitVerticalStrictGtBridgeNonStripGapChain_of_frontierChain
    (hfrontier : RayExitVerticalStrictGtBridgeFrontierChain F) :
    RayExitVerticalStrictGtBridgeNonStripGapChain F := by
  intro a b hup hgt hgap hnon
  exact ((hfrontier a b hup hgt hgap hnon).1).trans
    ((hfrontier a b hup hgt hgap hnon).2)

/-- Frontier-split data recover the existing non-strip bridge-gap input. -/
theorem rayExitVerticalStrictBridgeNonStripGapChainStep_of_frontierChainStep
    (hfrontier : RayExitVerticalStrictBridgeFrontierChainStep F) :
    RayExitVerticalStrictBridgeNonStripGapChainStep F :=
  ⟨rayExitVerticalStrictLtBridgeNonStripGapChain_of_frontierChain hfrontier.1,
    rayExitVerticalStrictGtBridgeNonStripGapChain_of_frontierChain hfrontier.2⟩

/-! ## Route wrappers -/

/-- Pairwise dart reachability from frontier-split non-strip data and within-`F` connectivity. -/
theorem dartReachable_of_rayExitVerticalStrictBridgeFrontierChain
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hfrontier : RayExitVerticalStrictBridgeFrontierChainStep F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b)
    (d e : BoundaryDart F) : DartReachable F d e :=
  dartReachable_of_rayExitVerticalStrictBridgeNonStripGapChain hanchor
    (rayExitVerticalStrictBridgeNonStripGapChainStep_of_frontierChainStep hfrontier) hconn d e

/-- The common-box dual cut is edge-connected from frontier-split non-strip data. -/
theorem dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierChain
    (hsub : dualSupport F ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hfrontier : RayExitVerticalStrictBridgeFrontierChainStep F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeNonStripGapChain hsub hanchor
    (rayExitVerticalStrictBridgeNonStripGapChainStep_of_frontierChainStep hfrontier) hconn

/-- **The Peierls contour count from frontier-split non-strip strict ray-exit data**: the remaining
vertical input is factored through the first re-entry darts. -/
theorem peierls_contour_count_rayExit_verticalStrictBridgeFrontierChain
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
      RayExitVerticalStrictBridgeFrontierChainStep (S.image Subtype.val) ∧
      (∀ a ∈ S.image Subtype.val, ∀ b ∈ S.image Subtype.val,
        ReachableWithin (latticeGraph 2) (S.image Subtype.val) a b))
    (hr : ∀ S ∈ D, (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) S).card = r) :
    D.card ≤ r * (2 * 2) ^ (2 * r) :=
  peierls_contour_count_rayExit_verticalStrictBridgeNonStripGapChain hpre D hdual hi hne hg
    (fun S hS =>
      ⟨(hdata S hS).1,
        rayExitVerticalStrictBridgeNonStripGapChainStep_of_frontierChainStep
          (hdata S hS).2.1,
        (hdata S hS).2.2⟩)
    hr

/-- Pairwise dart reachability from frontier-split non-strip data and connectedness of the
underlying box droplet. -/
theorem dartReachable_of_rayExitVerticalStrictBridgeFrontierChain_connected {S : Finset ↑Λ}
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hfrontier : RayExitVerticalStrictBridgeFrontierChainStep (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (d e : BoundaryDart (S.image Subtype.val)) :
    DartReachable (S.image Subtype.val) d e :=
  dartReachable_of_rayExitVerticalStrictBridgeNonStripGapChain_connected hanchor
    (rayExitVerticalStrictBridgeNonStripGapChainStep_of_frontierChainStep hfrontier) hconn d e

/-- The common-box dual cut is edge-connected from frontier-split non-strip data and connectedness
of the underlying box droplet. -/
theorem dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierChain_connected
    {S : Finset ↑Λ}
    (hsub : dualSupport (S.image Subtype.val) ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hfrontier : RayExitVerticalStrictBridgeFrontierChainStep (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeNonStripGapChain_connected hsub
    hanchor (rayExitVerticalStrictBridgeNonStripGapChainStep_of_frontierChainStep hfrontier)
    hconn

/-- **The Peierls contour count from frontier-split non-strip strict ray-exit data and connected
droplets**: ordinary within-image connectivity is supplied from `IsConnectedDroplet`. -/
theorem peierls_contour_count_rayExit_verticalStrictBridgeFrontierChain_connected
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
      RayExitVerticalStrictBridgeFrontierChainStep (S.image Subtype.val) ∧
      IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (hr : ∀ S ∈ D, (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) S).card = r) :
    D.card ≤ r * (2 * 2) ^ (2 * r) :=
  peierls_contour_count_rayExit_verticalStrictBridgeNonStripGapChain_connected hpre D hdual hi
    hne hg
    (fun S hS =>
      ⟨(hdata S hS).1,
        rayExitVerticalStrictBridgeNonStripGapChainStep_of_frontierChainStep
          (hdata S hS).2.1,
        (hdata S hS).2.2⟩)
    hr

end IsingModel

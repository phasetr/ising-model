import IsingModel.Peierls.RayExitAnchorVerticalStrictBridge

/-!
# Bridge-chain inputs for strict vertical ray-exit steps (FV §3.7.2)

`RayExitAnchorVerticalStrictBridge.lean` constructs the first forced boundary dart at the endpoint
of each ordered strict vertical case.  This file uses those endpoint bridges to restate the
remaining ordered obligations as post-bridge chain inputs:

* in the lower-exits-first case, it remains to connect the lower-first bridge dart to the upper
  ray-exit anchor;
* in the upper-exits-first case, it remains to connect the lower ray-exit anchor to the
  upper-first bridge dart.

The endpoint bridge lemmas then recover the ordered strict vertical obligations by transitivity of
`DartReachable`.  This is still an interface reduction; it does not prove the remaining
post-bridge frontier chains.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F Λ Λd : Finset (Fin 2 → ℤ)}

/-- The lower-exits-first post-bridge chain obligation: after the forced lower endpoint bridge,
connect that bridge dart to the upper ray-exit anchor. -/
def RayExitVerticalStrictLtBridgeChain (F : Finset (Fin 2 → ℤ)) : Prop :=
  ∀ a b : {x : Fin 2 → ℤ // x ∈ F},
    (hup : b.1 = a.1 + unitVec2 1) →
      (hlt : rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2) →
        DartReachable F (rayExitVerticalStrictLtBridgeDart a b hup hlt)
          (rayExitAnchorDartMap F b)

/-- The upper-exits-first post-bridge chain obligation: connect the lower ray-exit anchor to the
forced upper endpoint bridge. -/
def RayExitVerticalStrictGtBridgeChain (F : Finset (Fin 2 → ℤ)) : Prop :=
  ∀ a b : {x : Fin 2 → ℤ // x ∈ F},
    (hup : b.1 = a.1 + unitVec2 1) →
      (hgt : rayExitIndex F b.1 b.2 < rayExitIndex F a.1 a.2) →
        DartReachable F (rayExitAnchorDartMap F a)
          (rayExitVerticalStrictGtBridgeDart a b hup hgt)

/-- The bridge-chain form of the ordered strict vertical ray-exit obligation. -/
def RayExitVerticalStrictBridgeChainStep (F : Finset (Fin 2 → ℤ)) : Prop :=
  RayExitVerticalStrictLtBridgeChain F ∧ RayExitVerticalStrictGtBridgeChain F

/-- A lower-exits-first post-bridge chain recovers the lower-exits-first ordered strict step. -/
theorem rayExitVerticalStrictLtStep_of_bridgeChain
    (hchain : RayExitVerticalStrictLtBridgeChain F) :
    RayExitVerticalStrictLtStep F := by
  intro a b hup hlt
  exact (dartReachable_rayExitAnchorDartMap_ltBridgeDart a b hup hlt).trans
    (hchain a b hup hlt)

/-- An upper-exits-first post-bridge chain recovers the upper-exits-first ordered strict step. -/
theorem rayExitVerticalStrictGtStep_of_bridgeChain
    (hchain : RayExitVerticalStrictGtBridgeChain F) :
    RayExitVerticalStrictGtStep F := by
  intro a b hup hgt
  exact (hchain a b hup hgt).trans
    (dartReachable_rayExitAnchorDartMap_gtBridgeDart a b hup hgt).symm

/-- Bridge-chain data recover the ordered strict vertical ray-exit obligation. -/
theorem rayExitVerticalStrictOrderedStep_of_bridgeChainStep
    (hchain : RayExitVerticalStrictBridgeChainStep F) :
    RayExitVerticalStrictOrderedStep F :=
  ⟨rayExitVerticalStrictLtStep_of_bridgeChain hchain.1,
    rayExitVerticalStrictGtStep_of_bridgeChain hchain.2⟩

/-- Pairwise dart reachability from ray-exit anchoring, bridge-chain strict vertical data, and
within-`F` connectivity. -/
theorem dartReachable_of_rayExitVerticalStrictBridgeChain
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hchain : RayExitVerticalStrictBridgeChainStep F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b)
    (d e : BoundaryDart F) : DartReachable F d e :=
  dartReachable_of_rayExitVerticalStrictOrdered hanchor
    (rayExitVerticalStrictOrderedStep_of_bridgeChainStep hchain) hconn d e

/-- The common-box dual cut is edge-connected from bridge-chain strict vertical data. -/
theorem dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeChain
    (hsub : dualSupport F ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hchain : RayExitVerticalStrictBridgeChainStep F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictOrdered hsub hanchor
    (rayExitVerticalStrictOrderedStep_of_bridgeChainStep hchain) hconn

/-- **The Peierls contour count from bridge-chain strict ray-exit data**: endpoint bridge darts
are automatic, and the remaining vertical input starts after those bridges. -/
theorem peierls_contour_count_rayExit_verticalStrictBridgeChain
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
      RayExitVerticalStrictBridgeChainStep (S.image Subtype.val) ∧
      (∀ a ∈ S.image Subtype.val, ∀ b ∈ S.image Subtype.val,
        ReachableWithin (latticeGraph 2) (S.image Subtype.val) a b))
    (hr : ∀ S ∈ D, (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) S).card = r) :
    D.card ≤ r * (2 * 2) ^ (2 * r) :=
  peierls_contour_count_rayExit_verticalStrictOrdered hpre D hdual hi hne hg
    (fun S hS =>
      ⟨(hdata S hS).1,
        rayExitVerticalStrictOrderedStep_of_bridgeChainStep (hdata S hS).2.1,
        (hdata S hS).2.2⟩)
    hr

/-- Pairwise dart reachability from bridge-chain strict vertical data and connectedness of the
underlying box droplet. -/
theorem dartReachable_of_rayExitVerticalStrictBridgeChain_connected {S : Finset ↑Λ}
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hchain : RayExitVerticalStrictBridgeChainStep (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (d e : BoundaryDart (S.image Subtype.val)) :
    DartReachable (S.image Subtype.val) d e :=
  dartReachable_of_rayExitVerticalStrictOrdered_connected hanchor
    (rayExitVerticalStrictOrderedStep_of_bridgeChainStep hchain) hconn d e

/-- The common-box dual cut is edge-connected from bridge-chain strict vertical data and
connectedness of the underlying box droplet. -/
theorem dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeChain_connected
    {S : Finset ↑Λ}
    (hsub : dualSupport (S.image Subtype.val) ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hchain : RayExitVerticalStrictBridgeChainStep (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictOrdered_connected hsub hanchor
    (rayExitVerticalStrictOrderedStep_of_bridgeChainStep hchain) hconn

/-- **The Peierls contour count from bridge-chain strict ray-exit data and connected droplets**:
endpoint bridge darts are automatic, and ordinary within-image connectivity is supplied from
`IsConnectedDroplet`. -/
theorem peierls_contour_count_rayExit_verticalStrictBridgeChain_connected
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
      RayExitVerticalStrictBridgeChainStep (S.image Subtype.val) ∧
      IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (hr : ∀ S ∈ D, (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) S).card = r) :
    D.card ≤ r * (2 * 2) ^ (2 * r) :=
  peierls_contour_count_rayExit_verticalStrictOrdered_connected hpre D hdual hi hne hg
    (fun S hS =>
      ⟨(hdata S hS).1,
        rayExitVerticalStrictOrderedStep_of_bridgeChainStep (hdata S hS).2.1,
        (hdata S hS).2.2⟩)
    hr

end IsingModel

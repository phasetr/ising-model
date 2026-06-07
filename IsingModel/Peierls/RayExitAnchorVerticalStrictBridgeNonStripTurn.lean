import IsingModel.Peierls.RayExitAnchorVerticalStrictBridgeNonStripNextDart

/-!
# Turn-certificate inputs for non-strip strict ray-exit frontier chains (FV §3.7.2)

`RayExitAnchorVerticalStrictBridgeNonStripNextDart.lean` reduces the remaining non-strip
frontier-chain obligations to explicit forward `nextDart` iterate witnesses.  This file refines
that input by naming the local turn certificates which compute each `nextDart` step.

The generic `NextDartTurnStep` records whether the traversal turns left, goes straight, or turns
right at a dart.  `NextDartTurnChain` is a finite chain of such local certificates.  It recovers a
forward `nextDart` iterate witness, so the stricter input reuses the #3768 route/count wrappers.

This is still an interface reduction: it does not yet prove which concrete turn occurs along the
non-strip frontier legs.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F Λ Λd : Finset (Fin 2 → ℤ)}

/-! ## Local turn certificates -/

/-- A one-step certificate for computing `BoundaryDart.nextDart` from the local turn rule. -/
inductive NextDartTurnStep (d : BoundaryDart F) : BoundaryDart F → Prop
  | turnLeft (h : ValidAt F d.head d.dir.turnLeft) :
      NextDartTurnStep d ⟨d.head, d.dir.turnLeft, h.1, h.2⟩
  | straight (hL : ¬ ValidAt F d.head d.dir.turnLeft) (hS : ValidAt F d.head d.dir) :
      NextDartTurnStep d ⟨d.head, d.dir, hS.1, hS.2⟩
  | turnRight (hL : ¬ ValidAt F d.head d.dir.turnLeft)
      (hS : ¬ ValidAt F d.head d.dir) :
      NextDartTurnStep d
        ⟨d.head, d.dir.turnRight, (right_valid_of_not_left_not_straight d hL hS).1,
          (right_valid_of_not_left_not_straight d hL hS).2⟩

/-- A certified local turn step is exactly a `nextDart` step. -/
theorem nextDart_eq_of_turnStep {d e : BoundaryDart F} (hstep : NextDartTurnStep d e) :
    d.nextDart = e := by
  cases hstep with
  | turnLeft h =>
      exact nextDart_eq_turnLeft d h
  | straight hL hS =>
      exact nextDart_eq_straight d hL hS
  | turnRight hL hS =>
      exact nextDart_eq_turnRight d hL hS

/-- A finite chain of local turn certificates from one boundary dart to another. -/
inductive NextDartTurnChain : BoundaryDart F → BoundaryDart F → Prop
  | refl (d : BoundaryDart F) : NextDartTurnChain d d
  | snoc {d e f : BoundaryDart F}
      (hchain : NextDartTurnChain d e) (hstep : NextDartTurnStep e f) :
      NextDartTurnChain d f

/-- A turn-certificate chain gives an explicit forward `nextDart` iterate witness. -/
theorem exists_nextDart_iterate_eq_of_turnChain {d e : BoundaryDart F}
    (hchain : NextDartTurnChain d e) :
    ∃ n : ℕ, (BoundaryDart.nextDart^[n]) d = e := by
  induction hchain with
  | refl =>
      exact ⟨0, rfl⟩
  | snoc hchain hstep ih =>
      obtain ⟨n, hn⟩ := ih
      refine ⟨n + 1, ?_⟩
      rw [Nat.add_one, Function.iterate_succ_apply', hn]
      exact nextDart_eq_of_turnStep hstep

/-- A turn-certificate chain gives dart reachability directly via the #3768 iterate API. -/
theorem dartReachable_of_turnChain {d e : BoundaryDart F}
    (hchain : NextDartTurnChain d e) : DartReachable F d e := by
  obtain ⟨n, hn⟩ := exists_nextDart_iterate_eq_of_turnChain hchain
  exact dartReachable_of_nextDart_iterate_eq hn

/-! ## Turn-certificate non-strip chain data -/

/-- Lower-exits-first non-strip data in which both frontier-split legs are local turn chains. -/
def RayExitVerticalStrictLtBridgeFrontierTurnChain (F : Finset (Fin 2 → ℤ)) : Prop :=
  ∀ a b : {x : Fin 2 → ℤ // x ∈ F},
    (hup : b.1 = a.1 + unitVec2 1) →
      (hlt : rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2) →
        (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2) →
          (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) →
            NextDartTurnChain
                (rayExitVerticalStrictLtBridgeDart a b hup hlt)
                (rayExitVerticalStrictLtFrontierDart a b hgap hnon) ∧
            NextDartTurnChain
                (rayExitVerticalStrictLtFrontierDart a b hgap hnon)
                (rayExitAnchorDartMap F b)

/-- Upper-exits-first non-strip data in which both frontier-split legs are local turn chains. -/
def RayExitVerticalStrictGtBridgeFrontierTurnChain (F : Finset (Fin 2 → ℤ)) : Prop :=
  ∀ a b : {x : Fin 2 → ℤ // x ∈ F},
    (hup : b.1 = a.1 + unitVec2 1) →
      (hgt : rayExitIndex F b.1 b.2 < rayExitIndex F a.1 a.2) →
        (hgap : rayExitIndex F b.1 b.2 + 1 < rayExitIndex F a.1 a.2) →
          (hnon : ¬ RayExitVerticalStrictGtGapStrip F a b) →
            NextDartTurnChain
                (rayExitAnchorDartMap F a)
                (rayExitVerticalStrictGtFrontierDart a b hgap hnon) ∧
            NextDartTurnChain
                (rayExitVerticalStrictGtFrontierDart a b hgap hnon)
                (rayExitVerticalStrictGtBridgeDart a b hup hgt)

/-- The turn-certificate form of the non-strip frontier-chain input. -/
def RayExitVerticalStrictBridgeFrontierTurnChainStep (F : Finset (Fin 2 → ℤ)) : Prop :=
  RayExitVerticalStrictLtBridgeFrontierTurnChain F ∧
    RayExitVerticalStrictGtBridgeFrontierTurnChain F

/-- Lower turn-chain data recover the lower NextDart-split input. -/
theorem rayExitVerticalStrictLtBridgeFrontierNextDartChain_of_turnChain
    (hturn : RayExitVerticalStrictLtBridgeFrontierTurnChain F) :
    RayExitVerticalStrictLtBridgeFrontierNextDartChain F := by
  intro a b hup hlt hgap hnon
  obtain ⟨h₁, h₂⟩ := hturn a b hup hlt hgap hnon
  exact ⟨exists_nextDart_iterate_eq_of_turnChain h₁,
    exists_nextDart_iterate_eq_of_turnChain h₂⟩

/-- Upper turn-chain data recover the upper NextDart-split input. -/
theorem rayExitVerticalStrictGtBridgeFrontierNextDartChain_of_turnChain
    (hturn : RayExitVerticalStrictGtBridgeFrontierTurnChain F) :
    RayExitVerticalStrictGtBridgeFrontierNextDartChain F := by
  intro a b hup hgt hgap hnon
  obtain ⟨h₁, h₂⟩ := hturn a b hup hgt hgap hnon
  exact ⟨exists_nextDart_iterate_eq_of_turnChain h₁,
    exists_nextDart_iterate_eq_of_turnChain h₂⟩

/-- Turn-chain data recover the #3768 NextDart-split input. -/
theorem rayExitVerticalStrictBridgeFrontierNextDartChainStep_of_turnChainStep
    (hturn : RayExitVerticalStrictBridgeFrontierTurnChainStep F) :
    RayExitVerticalStrictBridgeFrontierNextDartChainStep F :=
  ⟨rayExitVerticalStrictLtBridgeFrontierNextDartChain_of_turnChain hturn.1,
    rayExitVerticalStrictGtBridgeFrontierNextDartChain_of_turnChain hturn.2⟩

/-! ## Route wrappers -/

/-- Pairwise dart reachability from turn-chain non-strip data and within-`F` connectivity. -/
theorem dartReachable_of_rayExitVerticalStrictBridgeFrontierTurnChain
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hturn : RayExitVerticalStrictBridgeFrontierTurnChainStep F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b)
    (d e : BoundaryDart F) : DartReachable F d e :=
  dartReachable_of_rayExitVerticalStrictBridgeFrontierNextDartChain hanchor
    (rayExitVerticalStrictBridgeFrontierNextDartChainStep_of_turnChainStep hturn)
    hconn d e

/-- The common-box dual cut is edge-connected from turn-chain non-strip data. -/
theorem dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierTurnChain
    (hsub : dualSupport F ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hturn : RayExitVerticalStrictBridgeFrontierTurnChainStep F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierNextDartChain hsub
    hanchor (rayExitVerticalStrictBridgeFrontierNextDartChainStep_of_turnChainStep hturn)
    hconn

/-- **The Peierls contour count from turn-chain non-strip strict ray-exit data**: each
frontier-split leg is supplied by local turn certificates. -/
theorem peierls_contour_count_rayExit_verticalStrictBridgeFrontierTurnChain
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
      RayExitVerticalStrictBridgeFrontierTurnChainStep (S.image Subtype.val) ∧
      (∀ a ∈ S.image Subtype.val, ∀ b ∈ S.image Subtype.val,
        ReachableWithin (latticeGraph 2) (S.image Subtype.val) a b))
    (hr : ∀ S ∈ D, (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) S).card = r) :
    D.card ≤ r * (2 * 2) ^ (2 * r) :=
  peierls_contour_count_rayExit_verticalStrictBridgeFrontierNextDartChain hpre D hdual hi
    hne hg
    (fun S hS =>
      ⟨(hdata S hS).1,
        rayExitVerticalStrictBridgeFrontierNextDartChainStep_of_turnChainStep
          (hdata S hS).2.1,
        (hdata S hS).2.2⟩)
    hr

/-- Pairwise dart reachability from turn-chain non-strip data and connectedness of the underlying
box droplet. -/
theorem dartReachable_of_rayExitVerticalStrictBridgeFrontierTurnChain_connected
    {S : Finset ↑Λ}
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hturn : RayExitVerticalStrictBridgeFrontierTurnChainStep (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (d e : BoundaryDart (S.image Subtype.val)) :
    DartReachable (S.image Subtype.val) d e :=
  dartReachable_of_rayExitVerticalStrictBridgeFrontierNextDartChain_connected hanchor
    (rayExitVerticalStrictBridgeFrontierNextDartChainStep_of_turnChainStep hturn)
    hconn d e

/-- The common-box dual cut is edge-connected from turn-chain non-strip data and connectedness of
the underlying box droplet. -/
theorem dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierTurnChain_connected
    {S : Finset ↑Λ}
    (hsub : dualSupport (S.image Subtype.val) ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hturn : RayExitVerticalStrictBridgeFrontierTurnChainStep (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierNextDartChain_connected hsub
    hanchor (rayExitVerticalStrictBridgeFrontierNextDartChainStep_of_turnChainStep hturn)
    hconn

/-- **The Peierls contour count from turn-chain non-strip strict ray-exit data and connected
droplets**: ordinary within-image connectivity is supplied from `IsConnectedDroplet`. -/
theorem peierls_contour_count_rayExit_verticalStrictBridgeFrontierTurnChain_connected
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
      RayExitVerticalStrictBridgeFrontierTurnChainStep (S.image Subtype.val) ∧
      IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (hr : ∀ S ∈ D, (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) S).card = r) :
    D.card ≤ r * (2 * 2) ^ (2 * r) :=
  peierls_contour_count_rayExit_verticalStrictBridgeFrontierNextDartChain_connected hpre D
    hdual hi hne hg
    (fun S hS =>
      ⟨(hdata S hS).1,
        rayExitVerticalStrictBridgeFrontierNextDartChainStep_of_turnChainStep
          (hdata S hS).2.1,
        (hdata S hS).2.2⟩)
    hr

end IsingModel

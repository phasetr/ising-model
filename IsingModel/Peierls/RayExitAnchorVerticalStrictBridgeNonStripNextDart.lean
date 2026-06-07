import IsingModel.Peierls.RayExitAnchorVerticalStrictBridgeNonStripFrontier

/-!
# NextDart inputs for non-strip strict ray-exit frontier chains (FV §3.7.2)

`RayExitAnchorVerticalStrictBridgeNonStripFrontier.lean` splits each remaining non-strip gap chain
through the first re-entry dart.  This file refines those split legs to forward `nextDart`
iterate witnesses and proves that such witnesses give the required `DartReachable` chains
directly, without routing through `SameOrbit` or `ContactMove`.

This is still an interface reduction: it names the next local frontier-chain target in terms of
`nextDart` iterates, but it does not yet prove which local turn occurs at each step.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F Λ Λd : Finset (Fin 2 → ℤ)}

/-! ## Direct nextDart-to-DartReachable API -/

/-- A boundary dart reaches every forward `nextDart` iterate in the dual-cut reachability
relation.  This is the direct `DartReachable` form of forward traversal; it does not pass through
`SameOrbit`. -/
theorem dartReachable_nextDart_iterate (d : BoundaryDart F) (n : ℕ) :
    DartReachable F d ((BoundaryDart.nextDart^[n]) d) := by
  induction n with
  | zero =>
      exact DartReachable.refl d
  | succ n ih =>
      rw [Nat.add_one, Function.iterate_succ_apply']
      exact ih.trans (dartReachable_nextDart ((BoundaryDart.nextDart^[n]) d))

/-- If a forward `nextDart` iterate of `d` is `e`, then `d` reaches `e` in the dual-cut
reachability relation. -/
theorem dartReachable_of_nextDart_iterate_eq {d e : BoundaryDart F} {n : ℕ}
    (h : (BoundaryDart.nextDart^[n]) d = e) : DartReachable F d e := by
  rw [← h]
  exact dartReachable_nextDart_iterate d n

/-! ## NextDart-split non-strip chain data -/

/-- Lower-exits-first non-strip data in which both frontier-split legs are forward `nextDart`
iterates. -/
def RayExitVerticalStrictLtBridgeFrontierNextDartChain (F : Finset (Fin 2 → ℤ)) : Prop :=
  ∀ a b : {x : Fin 2 → ℤ // x ∈ F},
    (hup : b.1 = a.1 + unitVec2 1) →
      (hlt : rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2) →
        (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2) →
          (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) →
            (∃ n : ℕ,
              (BoundaryDart.nextDart^[n])
                  (rayExitVerticalStrictLtBridgeDart a b hup hlt) =
                rayExitVerticalStrictLtFrontierDart a b hgap hnon) ∧
            (∃ n : ℕ,
              (BoundaryDart.nextDart^[n])
                  (rayExitVerticalStrictLtFrontierDart a b hgap hnon) =
                rayExitAnchorDartMap F b)

/-- Upper-exits-first non-strip data in which both frontier-split legs are forward `nextDart`
iterates. -/
def RayExitVerticalStrictGtBridgeFrontierNextDartChain (F : Finset (Fin 2 → ℤ)) : Prop :=
  ∀ a b : {x : Fin 2 → ℤ // x ∈ F},
    (hup : b.1 = a.1 + unitVec2 1) →
      (hgt : rayExitIndex F b.1 b.2 < rayExitIndex F a.1 a.2) →
        (hgap : rayExitIndex F b.1 b.2 + 1 < rayExitIndex F a.1 a.2) →
          (hnon : ¬ RayExitVerticalStrictGtGapStrip F a b) →
            (∃ n : ℕ,
              (BoundaryDart.nextDart^[n])
                  (rayExitAnchorDartMap F a) =
                rayExitVerticalStrictGtFrontierDart a b hgap hnon) ∧
            (∃ n : ℕ,
              (BoundaryDart.nextDart^[n])
                  (rayExitVerticalStrictGtFrontierDart a b hgap hnon) =
                rayExitVerticalStrictGtBridgeDart a b hup hgt)

/-- The nextDart-split form of the non-strip frontier-chain input. -/
def RayExitVerticalStrictBridgeFrontierNextDartChainStep (F : Finset (Fin 2 → ℤ)) : Prop :=
  RayExitVerticalStrictLtBridgeFrontierNextDartChain F ∧
    RayExitVerticalStrictGtBridgeFrontierNextDartChain F

/-- Lower nextDart-split data recover the lower frontier-split input. -/
theorem rayExitVerticalStrictLtBridgeFrontierChain_of_nextDartChain
    (hnext : RayExitVerticalStrictLtBridgeFrontierNextDartChain F) :
    RayExitVerticalStrictLtBridgeFrontierChain F := by
  intro a b hup hlt hgap hnon
  obtain ⟨⟨_, h₁⟩, ⟨_, h₂⟩⟩ := hnext a b hup hlt hgap hnon
  exact ⟨dartReachable_of_nextDart_iterate_eq h₁,
    dartReachable_of_nextDart_iterate_eq h₂⟩

/-- Upper nextDart-split data recover the upper frontier-split input. -/
theorem rayExitVerticalStrictGtBridgeFrontierChain_of_nextDartChain
    (hnext : RayExitVerticalStrictGtBridgeFrontierNextDartChain F) :
    RayExitVerticalStrictGtBridgeFrontierChain F := by
  intro a b hup hgt hgap hnon
  obtain ⟨⟨_, h₁⟩, ⟨_, h₂⟩⟩ := hnext a b hup hgt hgap hnon
  exact ⟨dartReachable_of_nextDart_iterate_eq h₁,
    dartReachable_of_nextDart_iterate_eq h₂⟩

/-- NextDart-split data recover the frontier-split non-strip input. -/
theorem rayExitVerticalStrictBridgeFrontierChainStep_of_nextDartChainStep
    (hnext : RayExitVerticalStrictBridgeFrontierNextDartChainStep F) :
    RayExitVerticalStrictBridgeFrontierChainStep F :=
  ⟨rayExitVerticalStrictLtBridgeFrontierChain_of_nextDartChain hnext.1,
    rayExitVerticalStrictGtBridgeFrontierChain_of_nextDartChain hnext.2⟩

/-! ## Route wrappers -/

/-- Pairwise dart reachability from nextDart-split non-strip data and within-`F` connectivity. -/
theorem dartReachable_of_rayExitVerticalStrictBridgeFrontierNextDartChain
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hnext : RayExitVerticalStrictBridgeFrontierNextDartChainStep F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b)
    (d e : BoundaryDart F) : DartReachable F d e :=
  dartReachable_of_rayExitVerticalStrictBridgeFrontierChain hanchor
    (rayExitVerticalStrictBridgeFrontierChainStep_of_nextDartChainStep hnext) hconn d e

/-- The common-box dual cut is edge-connected from nextDart-split non-strip data. -/
theorem dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierNextDartChain
    (hsub : dualSupport F ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hnext : RayExitVerticalStrictBridgeFrontierNextDartChainStep F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierChain hsub hanchor
    (rayExitVerticalStrictBridgeFrontierChainStep_of_nextDartChainStep hnext) hconn

/-- **The Peierls contour count from nextDart-split non-strip strict ray-exit data**: the
frontier-split legs are supplied as forward `nextDart` iterate witnesses. -/
theorem peierls_contour_count_rayExit_verticalStrictBridgeFrontierNextDartChain
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
      RayExitVerticalStrictBridgeFrontierNextDartChainStep (S.image Subtype.val) ∧
      (∀ a ∈ S.image Subtype.val, ∀ b ∈ S.image Subtype.val,
        ReachableWithin (latticeGraph 2) (S.image Subtype.val) a b))
    (hr : ∀ S ∈ D, (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) S).card = r) :
    D.card ≤ r * (2 * 2) ^ (2 * r) :=
  peierls_contour_count_rayExit_verticalStrictBridgeFrontierChain hpre D hdual hi hne hg
    (fun S hS =>
      ⟨(hdata S hS).1,
        rayExitVerticalStrictBridgeFrontierChainStep_of_nextDartChainStep
          (hdata S hS).2.1,
        (hdata S hS).2.2⟩)
    hr

/-- Pairwise dart reachability from nextDart-split non-strip data and connectedness of the
underlying box droplet. -/
theorem dartReachable_of_rayExitVerticalStrictBridgeFrontierNextDartChain_connected
    {S : Finset ↑Λ}
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hnext : RayExitVerticalStrictBridgeFrontierNextDartChainStep (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (d e : BoundaryDart (S.image Subtype.val)) :
    DartReachable (S.image Subtype.val) d e :=
  dartReachable_of_rayExitVerticalStrictBridgeFrontierChain_connected hanchor
    (rayExitVerticalStrictBridgeFrontierChainStep_of_nextDartChainStep hnext) hconn d e

/-- The common-box dual cut is edge-connected from nextDart-split non-strip data and connectedness
of the underlying box droplet. -/
theorem dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierNextDartChain_connected
    {S : Finset ↑Λ}
    (hsub : dualSupport (S.image Subtype.val) ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hnext : RayExitVerticalStrictBridgeFrontierNextDartChainStep (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeFrontierChain_connected hsub
    hanchor (rayExitVerticalStrictBridgeFrontierChainStep_of_nextDartChainStep hnext) hconn

/-- **The Peierls contour count from nextDart-split non-strip strict ray-exit data and connected
droplets**: ordinary within-image connectivity is supplied from `IsConnectedDroplet`. -/
theorem peierls_contour_count_rayExit_verticalStrictBridgeFrontierNextDartChain_connected
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
      RayExitVerticalStrictBridgeFrontierNextDartChainStep (S.image Subtype.val) ∧
      IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (hr : ∀ S ∈ D, (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) S).card = r) :
    D.card ≤ r * (2 * 2) ^ (2 * r) :=
  peierls_contour_count_rayExit_verticalStrictBridgeFrontierChain_connected hpre D hdual hi
    hne hg
    (fun S hS =>
      ⟨(hdata S hS).1,
        rayExitVerticalStrictBridgeFrontierChainStep_of_nextDartChainStep
          (hdata S hS).2.1,
        (hdata S hS).2.2⟩)
    hr

end IsingModel

import IsingModel.Peierls.RayExitAnchorVerticalStrictBridgeChain

/-!
# Gap-reduced bridge-chain inputs for strict vertical ray-exit steps (FV §3.7.2)

`RayExitAnchorVerticalStrictBridgeChain.lean` reduces the ordered strict vertical ray-exit
obligations to chains starting at the endpoint bridge darts.  This file discharges the
adjacent-index subcase: if the two first-exit indices differ by exactly one, the endpoint bridge
dart already shares a dual vertex with the opposite ray-exit anchor.

Consequently the remaining post-bridge chain input only has to cover genuine gaps:

* lower-exits-first: `rayExitIndex a + 1 < rayExitIndex b`;
* upper-exits-first: `rayExitIndex b + 1 < rayExitIndex a`.

No monotonicity after the first exit is assumed.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F Λ Λd : Finset (Fin 2 → ℤ)}

/-- In the lower-exits-first case, if the upper first-exit index is exactly one more than the
lower one, the lower endpoint bridge dart shares its head with the upper ray-exit anchor. -/
theorem rayExitVerticalStrictLtBridgeDart_terminal_shared_of_succ
    (a b : {x : Fin 2 → ℤ // x ∈ F}) (hup : b.1 = a.1 + unitVec2 1)
    (hlt : rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2)
    (hsucc : rayExitIndex F b.1 b.2 = rayExitIndex F a.1 a.2 + 1) :
    ∃ v : Fin 2 → ℤ,
      v ∈ s((rayExitVerticalStrictLtBridgeDart a b hup hlt).tail,
          (rayExitVerticalStrictLtBridgeDart a b hup hlt).head) ∧
        v ∈ s((rayExitAnchorDartMap F b).tail, (rayExitAnchorDartMap F b).head) := by
  refine ⟨ray0 a.1 (rayExitIndex F a.1 a.2 + 1), ?_, ?_⟩
  · rw [rayExitVerticalStrictLtBridgeDart_head]
    exact Sym2.mem_mk_right _ _
  · have htail : (rayExitAnchorDartMap F b).tail =
        ray0 a.1 (rayExitIndex F a.1 a.2 + 1) := by
      calc
        (rayExitAnchorDartMap F b).tail =
            ray0 b.1 (rayExitIndex F b.1 b.2) - unitVec2 1 := by
              rw [rayExitAnchorDartMap_tail]
        _ = ray0 b.1 (rayExitIndex F a.1 a.2 + 1) - unitVec2 1 := by
              rw [hsucc]
        _ = ray0 (a.1 + unitVec2 1) (rayExitIndex F a.1 a.2 + 1) - unitVec2 1 := by
              rw [hup]
        _ = (ray0 a.1 (rayExitIndex F a.1 a.2 + 1) + unitVec2 1) - unitVec2 1 := by
              rw [ray0_add_unitVec2_one]
        _ = ray0 a.1 (rayExitIndex F a.1 a.2 + 1) :=
              add_unitVec2_sub_unitVec2 _ _
    rw [htail]
    exact Sym2.mem_mk_left _ _

/-- The adjacent-index lower-exits-first post-bridge chain is a single shared-vertex step. -/
theorem dartReachable_ltBridgeDart_rayExitAnchorDartMap_of_succ
    (a b : {x : Fin 2 → ℤ // x ∈ F}) (hup : b.1 = a.1 + unitVec2 1)
    (hlt : rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2)
    (hsucc : rayExitIndex F b.1 b.2 = rayExitIndex F a.1 a.2 + 1) :
    DartReachable F (rayExitVerticalStrictLtBridgeDart a b hup hlt)
      (rayExitAnchorDartMap F b) := by
  obtain ⟨_, hbridge, hanchor⟩ :=
    rayExitVerticalStrictLtBridgeDart_terminal_shared_of_succ a b hup hlt hsucc
  exact dartReachable_of_shared hbridge hanchor

/-- In the upper-exits-first case, if the lower first-exit index is exactly one more than the
upper one, the lower ray-exit anchor shares its head with the upper endpoint bridge dart. -/
theorem rayExitVerticalStrictGtBridgeDart_terminal_shared_of_succ
    (a b : {x : Fin 2 → ℤ // x ∈ F}) (hup : b.1 = a.1 + unitVec2 1)
    (hgt : rayExitIndex F b.1 b.2 < rayExitIndex F a.1 a.2)
    (hsucc : rayExitIndex F a.1 a.2 = rayExitIndex F b.1 b.2 + 1) :
    ∃ v : Fin 2 → ℤ,
      v ∈ s((rayExitAnchorDartMap F a).tail, (rayExitAnchorDartMap F a).head) ∧
        v ∈ s((rayExitVerticalStrictGtBridgeDart a b hup hgt).tail,
          (rayExitVerticalStrictGtBridgeDart a b hup hgt).head) := by
  refine ⟨ray0 a.1 (rayExitIndex F b.1 b.2 + 1), ?_, ?_⟩
  · have hhead : (rayExitAnchorDartMap F a).head =
        ray0 a.1 (rayExitIndex F b.1 b.2 + 1) := by
      rw [rayExitAnchorDartMap_head, hsucc]
    rw [hhead]
    exact Sym2.mem_mk_right _ _
  · rw [rayExitVerticalStrictGtBridgeDart_tail]
    exact Sym2.mem_mk_left _ _

/-- The adjacent-index upper-exits-first post-bridge chain is a single shared-vertex step. -/
theorem dartReachable_rayExitAnchorDartMap_gtBridgeDart_of_succ
    (a b : {x : Fin 2 → ℤ // x ∈ F}) (hup : b.1 = a.1 + unitVec2 1)
    (hgt : rayExitIndex F b.1 b.2 < rayExitIndex F a.1 a.2)
    (hsucc : rayExitIndex F a.1 a.2 = rayExitIndex F b.1 b.2 + 1) :
    DartReachable F (rayExitAnchorDartMap F a)
      (rayExitVerticalStrictGtBridgeDart a b hup hgt) := by
  obtain ⟨_, hanchor, hbridge⟩ :=
    rayExitVerticalStrictGtBridgeDart_terminal_shared_of_succ a b hup hgt hsucc
  exact dartReachable_of_shared hanchor hbridge

/-- Lower-exits-first bridge-chain data only for genuine gaps beyond the adjacent-index case. -/
def RayExitVerticalStrictLtBridgeGapChain (F : Finset (Fin 2 → ℤ)) : Prop :=
  ∀ a b : {x : Fin 2 → ℤ // x ∈ F},
    (hup : b.1 = a.1 + unitVec2 1) →
      (hlt : rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2) →
        rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2 →
          DartReachable F (rayExitVerticalStrictLtBridgeDart a b hup hlt)
            (rayExitAnchorDartMap F b)

/-- Upper-exits-first bridge-chain data only for genuine gaps beyond the adjacent-index case. -/
def RayExitVerticalStrictGtBridgeGapChain (F : Finset (Fin 2 → ℤ)) : Prop :=
  ∀ a b : {x : Fin 2 → ℤ // x ∈ F},
    (hup : b.1 = a.1 + unitVec2 1) →
      (hgt : rayExitIndex F b.1 b.2 < rayExitIndex F a.1 a.2) →
        rayExitIndex F b.1 b.2 + 1 < rayExitIndex F a.1 a.2 →
          DartReachable F (rayExitAnchorDartMap F a)
            (rayExitVerticalStrictGtBridgeDart a b hup hgt)

/-- The gap-reduced form of the strict vertical bridge-chain input. -/
def RayExitVerticalStrictBridgeGapChainStep (F : Finset (Fin 2 → ℤ)) : Prop :=
  RayExitVerticalStrictLtBridgeGapChain F ∧ RayExitVerticalStrictGtBridgeGapChain F

/-- Gap-reduced lower-exits-first data recover the full lower bridge-chain input, because the
adjacent-index case is already a shared-vertex step. -/
theorem rayExitVerticalStrictLtBridgeChain_of_gapChain
    (hgap : RayExitVerticalStrictLtBridgeGapChain F) :
    RayExitVerticalStrictLtBridgeChain F := by
  intro a b hup hlt
  by_cases hsucc : rayExitIndex F b.1 b.2 = rayExitIndex F a.1 a.2 + 1
  · exact dartReachable_ltBridgeDart_rayExitAnchorDartMap_of_succ a b hup hlt hsucc
  · exact hgap a b hup hlt (by omega)

/-- Gap-reduced upper-exits-first data recover the full upper bridge-chain input, because the
adjacent-index case is already a shared-vertex step. -/
theorem rayExitVerticalStrictGtBridgeChain_of_gapChain
    (hgap : RayExitVerticalStrictGtBridgeGapChain F) :
    RayExitVerticalStrictGtBridgeChain F := by
  intro a b hup hgt
  by_cases hsucc : rayExitIndex F a.1 a.2 = rayExitIndex F b.1 b.2 + 1
  · exact dartReachable_rayExitAnchorDartMap_gtBridgeDart_of_succ a b hup hgt hsucc
  · exact hgap a b hup hgt (by omega)

/-- Gap-reduced bridge-chain data recover the full bridge-chain input. -/
theorem rayExitVerticalStrictBridgeChainStep_of_gapChainStep
    (hgap : RayExitVerticalStrictBridgeGapChainStep F) :
    RayExitVerticalStrictBridgeChainStep F :=
  ⟨rayExitVerticalStrictLtBridgeChain_of_gapChain hgap.1,
    rayExitVerticalStrictGtBridgeChain_of_gapChain hgap.2⟩

/-- Pairwise dart reachability from gap-reduced bridge-chain strict vertical data and
within-`F` connectivity. -/
theorem dartReachable_of_rayExitVerticalStrictBridgeGapChain
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hgap : RayExitVerticalStrictBridgeGapChainStep F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b)
    (d e : BoundaryDart F) : DartReachable F d e :=
  dartReachable_of_rayExitVerticalStrictBridgeChain hanchor
    (rayExitVerticalStrictBridgeChainStep_of_gapChainStep hgap) hconn d e

/-- The common-box dual cut is edge-connected from gap-reduced bridge-chain data. -/
theorem dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeGapChain
    (hsub : dualSupport F ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hgap : RayExitVerticalStrictBridgeGapChainStep F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeChain hsub hanchor
    (rayExitVerticalStrictBridgeChainStep_of_gapChainStep hgap) hconn

/-- **The Peierls contour count from gap-reduced strict ray-exit data**: the adjacent-index
post-bridge cases are automatic, and the remaining vertical input starts only at genuine gaps. -/
theorem peierls_contour_count_rayExit_verticalStrictBridgeGapChain
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
      RayExitVerticalStrictBridgeGapChainStep (S.image Subtype.val) ∧
      (∀ a ∈ S.image Subtype.val, ∀ b ∈ S.image Subtype.val,
        ReachableWithin (latticeGraph 2) (S.image Subtype.val) a b))
    (hr : ∀ S ∈ D, (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) S).card = r) :
    D.card ≤ r * (2 * 2) ^ (2 * r) :=
  peierls_contour_count_rayExit_verticalStrictBridgeChain hpre D hdual hi hne hg
    (fun S hS =>
      ⟨(hdata S hS).1,
        rayExitVerticalStrictBridgeChainStep_of_gapChainStep (hdata S hS).2.1,
        (hdata S hS).2.2⟩)
    hr

/-- Pairwise dart reachability from gap-reduced bridge-chain strict vertical data and connectedness
of the underlying box droplet. -/
theorem dartReachable_of_rayExitVerticalStrictBridgeGapChain_connected {S : Finset ↑Λ}
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hgap : RayExitVerticalStrictBridgeGapChainStep (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (d e : BoundaryDart (S.image Subtype.val)) :
    DartReachable (S.image Subtype.val) d e :=
  dartReachable_of_rayExitVerticalStrictBridgeChain_connected hanchor
    (rayExitVerticalStrictBridgeChainStep_of_gapChainStep hgap) hconn d e

/-- The common-box dual cut is edge-connected from gap-reduced bridge-chain data and connectedness
of the underlying box droplet. -/
theorem dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeGapChain_connected
    {S : Finset ↑Λ}
    (hsub : dualSupport (S.image Subtype.val) ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hgap : RayExitVerticalStrictBridgeGapChainStep (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictBridgeChain_connected hsub hanchor
    (rayExitVerticalStrictBridgeChainStep_of_gapChainStep hgap) hconn

/-- **The Peierls contour count from gap-reduced strict ray-exit data and connected droplets**:
the adjacent-index post-bridge cases are automatic, and ordinary within-image connectivity is
supplied from `IsConnectedDroplet`. -/
theorem peierls_contour_count_rayExit_verticalStrictBridgeGapChain_connected
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
      RayExitVerticalStrictBridgeGapChainStep (S.image Subtype.val) ∧
      IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (hr : ∀ S ∈ D, (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) S).card = r) :
    D.card ≤ r * (2 * 2) ^ (2 * r) :=
  peierls_contour_count_rayExit_verticalStrictBridgeChain_connected hpre D hdual hi hne hg
    (fun S hS =>
      ⟨(hdata S hS).1,
        rayExitVerticalStrictBridgeChainStep_of_gapChainStep (hdata S hS).2.1,
        (hdata S hS).2.2⟩)
    hr

end IsingModel

import IsingModel.Peierls.RayExitAnchorVerticalStrictConnected

/-!
# Ordered strict vertical ray-exit obligations (FV §3.7.2)

`RayExitAnchorVerticalEqual.lean` reduces vertical ray-exit transport to upward `+e₁`
pairs whose first-exit indices are unequal.  This file splits that remaining strict input
by the order of the two exit indices.  The split is only an interface refinement: the two
ordered frontier-chain obligations remain explicit.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F Λ Λd : Finset (Fin 2 → ℤ)}

/-- The strict upward vertical obligation in the case where the lower ray exits first. -/
def RayExitVerticalStrictLtStep (F : Finset (Fin 2 → ℤ)) : Prop :=
  ∀ a b : {x : Fin 2 → ℤ // x ∈ F},
    b.1 = a.1 + unitVec2 1 →
      rayExitIndex F a.1 a.2 < rayExitIndex F b.1 b.2 →
        DartReachable F (rayExitAnchorDartMap F a) (rayExitAnchorDartMap F b)

/-- The strict upward vertical obligation in the case where the upper ray exits first. -/
def RayExitVerticalStrictGtStep (F : Finset (Fin 2 → ℤ)) : Prop :=
  ∀ a b : {x : Fin 2 → ℤ // x ∈ F},
    b.1 = a.1 + unitVec2 1 →
      rayExitIndex F b.1 b.2 < rayExitIndex F a.1 a.2 →
        DartReachable F (rayExitAnchorDartMap F a) (rayExitAnchorDartMap F b)

/-- The ordered form of the remaining strict vertical ray-exit obligation. -/
def RayExitVerticalStrictOrderedStep (F : Finset (Fin 2 → ℤ)) : Prop :=
  RayExitVerticalStrictLtStep F ∧ RayExitVerticalStrictGtStep F

/-- The ordered strict obligations recover the previous unequal-index strict obligation. -/
theorem rayExitVerticalStrictStep_of_orderedStep
    (hordered : RayExitVerticalStrictOrderedStep F) :
    RayExitVerticalStrictStep F := by
  intro a b hup hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hordered.1 a b hup hlt
  · exact hordered.2 a b hup hgt

/-- Pairwise dart reachability from ray-exit anchoring, ordered strict vertical data, and
within-`F` connectivity. -/
theorem dartReachable_of_rayExitVerticalStrictOrdered
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hordered : RayExitVerticalStrictOrderedStep F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b)
    (d e : BoundaryDart F) : DartReachable F d e :=
  dartReachable_of_rayExitVerticalStrict hanchor
    (rayExitVerticalStrictStep_of_orderedStep hordered) hconn d e

/-- The common-box dual cut is edge-connected from ordered strict vertical ray-exit data. -/
theorem dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictOrdered
    (hsub : dualSupport F ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hordered : RayExitVerticalStrictOrderedStep F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrict hsub hanchor
    (rayExitVerticalStrictStep_of_orderedStep hordered) hconn

/-- **The Peierls contour count from ordered strict vertical ray-exit data**: the remaining
unequal-index vertical input is split into the two possible exit-index orders. -/
theorem peierls_contour_count_rayExit_verticalStrictOrdered {i : Fin 2 → ℤ} {g : ↑Λ} {r : ℕ}
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
      RayExitVerticalStrictOrderedStep (S.image Subtype.val) ∧
      (∀ a ∈ S.image Subtype.val, ∀ b ∈ S.image Subtype.val,
        ReachableWithin (latticeGraph 2) (S.image Subtype.val) a b))
    (hr : ∀ S ∈ D, (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) S).card = r) :
    D.card ≤ r * (2 * 2) ^ (2 * r) :=
  peierls_contour_count_rayExit_verticalStrict hpre D hdual hi hne hg
    (fun S hS =>
      ⟨(hdata S hS).1, rayExitVerticalStrictStep_of_orderedStep (hdata S hS).2.1,
        (hdata S hS).2.2⟩)
    hr

/-- Pairwise dart reachability from ordered strict vertical data and connectedness of the underlying
box droplet. -/
theorem dartReachable_of_rayExitVerticalStrictOrdered_connected {S : Finset ↑Λ}
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hordered : RayExitVerticalStrictOrderedStep (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (d e : BoundaryDart (S.image Subtype.val)) :
    DartReachable (S.image Subtype.val) d e :=
  dartReachable_of_rayExitVerticalStrict_connected hanchor
    (rayExitVerticalStrictStep_of_orderedStep hordered) hconn d e

/-- The common-box dual cut is edge-connected from ordered strict vertical data and connectedness
of the underlying box droplet. -/
theorem dualCutInBox_isEdgeConnected_of_rayExitVerticalStrictOrdered_connected {S : Finset ↑Λ}
    (hsub : dualSupport (S.image Subtype.val) ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart (S.image Subtype.val),
      DartReachable (S.image Subtype.val) d
        (rayExitAnchorDartMap (S.image Subtype.val) ⟨d.left, d.left_mem⟩))
    (hordered : RayExitVerticalStrictOrderedStep (S.image Subtype.val))
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitVerticalStrict_connected hsub hanchor
    (rayExitVerticalStrictStep_of_orderedStep hordered) hconn

/-- **The Peierls contour count from ordered strict ray-exit data and connected droplets**: the
ordinary within-image connectivity is supplied from `IsConnectedDroplet`, while the two ordered
unequal-index vertical cases remain explicit. -/
theorem peierls_contour_count_rayExit_verticalStrictOrdered_connected
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
      RayExitVerticalStrictOrderedStep (S.image Subtype.val) ∧
      IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (hr : ∀ S ∈ D, (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) S).card = r) :
    D.card ≤ r * (2 * 2) ^ (2 * r) :=
  peierls_contour_count_rayExit_verticalStrict_connected hpre D hdual hi hne hg
    (fun S hS =>
      ⟨(hdata S hS).1, rayExitVerticalStrictStep_of_orderedStep (hdata S hS).2.1,
        (hdata S hS).2.2⟩)
    hr

end IsingModel

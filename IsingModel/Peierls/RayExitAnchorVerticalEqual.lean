import IsingModel.Peierls.RayExitAnchorAdjacencyRoute

/-!
# Equal-index vertical ray-exit anchor steps (FV §3.7.2)

`RayExitAnchorAdjacencyRoute.lean` leaves vertical adjacent-site ray-exit anchor transport as a
`DartReachable` obligation, because different first-exit indices may require a longer chain in the
dual cut.  This file closes the safe equal-index part: for an upward vertical pair `b = a + e₁`,
equal first-exit indices force the two ray-exit anchor dual edges to share the vertex at the lower
ray's exit point.

The remaining vertical input is therefore narrowed to a strict upward unequal-index obligation.
The downward case is obtained by applying the upward statement in the reverse order and using
symmetry of `DartReachable`.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F Λ Λd : Finset (Fin 2 → ℤ)}

/-- Adding and then subtracting the same coordinate unit vector returns the original site. -/
theorem add_unitVec2_sub_unitVec2 (x : Fin 2 → ℤ) (k : Fin 2) :
    x + unitVec2 k - unitVec2 k = x := by
  funext j
  simp [unitVec2, Pi.add_apply, Pi.sub_apply]

/-- Translating the origin by `+e₁` translates every point on the `+e₀` ray by `+e₁`. -/
theorem ray0_add_unitVec2_one (x : Fin 2 → ℤ) (k : ℕ) :
    ray0 (x + unitVec2 1) k = ray0 x k + unitVec2 1 := by
  simp only [ray0]
  abel

/-- For an upward vertical pair with equal first-exit indices, the ray-exit anchor dual edges share
the lower ray's first-exit point, in the canonical subtype representative. -/
theorem rayExitAnchorDartMap_add_e1_shared_of_index_eq'
    (a : {x : Fin 2 → ℤ // x ∈ F}) (hb : a.1 + unitVec2 1 ∈ F)
    (hidx : rayExitIndex F (a.1 + unitVec2 1) hb = rayExitIndex F a.1 a.2) :
    ∃ v : Fin 2 → ℤ,
      v ∈ s((rayExitAnchorDartMap F a).tail, (rayExitAnchorDartMap F a).head) ∧
        v ∈ s((rayExitAnchorDartMap F ⟨a.1 + unitVec2 1, hb⟩).tail,
          (rayExitAnchorDartMap F ⟨a.1 + unitVec2 1, hb⟩).head) := by
  refine ⟨ray0 a.1 (rayExitIndex F a.1 a.2), ?_, ?_⟩
  · exact rayExitAnchorDartMap_anchor_mem a
  · simp [hidx, ray0_add_unitVec2_one]

/-- For an upward vertical pair with equal first-exit indices, the ray-exit anchor dual edges share
the lower ray's first-exit point. -/
theorem rayExitAnchorDartMap_add_e1_shared_of_index_eq
    (a b : {x : Fin 2 → ℤ // x ∈ F}) (hup : b.1 = a.1 + unitVec2 1)
    (hidx : rayExitIndex F b.1 b.2 = rayExitIndex F a.1 a.2) :
    ∃ v : Fin 2 → ℤ,
      v ∈ s((rayExitAnchorDartMap F a).tail, (rayExitAnchorDartMap F a).head) ∧
        v ∈ s((rayExitAnchorDartMap F b).tail, (rayExitAnchorDartMap F b).head) := by
  let hb : a.1 + unitVec2 1 ∈ F := by
    simp [← hup]
  have hbsub : b = (⟨a.1 + unitVec2 1, hb⟩ : {x : Fin 2 → ℤ // x ∈ F}) :=
    Subtype.ext hup
  have hidx' : rayExitIndex F (a.1 + unitVec2 1) hb = rayExitIndex F a.1 a.2 := by
    simpa [hbsub] using hidx
  simpa [hbsub] using rayExitAnchorDartMap_add_e1_shared_of_index_eq' a hb hidx'

/-- The remaining strict vertical obligation: only upward `+e₁` pairs with unequal ray-exit indices
must be supplied by later geometry. -/
def RayExitVerticalStrictStep (F : Finset (Fin 2 → ℤ)) : Prop :=
  ∀ a b : {x : Fin 2 → ℤ // x ∈ F},
    b.1 = a.1 + unitVec2 1 →
      rayExitIndex F a.1 a.2 ≠ rayExitIndex F b.1 b.2 →
        DartReachable F (rayExitAnchorDartMap F a) (rayExitAnchorDartMap F b)

/-- A strict upward unequal-index obligation supplies the full vertical-step obligation: equal
indices share a vertex, while downward cases are handled by reversing the upward pair. -/
theorem rayExitVerticalStep_of_strictStep (hstrict : RayExitVerticalStrictStep F) :
    RayExitVerticalStep F := by
  intro a b hvert
  rcases hvert with hup | hdown
  · by_cases hidx : rayExitIndex F a.1 a.2 = rayExitIndex F b.1 b.2
    · obtain ⟨_, hva, hvb⟩ :=
        rayExitAnchorDartMap_add_e1_shared_of_index_eq a b hup hidx.symm
      exact dartReachable_of_shared hva hvb
    · exact hstrict a b hup hidx
  · by_cases hidx : rayExitIndex F b.1 b.2 = rayExitIndex F a.1 a.2
    · have hup : a.1 = b.1 + unitVec2 1 := by
        rw [hdown]
        exact (sub_unitVec2_add_unitVec2 a.1 1).symm
      obtain ⟨_, hvb, hva⟩ :=
        rayExitAnchorDartMap_add_e1_shared_of_index_eq b a hup hidx.symm
      exact dartReachable_of_shared hva hvb
    · have hup : a.1 = b.1 + unitVec2 1 := by
        rw [hdown]
        exact (sub_unitVec2_add_unitVec2 a.1 1).symm
      exact (hstrict b a hup hidx).symm

/-- Adjacent ray-exit anchors are reachable from the strict unequal-index vertical obligation. -/
theorem rayExitAnchorDartMap_adj_reachable_of_strictStep
    (hstrict : RayExitVerticalStrictStep F) (x y : {x : Fin 2 → ℤ // x ∈ F})
    (hxy : (latticeGraph 2).Adj x.1 y.1) :
    DartReachable F (rayExitAnchorDartMap F x) (rayExitAnchorDartMap F y) :=
  rayExitAnchorDartMap_adj_reachable_of_verticalStep
    (rayExitVerticalStep_of_strictStep hstrict) x y hxy

/-- Pairwise dart reachability from ray-exit anchoring, strict vertical data, and within-`F`
connectivity. -/
theorem dartReachable_of_rayExitVerticalStrict
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hstrict : RayExitVerticalStrictStep F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b)
    (d e : BoundaryDart F) : DartReachable F d e :=
  dartReachable_of_rayExitAdjacency hanchor (rayExitVerticalStep_of_strictStep hstrict)
    hconn d e

/-- The ambient dart dual cut is edge-connected from ray-exit anchoring, strict vertical data, and
within-`F` connectivity. -/
theorem dartDualCut_isEdgeConnected_of_rayExitVerticalStrict
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hstrict : RayExitVerticalStrictStep F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b) :
    IsEdgeConnected (dartDualCut F) :=
  dartDualCut_isEdgeConnected_of_rayExitAdjacency hanchor
    (rayExitVerticalStep_of_strictStep hstrict) hconn

/-- The subtype-lifted dual cut is edge-connected from ray-exit anchoring, strict vertical data, and
within-`F` connectivity. -/
theorem dualCutSub_isEdgeConnected_of_rayExitVerticalStrict
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hstrict : RayExitVerticalStrictStep F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b) :
    IsEdgeConnected (dualCutSub F) :=
  dualCutSub_isEdgeConnected_of_rayExitAdjacency hanchor
    (rayExitVerticalStep_of_strictStep hstrict) hconn

/-- The common-box dual cut is edge-connected from ray-exit anchoring, strict vertical data, and
within-`F` connectivity. -/
theorem dualCutInBox_isEdgeConnected_of_rayExitVerticalStrict (hsub : dualSupport F ⊆ Λd)
    (hanchor : ∀ d : BoundaryDart F,
      DartReachable F d (rayExitAnchorDartMap F ⟨d.left, d.left_mem⟩))
    (hstrict : RayExitVerticalStrictStep F)
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_rayExitAdjacency hsub hanchor
    (rayExitVerticalStep_of_strictStep hstrict) hconn

/-- **The Peierls contour count from strict vertical ray-exit data**: equal first-exit-index
vertical steps are closed by shared vertices, so the remaining vertical input only covers upward
unequal-index pairs. -/
theorem peierls_contour_count_rayExit_verticalStrict {i : Fin 2 → ℤ} {g : ↑Λ} {r : ℕ}
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
      (∀ a ∈ S.image Subtype.val, ∀ b ∈ S.image Subtype.val,
        ReachableWithin (latticeGraph 2) (S.image Subtype.val) a b))
    (hr : ∀ S ∈ D, (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) S).card = r) :
    D.card ≤ r * (2 * 2) ^ (2 * r) :=
  peierls_contour_count_rayExit_adjacency hpre D hdual hi hne hg
    (fun S hS =>
      ⟨(hdata S hS).1, rayExitVerticalStep_of_strictStep (hdata S hS).2.1,
        (hdata S hS).2.2⟩)
    hr

end IsingModel

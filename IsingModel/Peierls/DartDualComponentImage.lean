import IsingModel.Peierls.DartDualReachable
import IsingModel.Peierls.DartPrimalCutCard
import IsingModel.Peierls.PlanarBondSeparationBridge
import IsingModel.Peierls.EdgeSideComponent

/-!
# The box-primal image of a dart's dual component (FV §3.7.2)

Continuing the homological route to `PlanarBondHypothesis`: this file assembles the separating
region used in the discharge. From a boundary dart `d`, the edge set `B` is the box primal cut
edges of the darts in `d`'s dual-cut component (`DartReachable F d`), and the separating region is
`edgeSideComponent` of `B` rooted at `d.left`.

The constructions and all properties EXCEPT the discrete-Jordan separation are proved here:
membership in `B` is exactly dart reachability, a non-reachable dart's primal edge avoids `B` (and
hence the cut of the region), and the region's cut is contained in the lifted cut of `F`. The
single remaining hard input — `d.right` lies outside the region, i.e. `d`'s component separates
its two sides — is stated as `dual_component_separates_primal` and proved in a subsequent PR.

* `BoundaryDart.boxPrimalCutEdge` — a dart's primal cut edge as a box-subtype edge.
* `BoundaryDart.boxPrimalCutEdge_injective` — box primal edges distinguish darts.
* `dartDualComponentBoxPrimalEdges` — the box primal edges of `d`'s dual component.
* `boxPrimalCutEdge_mem_dartDualComponentBoxPrimalEdges_iff` — membership `↔` `DartReachable`.
* `dartDualComponentBoxPrimalEdges_subset_cutEdges_lift` — `B ⊆ cutEdges (liftFinset F)`.
* `cutEdges_edgeSideComponentDart_subset_lift` — the region's cut sits in the lifted cut of `F`.
* `boxPrimalCutEdge_not_mem_cutEdges_edgeSideComponentDart_of_not_reachable` — a non-reachable
  dart's primal edge avoids the region's cut.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset SimpleGraph

variable {F Λ : Finset (Fin 2 → ℤ)}

/-- **A dart's primal cut edge as a box-subtype edge**: `s(d.left, d.right)` lifted to
`Sym2 ↑Λ`, given that both sites lie in the box `Λ`. -/
def BoundaryDart.boxPrimalCutEdge (hFΛ : F ⊆ Λ) (hRΛ : ∀ q : BoundaryDart F, q.right ∈ Λ)
    (q : BoundaryDart F) : Sym2 (↑Λ : Type _) :=
  s(⟨q.left, hFΛ q.left_mem⟩, ⟨q.right, hRΛ q⟩)

/-- **Mapping a box primal edge back to the ambient primal cut edge**: applying `Sym2.map
Subtype.val` recovers `primalCutEdge q.tail q.dir`. -/
theorem BoundaryDart.map_val_boxPrimalCutEdge (hFΛ : F ⊆ Λ)
    (hRΛ : ∀ q : BoundaryDart F, q.right ∈ Λ) (q : BoundaryDart F) :
    Sym2.map Subtype.val (BoundaryDart.boxPrimalCutEdge hFΛ hRΛ q)
      = primalCutEdge q.tail q.dir := by
  rfl

/-- **Box primal cut edges distinguish boundary darts**: the map `q ↦ boxPrimalCutEdge q` is
injective (mapping back to the ambient primal edge and using `dartPrimalEdge_injective`). -/
theorem BoundaryDart.boxPrimalCutEdge_injective (hFΛ : F ⊆ Λ)
    (hRΛ : ∀ q : BoundaryDart F, q.right ∈ Λ) :
    Function.Injective (BoundaryDart.boxPrimalCutEdge hFΛ hRΛ) := by
  intro p q h
  apply dartPrimalEdge_injective
  change primalCutEdge p.tail p.dir = primalCutEdge q.tail q.dir
  rw [← BoundaryDart.map_val_boxPrimalCutEdge hFΛ hRΛ p,
    ← BoundaryDart.map_val_boxPrimalCutEdge hFΛ hRΛ q, h]

/-- **The box primal edges crossed by the dual component of `d`**: the image, under
`boxPrimalCutEdge`, of the darts reachable from `d` in the dual cut. -/
noncomputable def dartDualComponentBoxPrimalEdges (hFΛ : F ⊆ Λ)
    (hRΛ : ∀ q : BoundaryDart F, q.right ∈ Λ) (d : BoundaryDart F) :
    Finset (Sym2 (↑Λ : Type _)) := by
  classical
  exact ((Finset.univ : Finset (BoundaryDart F)).filter (fun q => DartReachable F d q)).image
    (BoundaryDart.boxPrimalCutEdge hFΛ hRΛ)

/-- **Membership in the dual-component box image is exactly dart reachability**: `e`'s box primal
edge lies in `dartDualComponentBoxPrimalEdges d` iff `DartReachable F d e` (by injectivity of
`boxPrimalCutEdge`). -/
theorem boxPrimalCutEdge_mem_dartDualComponentBoxPrimalEdges_iff (hFΛ : F ⊆ Λ)
    (hRΛ : ∀ q : BoundaryDart F, q.right ∈ Λ) (d e : BoundaryDart F) :
    BoundaryDart.boxPrimalCutEdge hFΛ hRΛ e ∈ dartDualComponentBoxPrimalEdges hFΛ hRΛ d ↔
      DartReachable F d e := by
  classical
  unfold dartDualComponentBoxPrimalEdges
  rw [Finset.mem_image]
  constructor
  · rintro ⟨q, hq, hqe⟩
    rw [Finset.mem_filter] at hq
    rw [BoundaryDart.boxPrimalCutEdge_injective hFΛ hRΛ hqe] at hq
    exact hq.2
  · intro hde
    exact ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ e, hde⟩, rfl⟩

/-- **A non-reachable dart's box primal edge avoids the dual-component image**. -/
theorem boxPrimalCutEdge_not_mem_dartDualComponentBoxPrimalEdges_of_not_reachable (hFΛ : F ⊆ Λ)
    (hRΛ : ∀ q : BoundaryDart F, q.right ∈ Λ) {d e : BoundaryDart F}
    (hne : ¬ DartReachable F d e) :
    BoundaryDart.boxPrimalCutEdge hFΛ hRΛ e ∉ dartDualComponentBoxPrimalEdges hFΛ hRΛ d := by
  rw [boxPrimalCutEdge_mem_dartDualComponentBoxPrimalEdges_iff]
  exact hne

/-- **The dual-component box image sits inside the lifted cut of `F`**: every dart's box primal
edge is a cut edge of `liftFinset F` (via `boundaryDart_box_primalCut_mem_cutEdges_lift`). -/
theorem dartDualComponentBoxPrimalEdges_subset_cutEdges_lift (hFΛ : F ⊆ Λ)
    (hRΛ : ∀ q : BoundaryDart F, q.right ∈ Λ) (d : BoundaryDart F) :
    dartDualComponentBoxPrimalEdges hFΛ hRΛ d ⊆
      cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) (Ambient.liftFinset F hFΛ) := by
  classical
  intro p hp
  unfold dartDualComponentBoxPrimalEdges at hp
  rw [Finset.mem_image] at hp
  obtain ⟨q, _, rfl⟩ := hp
  exact boundaryDart_box_primalCut_mem_cutEdges_lift hFΛ q (hRΛ q)

/-- **The separating region of the dual component of `d`**: `edgeSideComponent` of the box image
`B` rooted at `d.left`. -/
noncomputable def edgeSideComponentDart (hFΛ : F ⊆ Λ)
    (hRΛ : ∀ q : BoundaryDart F, q.right ∈ Λ) (d : BoundaryDart F) :
    Finset (↑Λ : Type _) :=
  edgeSideComponent (Ambient.inducedGraph (latticeGraph 2) Λ)
    (dartDualComponentBoxPrimalEdges hFΛ hRΛ d) ⟨d.left, hFΛ d.left_mem⟩

/-- **The region's cut sits inside the lifted cut of `F`**: `cutEdges (edgeSideComponentDart d)
⊆ cutEdges (liftFinset F)`, composing `cutEdges_edgeSideComponent_subset` with the box image's
containment in the lifted cut. This is the `hsub` input of
`false_of_box_separating_region_boundaryDart`. -/
theorem cutEdges_edgeSideComponentDart_subset_lift (hFΛ : F ⊆ Λ)
    (hRΛ : ∀ q : BoundaryDart F, q.right ∈ Λ) (d : BoundaryDart F) :
    cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) (edgeSideComponentDart hFΛ hRΛ d) ⊆
      cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) (Ambient.liftFinset F hFΛ) :=
  (cutEdges_edgeSideComponent_subset).trans
    (dartDualComponentBoxPrimalEdges_subset_cutEdges_lift hFΛ hRΛ d)

/-- **A non-reachable dart's primal edge avoids the region's cut**: since `cutEdges
(edgeSideComponentDart d) ⊆ B` and `e`'s box primal edge is not in `B` when `¬ DartReachable F d
e`, the edge is not in the region's cut. This is the `he_ncross` input of
`false_of_box_separating_region_boundaryDart`. -/
theorem boxPrimalCutEdge_not_mem_cutEdges_edgeSideComponentDart_of_not_reachable (hFΛ : F ⊆ Λ)
    (hRΛ : ∀ q : BoundaryDart F, q.right ∈ Λ) {d e : BoundaryDart F}
    (hne : ¬ DartReachable F d e) :
    BoundaryDart.boxPrimalCutEdge hFΛ hRΛ e ∉
      cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) (edgeSideComponentDart hFΛ hRΛ d) :=
  fun hmem =>
    boxPrimalCutEdge_not_mem_dartDualComponentBoxPrimalEdges_of_not_reachable hFΛ hRΛ hne
      (cutEdges_edgeSideComponent_subset hmem)

end IsingModel

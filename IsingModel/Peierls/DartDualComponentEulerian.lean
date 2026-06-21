import IsingModel.Peierls.DartDualReachable
import IsingModel.Peierls.DualCutConnected
import IsingModel.Peierls.DualCutEdgeAdjacency

/-!
# A dart's dual component is Eulerian (FV §3.7.2)

The discrete-Jordan separation `dual_component_separates_primal` (the remaining core of the
homological route, `PlanarBondAssembly.lean`) rests on a mod-2 crossing-parity argument, which in
turn needs the dual-cut component of a dart to be a **mod-2 cycle**: even degree at every dual
vertex.

The key structural fact proved here: at any dual vertex `c`, *all* dual-cut edges incident to `c`
are mutually `DartReachable` (they pairwise share the vertex `c`), so they lie in the same
component. Hence a dart's dual component, restricted to the edges incident to `c`, either misses
`c` entirely or contains every dual-cut edge at `c`. The component's incidence degree at `c` is
therefore `0` or equal to the full dual cut's, so it is even whenever the full dual cut is even at
`c`. This isolates the remaining even-degree obligation to the full dual cut.

* `dartDualComponentEdges` — the dual edges of the darts in `d`'s dual component.
* `dartDualComponentEdges_subset_dartDualCut` — the component edges sit inside the dual cut.
* `dartDualComponentEdges_incident_eq_dartDualCut_incident_of_mem` — at a vertex carrying a
  component edge, the component's incident edges equal the dual cut's incident edges.
* `dartDualComponentEdges_incident_even_of_dartDualCut_incident_even` — the component is even at
  `c` whenever the full dual cut is.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- **The dual edges of a dart's dual component**: the image, under `q ↦ s(q.tail, q.head)`, of
the darts reachable from `d` in the dual cut. -/
noncomputable def dartDualComponentEdges (F : Finset (Fin 2 → ℤ)) (d : BoundaryDart F) :
    Finset (Sym2 (Fin 2 → ℤ)) := by
  classical
  exact ((Finset.univ : Finset (BoundaryDart F)).filter (fun q => DartReachable F d q)).image
    (fun q => s(q.tail, q.head))

/-- **The component edges sit inside the dual cut**. -/
theorem dartDualComponentEdges_subset_dartDualCut (d : BoundaryDart F) :
    dartDualComponentEdges F d ⊆ dartDualCut F := by
  classical
  rw [dartDualComponentEdges, dartDualCut]
  exact Finset.image_subset_image (Finset.filter_subset _ _)

/-- **At a vertex carrying a component edge, the component's incident edges equal the dual cut's**:
if some dart `q` in `d`'s dual component has its dual edge through `c`, then every dual-cut edge
through `c` is also in the component (it shares the vertex `c` with `q`, so is `DartReachable`).
The two incidence sets at `c` therefore coincide. -/
theorem dartDualComponentEdges_incident_eq_dartDualCut_incident_of_mem {d q : BoundaryDart F}
    {c : Fin 2 → ℤ} (hdq : DartReachable F d q) (hcq : c ∈ s(q.tail, q.head)) :
    (dartDualComponentEdges F d).filter (fun e => c ∈ e) =
      (dartDualCut F).filter (fun e => c ∈ e) := by
  classical
  refine Finset.Subset.antisymm
    (Finset.filter_subset_filter _ (dartDualComponentEdges_subset_dartDualCut d)) ?_
  intro e' he'
  rw [Finset.mem_filter] at he' ⊢
  obtain ⟨he'cut, he'c⟩ := he'
  refine ⟨?_, he'c⟩
  rw [dartDualCut, Finset.mem_image] at he'cut
  obtain ⟨q', _, rfl⟩ := he'cut
  rw [dartDualComponentEdges, Finset.mem_image]
  exact ⟨q', Finset.mem_filter.mpr ⟨Finset.mem_univ q',
    hdq.trans (dartReachable_of_shared hcq he'c)⟩, rfl⟩

/-- **The component is even at `c` whenever the full dual cut is**: at any dual vertex `c`, the
component's incidence degree is `0` (if no component edge passes through `c`) or equals the full
dual cut's (by `..._incident_eq_..._of_mem`), hence even under the dual cut's even-degree
hypothesis. -/
theorem dartDualComponentEdges_incident_even_of_dartDualCut_incident_even (d : BoundaryDart F)
    (c : Fin 2 → ℤ) (heven : Even (((dartDualCut F).filter (fun e => c ∈ e)).card)) :
    Even (((dartDualComponentEdges F d).filter (fun e => c ∈ e)).card) := by
  classical
  by_cases h : ((dartDualComponentEdges F d).filter (fun e => c ∈ e)).Nonempty
  · obtain ⟨e', he'⟩ := h
    rw [Finset.mem_filter] at he'
    obtain ⟨he'comp, he'c⟩ := he'
    rw [dartDualComponentEdges, Finset.mem_image] at he'comp
    obtain ⟨q, hq, rfl⟩ := he'comp
    rw [Finset.mem_filter] at hq
    rw [dartDualComponentEdges_incident_eq_dartDualCut_incident_of_mem hq.2 he'c]
    exact heven
  · rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.card_empty]
    exact ⟨0, rfl⟩

end IsingModel

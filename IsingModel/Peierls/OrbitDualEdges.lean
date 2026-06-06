import IsingModel.Peierls.SameOrbit
import IsingModel.Conditioning.EdgeWalkExistence

/-!
# A dart orbit's dual edges are edge-connected (FV §3.7.2)

The dual edges `s(e.tail, e.head)` of the darts in one `nextDart`-orbit form an edge-connected set
in the face lattice: consecutive darts `e`, `nextDart e` have dual edges sharing the pivot vertex
`e.head = (nextDart e).tail`. This is one half of the contour count — once the discrete Jordan
single-curve theorem places all boundary darts of a connected filled region in one orbit, the
whole dual cut is this single edge-connected contour.

* `dartOrbit`, `orbitDualEdges` — the orbit (as a finset) and its dual edges.
* `orbitDualEdges_isEdgeConnected` — those dual edges are edge-connected.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

open Classical in
/-- The **orbit** of a dart, as a finset (its `SameOrbit` class). -/
noncomputable def dartOrbit (d : BoundaryDart F) : Finset (BoundaryDart F) :=
  Finset.univ.filter (fun e => d.SameOrbit e)

open Classical in
/-- The **dual edges** of a dart orbit: each dart `e` contributes the face-lattice edge
`s(e.tail, e.head)`. -/
noncomputable def orbitDualEdges (d : BoundaryDart F) : Finset (Sym2 (Fin 2 → ℤ)) :=
  (dartOrbit d).image (fun e => s(e.tail, e.head))

/-- Membership in the orbit's dual edges. -/
theorem mem_orbitDualEdges {d e : BoundaryDart F} (he : d.SameOrbit e) :
    s(e.tail, e.head) ∈ orbitDualEdges d := by
  classical
  rw [orbitDualEdges]
  exact Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩, rfl⟩

/-- **Each iterate's dual edge is reachable from the anchor**: the dual edge of `nextDart^[k] d` is
edge-adjacency-connected to the dual edge `s(d.tail, d.head)`. -/
theorem orbit_iterate_dualEdge_reachable (d : BoundaryDart F) (k : ℕ) :
    Relation.ReflTransGen (edgeAdjacentIn (orbitDualEdges d)) s(d.tail, d.head)
      s((BoundaryDart.nextDart^[k] d).tail, (BoundaryDart.nextDart^[k] d).head) := by
  induction k with
  | zero => exact Relation.ReflTransGen.refl
  | succ k ih =>
    refine ih.tail ?_
    have htail : (BoundaryDart.nextDart^[k + 1] d).tail = (BoundaryDart.nextDart^[k] d).head := by
      rw [Function.iterate_succ_apply', BoundaryDart.nextDart_tail]
    refine ⟨mem_orbitDualEdges ⟨k, rfl⟩, mem_orbitDualEdges ⟨k + 1, rfl⟩,
      (BoundaryDart.nextDart^[k] d).head, Sym2.mem_mk_right _ _, ?_⟩
    rw [← htail]
    exact Sym2.mem_mk_left _ _

/-- **The anchor reaches every orbit dual edge**. -/
theorem orbit_dualEdge_reachable {d e : BoundaryDart F} (he : d.SameOrbit e) :
    Relation.ReflTransGen (edgeAdjacentIn (orbitDualEdges d)) s(d.tail, d.head)
      s(e.tail, e.head) := by
  obtain ⟨k, hk⟩ := he
  rw [← hk]
  exact orbit_iterate_dualEdge_reachable d k

/-- **A dart orbit's dual edges are edge-connected**. -/
theorem orbitDualEdges_isEdgeConnected (d : BoundaryDart F) :
    IsEdgeConnected (orbitDualEdges d) := by
  classical
  have hsymm : Symmetric (edgeAdjacentIn (orbitDualEdges d)) := by
    intro a b h
    obtain ⟨v, hv⟩ := h.2.2
    exact ⟨h.2.1, h.1, v, hv.2, hv.1⟩
  intro e₁ he₁ e₂ he₂
  rw [orbitDualEdges, Finset.mem_image] at he₁ he₂
  obtain ⟨a, ha, rfl⟩ := he₁
  obtain ⟨b, hb, rfl⟩ := he₂
  rw [dartOrbit, Finset.mem_filter] at ha hb
  exact (Relation.ReflTransGen.symmetric hsymm (orbit_dualEdge_reachable ha.2)).trans
    (orbit_dualEdge_reachable hb.2)

end IsingModel

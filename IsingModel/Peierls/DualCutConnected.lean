import IsingModel.Peierls.OrbitDualEdges

/-!
# The whole dual cut is edge-connected, given a single orbit (FV §3.7.2)

The dual cut of a region `F` is the set of all dual edges `s(d.tail, d.head)` over the boundary
darts `d`. If all boundary darts lie in a single `nextDart`-orbit — the discrete Jordan
single-curve property for a connected, filled region — then this whole dual cut coincides with one
orbit's dual edges, hence is edge-connected (`orbitDualEdges_isEdgeConnected`).

This isolates the hard planar input (single orbit) as a hypothesis; once
`boundaryDart_single_orbit_of_connected_filled` is available, the whole dual cut is a single
edge-connected contour, the form consumed by the volume-independent count.

* `dartDualCut` — the dual cut as a finset.
* `dartDualCut_isEdgeConnected_of_single_orbit` — edge-connected given one orbit.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- The **dual cut** of `F`: every boundary dart's dual edge `s(d.tail, d.head)`. -/
noncomputable def dartDualCut (F : Finset (Fin 2 → ℤ)) : Finset (Sym2 (Fin 2 → ℤ)) :=
  (Finset.univ : Finset (BoundaryDart F)).image (fun d => s(d.tail, d.head))

/-- Membership in a dart orbit (as a finset). -/
theorem mem_dartOrbit {d e : BoundaryDart F} : e ∈ dartOrbit d ↔ d.SameOrbit e := by
  classical
  rw [dartOrbit, Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ e)

/-- **If all darts share one orbit, the dual cut is that orbit's dual edges**. -/
theorem dartDualCut_eq_orbitDualEdges (hone : ∀ d e : BoundaryDart F, d.SameOrbit e)
    (d : BoundaryDart F) : dartDualCut F = orbitDualEdges d := by
  have horb : dartOrbit d = (Finset.univ : Finset (BoundaryDart F)) :=
    Finset.eq_univ_iff_forall.mpr fun e => mem_dartOrbit.mpr (hone d e)
  rw [dartDualCut, orbitDualEdges, horb]

/-- **The whole dual cut is edge-connected, given a single orbit**: if all boundary darts lie in
one `nextDart`-orbit, the dual cut is a single edge-connected contour. -/
theorem dartDualCut_isEdgeConnected_of_single_orbit
    (hone : ∀ d e : BoundaryDart F, d.SameOrbit e) :
    IsEdgeConnected (dartDualCut F) := by
  classical
  rcases isEmpty_or_nonempty (BoundaryDart F) with hempty | hne
  · -- no boundary darts: the dual cut is empty, vacuously edge-connected
    have : dartDualCut F = ∅ := by
      rw [dartDualCut, Finset.univ_eq_empty, Finset.image_empty]
    rw [this]
    intro e₁ he₁
    simp only [Finset.notMem_empty] at he₁
  · obtain ⟨d⟩ := hne
    rw [dartDualCut_eq_orbitDualEdges hone d]
    exact orbitDualEdges_isEdgeConnected d

end IsingModel

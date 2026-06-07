import IsingModel.Peierls.DualCutConnected
import IsingModel.Peierls.OrbitDualEdges

/-!
# Edge-adjacency inside the whole dual cut (FV §3.7.2)

Towards proving the dual cut `dartDualCut F` of a connected, filled region is edge-connected
*directly* — without the strictly stronger single-orbit (discrete-Jordan) hypothesis. The decoupling
observation: at a degree-four crossing the four incident cut edges all share the crossing vertex, so
they are pairwise edge-adjacent **across distinct `nextDart`-orbits**; edge-connectivity therefore
genuinely sits below single-orbitness. These lemmas lift the within-orbit reachability of
`OrbitDualEdges` from one orbit's edges to the whole dual cut and record the basic shared-vertex
adjacency that the global argument chains together.

* `dartDualEdge_mem_dartDualCut` — a boundary dart's dual edge lies in the dual cut.
* `edgeAdjacentIn_dartDualCut_of_shared` — two cut edges sharing a vertex are edge-adjacent.
* `orbitDualEdges_subset_dartDualCut` — one orbit's dual edges sit inside the dual cut.
* `reachable_dartDualCut_of_sameOrbit` — same-orbit darts' edges are reachable in the dual cut.
* `edgeAdjacentIn_dartDualCut_nextDart` — a dart and its successor share the pivot vertex.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- **A boundary dart's dual edge lies in the dual cut**. -/
theorem dartDualEdge_mem_dartDualCut (d : BoundaryDart F) :
    s(d.tail, d.head) ∈ dartDualCut F := by
  rw [dartDualCut]
  exact Finset.mem_image_of_mem _ (Finset.mem_univ d)

/-- **Two cut edges sharing a dual vertex are edge-adjacent in the dual cut.** This is the step that
links different `nextDart`-orbits at a shared vertex (e.g. a degree-four crossing). -/
theorem edgeAdjacentIn_dartDualCut_of_shared {d e : BoundaryDart F} {v : Fin 2 → ℤ}
    (hd : v ∈ s(d.tail, d.head)) (he : v ∈ s(e.tail, e.head)) :
    edgeAdjacentIn (dartDualCut F) s(d.tail, d.head) s(e.tail, e.head) :=
  ⟨dartDualEdge_mem_dartDualCut d, dartDualEdge_mem_dartDualCut e, v, hd, he⟩

/-- **One orbit's dual edges sit inside the whole dual cut**. -/
theorem orbitDualEdges_subset_dartDualCut (d : BoundaryDart F) :
    orbitDualEdges d ⊆ dartDualCut F := by
  rw [orbitDualEdges, dartDualCut]
  exact Finset.image_subset_image (Finset.subset_univ _)

/-- **Same-orbit darts have dual edges reachable within the whole dual cut.** Lifting the within-
orbit reachability of `OrbitDualEdges` along the subset `orbitDualEdges d ⊆ dartDualCut F`. -/
theorem reachable_dartDualCut_of_sameOrbit {d e : BoundaryDart F} (he : d.SameOrbit e) :
    Relation.ReflTransGen (edgeAdjacentIn (dartDualCut F))
      s(d.tail, d.head) s(e.tail, e.head) :=
  (orbit_dualEdge_reachable he).mono
    (fun _ _ h => edgeAdjacentIn_mono (orbitDualEdges_subset_dartDualCut d) h)

/-- **A dart and its successor are edge-adjacent in the dual cut**, sharing the pivot vertex
`d.head = d.nextDart.tail`. -/
theorem edgeAdjacentIn_dartDualCut_nextDart (d : BoundaryDart F) :
    edgeAdjacentIn (dartDualCut F) s(d.tail, d.head)
      s(d.nextDart.tail, d.nextDart.head) := by
  refine edgeAdjacentIn_dartDualCut_of_shared (v := d.head) (Sym2.mem_mk_right _ _) ?_
  rw [BoundaryDart.nextDart_tail]
  exact Sym2.mem_mk_left _ _

end IsingModel

import IsingModel.Peierls.DualCutEdgeAdjacency

/-!
# Reachability of boundary darts inside the dual cut (FV §3.7.2)

The edge-connectedness of `dartDualCut F` is exactly the statement that any two boundary darts'
dual edges are joined by a chain of shared-vertex (`edgeAdjacentIn`) steps. This file packages that
reachability as a relation `DartReachable` on `BoundaryDart F` and records its closure properties,
then proves the **interface reduction** that turns whole-cut edge-connectedness into pairwise dart
reachability:

> `dartDualCut_isEdgeConnected_of_dartReachable` — if every pair of boundary darts is reachable,
> the whole dual cut is edge-connected.

This separates the target consumed at `PeierlsContourCount.lean` from the strictly stronger
single-orbit (discrete-Jordan) hypothesis `hone`: the remaining geometric obligation becomes "any
two boundary darts are reachable in the dual cut", the form intended for the F-path / shared-vertex
argument for a connected, filled region. Crucially the bridge is the weak shared-vertex relation
`edgeAdjacentIn` (via `edgeAdjacentIn_dartDualCut_of_shared`), **not** `SameOrbit`/`ContactMove`
(which would collapse back to single-orbitness); `SameOrbit` enters only as the convenience wrapper
`dartReachable_of_sameOrbit`.

* `DartReachable` — reachability of two darts' dual edges in `dartDualCut F`.
* `DartReachable.refl`, `DartReachable.symm`, `DartReachable.trans` — it is an equivalence.
* `dartReachable_of_shared` — darts sharing a dual vertex are reachable.
* `dartReachable_trans_shared` — extend a reachability by a shared-vertex step.
* `dartReachable_nextDart` — a dart and its `nextDart` successor are reachable.
* `dartReachable_of_sameOrbit` — same-orbit darts are reachable (comparison wrapper).
* `dartDualCut_isEdgeConnected_of_dartReachable` — pairwise reachability ⟹ edge-connected.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- **Reachability of two boundary darts inside the dual cut**: their dual edges
`s(d.tail, d.head)` and `s(e.tail, e.head)` are joined by a chain of shared-vertex steps
(`edgeAdjacentIn (dartDualCut F)`). This is the per-pair content of edge-connectedness. -/
def DartReachable (F : Finset (Fin 2 → ℤ)) (d e : BoundaryDart F) : Prop :=
  Relation.ReflTransGen (edgeAdjacentIn (dartDualCut F))
    s(d.tail, d.head) s(e.tail, e.head)

/-- Reachability is reflexive. -/
@[refl] theorem DartReachable.refl (d : BoundaryDart F) : DartReachable F d d :=
  Relation.ReflTransGen.refl

/-- Reachability is symmetric (the reflexive-transitive closure of the symmetric edge-adjacency
relation is symmetric). -/
theorem DartReachable.symm {d e : BoundaryDart F} (h : DartReachable F d e) :
    DartReachable F e d :=
  reflTransGen_edgeAdjacentIn_symmetric (dartDualCut F) h

/-- Reachability is transitive. -/
theorem DartReachable.trans {d e f : BoundaryDart F} (h₁ : DartReachable F d e)
    (h₂ : DartReachable F e f) : DartReachable F d f :=
  Relation.ReflTransGen.trans h₁ h₂

/-- **Two darts sharing a dual vertex are reachable**: a single shared-vertex step. This is the
cross-orbit link (e.g. the four cut edges meeting at a degree-four crossing). -/
theorem dartReachable_of_shared {d e : BoundaryDart F} {v : Fin 2 → ℤ}
    (hd : v ∈ s(d.tail, d.head)) (he : v ∈ s(e.tail, e.head)) :
    DartReachable F d e :=
  Relation.ReflTransGen.single (edgeAdjacentIn_dartDualCut_of_shared hd he)

/-- **Extend a reachability by a shared-vertex step**: if `d` reaches `e` and `e`, `f` share a
dual vertex, then `d` reaches `f`. The chaining primitive for the F-path argument. -/
theorem dartReachable_trans_shared {d e f : BoundaryDart F} {v : Fin 2 → ℤ}
    (h : DartReachable F d e) (he : v ∈ s(e.tail, e.head)) (hf : v ∈ s(f.tail, f.head)) :
    DartReachable F d f :=
  h.trans (dartReachable_of_shared he hf)

/-- **A dart and its `nextDart` successor are reachable**, sharing the pivot vertex
`d.head = d.nextDart.tail`. -/
theorem dartReachable_nextDart (d : BoundaryDart F) : DartReachable F d d.nextDart :=
  Relation.ReflTransGen.single (edgeAdjacentIn_dartDualCut_nextDart d)

/-- **Same-orbit darts are reachable** (comparison wrapper over
`reachable_dartDualCut_of_sameOrbit`). Note `SameOrbit` is *not* the intended bridge of the
unconditional route; the direct route must provide `DartReachable` by shared-vertex chains. -/
theorem dartReachable_of_sameOrbit {d e : BoundaryDart F} (he : d.SameOrbit e) :
    DartReachable F d e :=
  reachable_dartDualCut_of_sameOrbit he

/-- **Pairwise dart reachability gives an edge-connected dual cut**. This is the interface reduction
needed to replace the single-orbit hypothesis consumed at `PeierlsContourCount.lean`: it suffices to
show any two boundary darts are reachable in `dartDualCut F`. -/
theorem dartDualCut_isEdgeConnected_of_dartReachable
    (h : ∀ d e : BoundaryDart F, DartReachable F d e) :
    IsEdgeConnected (dartDualCut F) := by
  classical
  intro e₁ he₁ e₂ he₂
  rw [dartDualCut, Finset.mem_image] at he₁ he₂
  obtain ⟨d, _, rfl⟩ := he₁
  obtain ⟨e, _, rfl⟩ := he₂
  exact h d e

end IsingModel

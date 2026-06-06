import IsingModel.Peierls.GridEdge2Cut

/-!
# The dual edge map and its cardinality (FV §3.7.2)

A set `B` of `latticeGraph 2` edges (e.g. the primal cut `cutEdges F` of a region, lifted from
the box subtype to the ambient lattice) is transported to its **dual** edge set: each edge becomes
its perpendicular `GridEdge2.dual`. The dual map is injective, so the dual set has the same
cardinality `r` as `B`. This is the set whose connectivity (in the face lattice) will be counted.

* `otherAxis_injective`, `GridEdge2.dual_injective` — the dual map is injective.
* `toGrid`, `toGrid_toSym2` — the partial inverse of `toSym2` on lattice edges.
* `dualEdge`, `dualEdges`, `dualEdges_card` — the dual edge map and cardinality preservation.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

/-- `otherAxis` is injective (it is an involution on `Fin 2`). -/
theorem otherAxis_injective : Function.Injective otherAxis := by decide

/-- **The dual map is injective**: distinct directed coordinate edges have distinct duals. -/
theorem GridEdge2.dual_injective : Function.Injective GridEdge2.dual := by
  rintro ⟨a, j⟩ ⟨b, l⟩ h
  simp only [GridEdge2.dual, GridEdge2.mk.injEq] at h
  obtain ⟨hbase, hax⟩ := h
  have hjl : j = l := otherAxis_injective hax
  subst hjl
  rw [GridEdge2.mk.injEq]
  exact ⟨sub_left_injective hbase, rfl⟩

/-- The directed coordinate edge representing a lattice edge `e` (junk if `e` is not a lattice
edge). The partial inverse of `GridEdge2.toSym2`. -/
noncomputable def toGrid (e : Sym2 (Fin 2 → ℤ)) : GridEdge2 := by
  classical
  exact if h : e ∈ (latticeGraph 2).edgeSet then gridEdge2Equiv.symm ⟨e, h⟩ else ⟨0, 0⟩

/-- **Round trip on lattice edges**: `toGrid` followed by `toSym2` recovers a lattice edge. -/
theorem toGrid_toSym2 {e : Sym2 (Fin 2 → ℤ)} (he : e ∈ (latticeGraph 2).edgeSet) :
    (toGrid e).toSym2 = e := by
  rw [toGrid, dif_pos he]
  have : GridEdge2.toEdgeSet (gridEdge2Equiv.symm ⟨e, he⟩) = ⟨e, he⟩ :=
    gridEdge2Equiv.apply_symm_apply ⟨e, he⟩
  exact congrArg Subtype.val this

/-- **The dual edge** of a lattice edge: the perpendicular edge joining the two unit squares it
separates. -/
noncomputable def dualEdge (e : Sym2 (Fin 2 → ℤ)) : Sym2 (Fin 2 → ℤ) := (toGrid e).dual.toSym2

/-- **The dual edge map is injective on lattice edges**. -/
theorem dualEdge_injOn :
    Set.InjOn dualEdge {e | e ∈ (latticeGraph 2).edgeSet} := by
  intro a ha b hb hab
  rw [Set.mem_setOf_eq] at ha hb
  have h1 : (toGrid a).dual = (toGrid b).dual := GridEdge2.toSym2_injective hab
  have h2 : toGrid a = toGrid b := GridEdge2.dual_injective h1
  rw [← toGrid_toSym2 ha, ← toGrid_toSym2 hb, h2]

/-- **The dual edge set** of a finset of lattice edges. -/
noncomputable def dualEdges (B : Finset (Sym2 (Fin 2 → ℤ))) : Finset (Sym2 (Fin 2 → ℤ)) :=
  B.image dualEdge

/-- **Cardinality preservation**: if every edge of `B` is a lattice edge, the dual set has the
same cardinality `|dualEdges B| = |B| = r`. -/
theorem dualEdges_card {B : Finset (Sym2 (Fin 2 → ℤ))}
    (hB : ∀ e ∈ B, e ∈ (latticeGraph 2).edgeSet) :
    (dualEdges B).card = B.card := by
  rw [dualEdges, Finset.card_image_of_injOn]
  exact fun a ha b hb hab => dualEdge_injOn (hB a ha) (hB b hb) hab

/-- **Each dual edge is a lattice edge** (in the face lattice, again `latticeGraph 2`). -/
theorem dualEdge_mem_edgeSet (e : Sym2 (Fin 2 → ℤ)) :
    dualEdge e ∈ (latticeGraph 2).edgeSet :=
  (toGrid e).dual.toSym2_isLatticeEdge

end IsingModel

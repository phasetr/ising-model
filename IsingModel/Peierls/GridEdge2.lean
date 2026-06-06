import IsingModel.Lattice

/-!
# Directed coordinate edges and the dual correspondence in 2D (FV §3.7.2)

To count Peierls contours in the 2D lattice, the boundary `cutEdges F` of a region is connected
not in the primal graph but in the **dual** graph (edges sharing a unit square / face). The dual
graph of `latticeGraph 2` is, up to a half-integer shift, again `latticeGraph 2` on the faces.

To avoid the `Sym2` quotient in the geometry, we represent a lattice edge by a **directed
coordinate edge** `GridEdge2`: a base point and an axis, standing for the edge from `base` to
`base + e_axis`. Each undirected `latticeGraph 2` edge has a unique such representative.

The **dual edge** of a primal coordinate edge is the (face-lattice) edge joining the two unit
squares it separates — a `latticeGraph 2` edge perpendicular to the primal one. This is the entry
point for transporting the primal contour to a connected dual edge set, where the existing
walk-counting machinery applies.

* `GridEdge2`, `unitVec2`, `GridEdge2.toSym2` — the directed-edge representation.
* `toSym2_isLatticeEdge`, `toSym2_injective` — it is a lattice edge, injectively.
* `GridEdge2.dual`, `dual_toSym2_isLatticeEdge` — the perpendicular dual edge.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

/-- The `k`-th coordinate unit vector in `ℤ²`. -/
def unitVec2 (k : Fin 2) : Fin 2 → ℤ := Pi.single k 1

/-- The other coordinate axis (`0 ↦ 1`, `1 ↦ 0`). -/
def otherAxis (k : Fin 2) : Fin 2 := if k = 0 then 1 else 0

@[simp] theorem otherAxis_zero : otherAxis 0 = 1 := rfl

@[simp] theorem otherAxis_one : otherAxis 1 = 0 := rfl

/-- A **directed coordinate edge** of the 2D lattice: the edge from `base` to `base + e_axis`. -/
structure GridEdge2 where
  /-- The lower endpoint of the edge. -/
  base : Fin 2 → ℤ
  /-- The axis along which the edge points. -/
  axis : Fin 2
deriving DecidableEq

namespace GridEdge2

/-- The undirected `latticeGraph 2` edge represented by a directed coordinate edge. -/
def toSym2 (e : GridEdge2) : Sym2 (Fin 2 → ℤ) := s(e.base, e.base + unitVec2 e.axis)

/-- **A coordinate step is a lattice adjacency**: `x` and `x + e_k` are adjacent in
`latticeGraph 2`. -/
theorem latticeGraph_adj_add_unitVec2 (x : Fin 2 → ℤ) (k : Fin 2) :
    (latticeGraph 2).Adj x (x + unitVec2 k) := by
  change (∑ i : Fin 2, |x i - (x + unitVec2 k) i|) = 1
  have h : ∀ i : Fin 2, |x i - (x + unitVec2 k) i| = (if i = k then 1 else 0) := by
    intro i
    simp only [unitVec2, Pi.add_apply, Pi.single_apply]
    by_cases hik : i = k <;> simp [hik]
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_ite_eq' Finset.univ k]
  simp

/-- **The represented edge is a lattice edge**: `e.toSym2 ∈ (latticeGraph 2).edgeSet`. -/
theorem toSym2_isLatticeEdge (e : GridEdge2) : e.toSym2 ∈ (latticeGraph 2).edgeSet := by
  rw [toSym2, SimpleGraph.mem_edgeSet]
  exact latticeGraph_adj_add_unitVec2 e.base e.axis

/-- `unitVec2 k` is the indicator of axis `k`. -/
theorem unitVec2_apply (k j : Fin 2) : unitVec2 k j = if j = k then 1 else 0 := by
  simp [unitVec2, Pi.single_apply]

/-- The two coordinate unit vectors never sum to zero (both entries are nonnegative, one is
positive at each axis). -/
theorem unitVec2_add_ne_zero (k l : Fin 2) : unitVec2 k + unitVec2 l ≠ 0 := by
  intro h
  have hk := congrFun h k
  rw [Pi.add_apply, Pi.zero_apply, unitVec2_apply, unitVec2_apply, if_pos rfl] at hk
  split at hk <;> omega

/-- **The representation is injective**: distinct directed coordinate edges give distinct
undirected lattice edges. -/
theorem toSym2_injective : Function.Injective toSym2 := by
  rintro ⟨a, j⟩ ⟨b, l⟩ h
  simp only [toSym2] at h
  rw [Sym2.eq_iff] at h
  rcases h with ⟨ha, hjl⟩ | ⟨ha, hjl⟩
  · -- `a = b` and `a + e_j = b + e_l`, so `e_j = e_l`, so `j = l`
    subst ha
    have hu : unitVec2 j = unitVec2 l := by rwa [add_right_inj] at hjl
    have hjl' : j = l := by
      by_contra hne
      have h0 := congrFun hu j
      rw [unitVec2_apply, unitVec2_apply, if_pos rfl, if_neg hne] at h0
      exact one_ne_zero h0
    subst hjl'; rfl
  · -- `a = b + e_l` and `a + e_j = b`: then `e_l + e_j = 0`, impossible
    exfalso
    have h4 : b + (unitVec2 l + unitVec2 j) = b + 0 := by
      rw [← add_assoc, add_zero, ← ha]; exact hjl
    exact unitVec2_add_ne_zero l j (add_left_cancel h4)

/-- **The dual edge** of a primal coordinate edge: the face-lattice edge joining the two unit
squares the primal edge separates, perpendicular to it (axis `otherAxis e.axis`, based one step
back along that perpendicular). -/
def dual (e : GridEdge2) : GridEdge2 :=
  ⟨e.base - unitVec2 (otherAxis e.axis), otherAxis e.axis⟩

/-- **The dual edge is also a lattice edge** (in the face lattice, which is again
`latticeGraph 2`). -/
theorem dual_toSym2_isLatticeEdge (e : GridEdge2) : e.dual.toSym2 ∈ (latticeGraph 2).edgeSet :=
  toSym2_isLatticeEdge e.dual

/-- **The dual is perpendicular**: the dual edge runs along the other axis. -/
@[simp] theorem dual_axis (e : GridEdge2) : e.dual.axis = otherAxis e.axis := rfl

end GridEdge2

end IsingModel

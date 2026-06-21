import IsingModel.Peierls.DropletInjective

/-!
# The component of a vertex after deleting an edge set (FV §3.7.2)

The homological route to `PlanarBondHypothesis` constructs a separating region from a dual-cut
component `B`: the set of vertices reachable from a base point without traversing any edge of `B`.
This file builds that construction abstractly over a finite graph and proves its defining
property — its edge cut is contained in `B`.

* `ReachableAvoidingEdges` — reachability via edges avoiding a prescribed edge set `B`.
* `edgeSideComponent` — the component of `x` in `G` with the edges of `B` deleted.
* `mem_edgeSideComponent_iff`, `base_mem_edgeSideComponent` — membership and the base point.
* `edgeSideComponent_mem_iff_of_adj_not_block` — an edge outside `B` does not separate the
  component (both endpoints lie in it together).
* `cutEdges_edgeSideComponent_subset` — **the cut of the component is contained in `B`**: every
  edge leaving the component is an edge of `B`. This is the property that makes
  `edgeSideComponent` a valid separating region (`cutEdges A ⊆ B`).

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset SimpleGraph

variable {ι : Type*}

/-- **Reachability avoiding an edge set**: `x` reaches `y` by a chain of `G`-adjacencies none of
whose edges lie in `B`. Deleting `B` from `G` and asking for ordinary reachability. -/
def ReachableAvoidingEdges (G : SimpleGraph ι) (B : Finset (Sym2 ι)) (x y : ι) : Prop :=
  Relation.ReflTransGen (fun a b => G.Adj a b ∧ s(a, b) ∉ B) x y

/-- Reachability avoiding `B` is reflexive. -/
@[refl] theorem ReachableAvoidingEdges.refl (G : SimpleGraph ι) (B : Finset (Sym2 ι)) (x : ι) :
    ReachableAvoidingEdges G B x x :=
  Relation.ReflTransGen.refl

variable [Fintype ι]

/-- **The edge-deleted component of `x`**: the vertices reachable from `x` in `G` without
traversing any edge of `B`. -/
noncomputable def edgeSideComponent (G : SimpleGraph ι) (B : Finset (Sym2 ι)) (x : ι) :
    Finset ι := by
  classical
  exact Finset.univ.filter (fun y => ReachableAvoidingEdges G B x y)

/-- **Membership in the edge-deleted component**. -/
theorem mem_edgeSideComponent_iff {G : SimpleGraph ι} {B : Finset (Sym2 ι)} {x y : ι} :
    y ∈ edgeSideComponent G B x ↔ ReachableAvoidingEdges G B x y := by
  classical
  unfold edgeSideComponent
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ y)

/-- **The base point lies in its own component**. -/
theorem base_mem_edgeSideComponent (G : SimpleGraph ι) (B : Finset (Sym2 ι)) (x : ι) :
    x ∈ edgeSideComponent G B x :=
  mem_edgeSideComponent_iff.mpr (ReachableAvoidingEdges.refl G B x)

/-- **An edge outside `B` does not separate the component**: if `a` and `b` are adjacent and
`s(a, b) ∉ B`, then `a` lies in the component iff `b` does (the avoiding-`B` reachability extends
across the edge in both directions). -/
theorem edgeSideComponent_mem_iff_of_adj_not_block {G : SimpleGraph ι} {B : Finset (Sym2 ι)}
    {x a b : ι} (hadj : G.Adj a b) (hB : s(a, b) ∉ B) :
    a ∈ edgeSideComponent G B x ↔ b ∈ edgeSideComponent G B x := by
  rw [mem_edgeSideComponent_iff, mem_edgeSideComponent_iff]
  constructor
  · intro ha; exact ha.tail ⟨hadj, hB⟩
  · intro hb; refine hb.tail ⟨hadj.symm, ?_⟩; rwa [Sym2.eq_swap]

/-- **The cut of the edge-deleted component is contained in `B`**: every edge with exactly one
endpoint in `edgeSideComponent G B x` belongs to `B`. Hence `edgeSideComponent G B x` is a region
whose edge cut sits inside `B` — the separating region built from a dual-cut component `B`. -/
theorem cutEdges_edgeSideComponent_subset {G : SimpleGraph ι} [DecidableEq ι]
    [DecidableRel G.Adj] [Fintype G.edgeSet] {B : Finset (Sym2 ι)} {x : ι} :
    cutEdges G (edgeSideComponent G B x) ⊆ B := by
  intro e he
  induction e with
  | h a b =>
    rw [mem_cutEdges_iff] at he
    by_contra hB
    have hm := edgeSideComponent_mem_iff_of_adj_not_block (x := x) he.1 hB
    exact iff_not_self (hm.symm.trans he.2)

end IsingModel

import IsingModel.Peierls.ConnectedDroplet

/-!
# The boundary determines a connected droplet (FV §3.7.2)

Towards the volume-independent contour counting for `m*(β)>0`, the map sending a connected
droplet `S` to its edge boundary `cutEdges G S` is **injective** on connected droplets
containing a fixed vertex `i`. The droplet `S` is recoverable from its boundary: it is the
connected component of `i` in `G` once the boundary edges are removed, because every internal
edge of `S` (both endpoints in `S`) lies *outside* `cutEdges G S`, so a within-`S` walk from
`i` never crosses the boundary and therefore stays inside any droplet `T ⊇ {i}` with the same
boundary.

This reduces counting connected droplets by their cut size to counting *edge sets*, where the
walk-counting machinery (`card_connected_edge_sets_inducedLatticeGraph_le`,
`walksFromCount_le_pow`) applies.

* `mem_cutEdges_iff` — membership in the edge cut.
* `mem_cutEdges_of_mem_not_mem` — a crossing edge is a cut edge.
* `mem_of_adj_not_mem_cutEdges` — a non-cut edge stays inside `S`.
* `isConnectedDroplet_subset_of_cutEdges_eq` — equal boundaries ⟹ one droplet ⊆ the other.
* `cutEdges_injOn_connectedDroplet` — `S ↦ cutEdges G S` is injective on connected droplets ∋ i.
* `card_connectedDroplet_eq_card_cutEdges_image` — droplet count ≤ boundary-image count.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- **Membership in the edge cut**: `s(a,b)` is a cut edge of `S` iff `a,b` are adjacent and
exactly one of them lies in `S`. -/
theorem mem_cutEdges_iff {G : SimpleGraph ι} [DecidableRel G.Adj] [Fintype G.edgeSet]
    {S : Finset ι} {a b : ι} :
    s(a, b) ∈ cutEdges G S ↔ G.Adj a b ∧ ((a ∈ S) ↔ ¬ (b ∈ S)) := by
  rw [cutEdges, Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  refine and_congr_right fun _ => ?_
  unfold edgeCrosses
  rw [Sym2.lift_mk]
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> simp [ha, hb]

omit [Fintype ι] in
/-- **A crossing edge is a cut edge**: if `a ∈ S`, `b ∉ S`, and `a,b` are adjacent, then
`s(a,b)` lies in the edge cut of `S`. -/
theorem mem_cutEdges_of_mem_not_mem {G : SimpleGraph ι} [DecidableRel G.Adj]
    [Fintype G.edgeSet] {S : Finset ι} {a b : ι} (hadj : G.Adj a b) (ha : a ∈ S)
    (hb : b ∉ S) : s(a, b) ∈ cutEdges G S :=
  mem_cutEdges_iff.mpr ⟨hadj, by simp [ha, hb]⟩

omit [Fintype ι] in
/-- **A non-cut edge stays inside `S`**: if `a ∈ S`, `a,b` are adjacent, and `s(a,b)` is *not*
a cut edge of `S`, then `b ∈ S` too. This is the key step: walking along a non-boundary edge
cannot leave the droplet. -/
theorem mem_of_adj_not_mem_cutEdges {G : SimpleGraph ι} [DecidableRel G.Adj]
    [Fintype G.edgeSet] {S : Finset ι} {a b : ι} (hadj : G.Adj a b) (ha : a ∈ S)
    (hcut : s(a, b) ∉ cutEdges G S) : b ∈ S := by
  by_contra hb
  exact hcut (mem_cutEdges_of_mem_not_mem hadj ha hb)

omit [Fintype ι] in
/-- **Equal boundaries force one droplet inside the other**: if `S` is a connected droplet,
`i ∈ S`, `i ∈ T`, and `cutEdges G S = cutEdges G T`, then `S ⊆ T`. A within-`S` walk from `i`
crosses no edge of `cutEdges G S = cutEdges G T`, so it stays inside `T`. -/
theorem isConnectedDroplet_subset_of_cutEdges_eq {G : SimpleGraph ι} [DecidableRel G.Adj]
    [Fintype G.edgeSet] {S T : Finset ι} {i : ι} (hS : IsConnectedDroplet G S) (hiS : i ∈ S)
    (hiT : i ∈ T) (hcut : cutEdges G S = cutEdges G T) : S ⊆ T := by
  -- every vertex reachable within `S` from `i` already lies in `T`
  have key : ∀ y, ReachableWithin G S i y → y ∈ T := by
    intro y hy
    induction hy with
    | refl => exact hiT
    | @tail a b _ hstep ih =>
      -- `hstep : G.Adj a b ∧ a ∈ S ∧ b ∈ S`; the edge `s(a,b)` is internal to `S`, not cut
      obtain ⟨hadj, haS, hbS⟩ := hstep
      have hnotcutS : s(a, b) ∉ cutEdges G S := by
        intro hc
        rw [mem_cutEdges_iff] at hc
        exact (hc.2.mp haS) hbS
      have hnotcutT : s(a, b) ∉ cutEdges G T := hcut ▸ hnotcutS
      exact mem_of_adj_not_mem_cutEdges hadj ih hnotcutT
  exact fun x hxS => key x (hS i hiS x hxS)

omit [Fintype ι] in
/-- **The boundary determines a connected droplet**: two connected droplets containing `i`
with the same edge boundary are equal. -/
theorem connectedDroplet_eq_of_cutEdges_eq {G : SimpleGraph ι} [DecidableRel G.Adj]
    [Fintype G.edgeSet] {S T : Finset ι} {i : ι} (hS : IsConnectedDroplet G S)
    (hT : IsConnectedDroplet G T) (hiS : i ∈ S) (hiT : i ∈ T)
    (hcut : cutEdges G S = cutEdges G T) : S = T :=
  Finset.Subset.antisymm
    (isConnectedDroplet_subset_of_cutEdges_eq hS hiS hiT hcut)
    (isConnectedDroplet_subset_of_cutEdges_eq hT hiT hiS hcut.symm)

open Classical in
/-- **`S ↦ cutEdges G S` is injective on connected droplets containing `i`**: the boundary map
is injective on the finset of connected droplets `S ∋ i`. The basis of the volume-independent
contour count — droplets are counted by their boundary edge sets. -/
theorem cutEdges_injOn_connectedDroplet (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (i : ι) :
    Set.InjOn (cutEdges G)
      ↑(Finset.univ.filter (fun S : Finset ι => i ∈ S ∧ IsConnectedDroplet G S)) := by
  intro S hS T hT hcut
  rw [Finset.mem_coe, Finset.mem_filter] at hS hT
  exact connectedDroplet_eq_of_cutEdges_eq hS.2.2 hT.2.2 hS.2.1 hT.2.1 hcut

open Classical in
/-- **Connected droplets are counted by their boundaries**: the number of connected droplets
`S ∋ i` equals the number of edge sets arising as `cutEdges G S`. Reduces the contour count to
an edge-set count. -/
theorem card_connectedDroplet_eq_card_cutEdges_image (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (i : ι) :
    (Finset.univ.filter (fun S : Finset ι => i ∈ S ∧ IsConnectedDroplet G S)).card =
    ((Finset.univ.filter (fun S : Finset ι => i ∈ S ∧ IsConnectedDroplet G S)).image
        (cutEdges G)).card :=
  (Finset.card_image_of_injOn (by
    intro S hS T hT hcut
    rw [Finset.mem_coe, Finset.mem_filter] at hS hT
    exact connectedDroplet_eq_of_cutEdges_eq hS.2.2 hT.2.2 hS.2.1 hT.2.1 hcut)).symm

end IsingModel

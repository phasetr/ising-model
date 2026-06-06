import IsingModel.Peierls.DropletInjective

/-!
# Hole-filled droplet region (FV §3.7.2)

To count Peierls contours volume-independently one wants the droplet boundary to reduce to a
single outer contour. A connected droplet `S` can have holes (its complement can be
disconnected: an outer "outside" component plus interior holes), and then `cutEdges G S` carries
both inner and outer boundary. Filling the holes removes the inner boundaries, leaving the
complement a single connected "outside" component.

Fix a *ground* vertex `g ∉ S` (the anchor of the unbounded "outside", e.g. a `+`-boundary
vertex). The **outside component** `outsideComponent G S g` is the set of vertices reachable
from `g` without entering `S`; the **filled region** `filledRegion G S g` is its complement,
i.e. `S` together with all holes. Filling only *removes* boundary edges, so when `S` is the
down-spin component the filled region still has `cutEdges ⊆ phaseBoundary`, and its complement
(the outside) is connected. (Edge-connectivity of `cutEdges F` as a single contour is *not*
automatic for an abstract graph — that requires the `d = 2` dual/planar geometry, deferred.)

* `outsideComponent`, `filledRegion` — the constructions.
* `subset_filledRegion`, `ground_not_mem_filledRegion` — `S ⊆ F` and `g ∉ F`.
* `mem_droplet_of_mem_filledRegion_adj_outside` — a boundary edge of `F` has its `F`-side in `S`
  (holes are not adjacent to the outside).
* `cutEdges_filledRegion_downComponent_subset_phaseBoundary` — the filled boundary is still
  broken bonds.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The outside component**: vertices reachable from the ground vertex `g` by a walk staying
outside `S`. In a finite system this is the complementary component anchored at `g`. -/
noncomputable def outsideComponent (G : SimpleGraph ι) [DecidableRel G.Adj] (S : Finset ι)
    (g : ι) : Finset ι := by
  classical
  exact Finset.univ.filter (fun j => ReachableWithin G (Finset.univ \ S) g j)

/-- Membership in the outside component. -/
theorem mem_outsideComponent {G : SimpleGraph ι} [DecidableRel G.Adj] {S : Finset ι} {g j : ι} :
    j ∈ outsideComponent G S g ↔ ReachableWithin G (Finset.univ \ S) g j := by
  classical
  unfold outsideComponent
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ j)

/-- The ground vertex lies in its own outside component. -/
theorem ground_mem_outsideComponent (G : SimpleGraph ι) [DecidableRel G.Adj] (S : Finset ι)
    (g : ι) : g ∈ outsideComponent G S g :=
  mem_outsideComponent.mpr Relation.ReflTransGen.refl

/-- **The outside avoids `S`**: if `g ∉ S`, every vertex of the outside component is outside `S`. -/
theorem outsideComponent_subset_compl {G : SimpleGraph ι} [DecidableRel G.Adj] {S : Finset ι}
    {g : ι} (hg : g ∉ S) : ∀ j ∈ outsideComponent G S g, j ∉ S := by
  intro j hj
  rw [mem_outsideComponent] at hj
  induction hj with
  | refl => exact hg
  | tail _ hstep _ =>
    have := hstep.2.2
    rw [Finset.mem_sdiff] at this
    exact this.2

/-- **The hole-filled region**: the complement of the outside component, i.e. `S` together with
every hole (bounded complementary component). -/
noncomputable def filledRegion (G : SimpleGraph ι) [DecidableRel G.Adj] (S : Finset ι)
    (g : ι) : Finset ι :=
  Finset.univ \ outsideComponent G S g

/-- Membership in the filled region: `j ∈ F` iff `j` is *not* reachable from `g` avoiding `S`. -/
theorem mem_filledRegion {G : SimpleGraph ι} [DecidableRel G.Adj] {S : Finset ι} {g j : ι} :
    j ∈ filledRegion G S g ↔ j ∉ outsideComponent G S g := by
  unfold filledRegion
  rw [Finset.mem_sdiff]
  exact and_iff_right (Finset.mem_univ j)

/-- **The droplet is contained in its filled region** (for `g ∉ S`): no `S`-vertex is outside. -/
theorem subset_filledRegion {G : SimpleGraph ι} [DecidableRel G.Adj] {S : Finset ι} {g : ι}
    (hg : g ∉ S) : S ⊆ filledRegion G S g := by
  intro x hx
  rw [mem_filledRegion]
  intro hxout
  exact outsideComponent_subset_compl hg x hxout hx

/-- **The ground vertex is outside the filled region**. -/
theorem ground_not_mem_filledRegion (G : SimpleGraph ι) [DecidableRel G.Adj] (S : Finset ι)
    (g : ι) : g ∉ filledRegion G S g := by
  rw [mem_filledRegion, not_not]
  exact ground_mem_outsideComponent G S g

/-- **The origin lies in its filled droplet** (the indicator anchor): if `g` is outside the
down-spin droplet of `i`, then `i` lies in the filled region (used with `σ_i = -1`). -/
theorem self_mem_filledRegion {G : SimpleGraph ι} [DecidableRel G.Adj] (σ : Config ι)
    (i : ι) {g : ι} (hg : g ∉ downComponent G σ i) :
    i ∈ filledRegion G (downComponent G σ i) g :=
  subset_filledRegion hg (self_mem_downComponent G σ i)

/-- **Holes are not adjacent to the outside**: a vertex of the filled region adjacent to the
outside component must lie in `S`. Hence every boundary edge of `F` has its `F`-side in `S`. -/
theorem mem_droplet_of_mem_filledRegion_adj_outside {G : SimpleGraph ι} [DecidableRel G.Adj]
    {S : Finset ι} {g a b : ι} (hg : g ∉ S) (ha : a ∈ filledRegion G S g)
    (hb : b ∈ outsideComponent G S g) (hadj : G.Adj a b) : a ∈ S := by
  by_contra haS
  -- if `a ∉ S` then the walk to `b` extends across `a-b`, putting `a` in the outside
  have hbreach : ReachableWithin G (Finset.univ \ S) g b := mem_outsideComponent.mp hb
  have haT : a ∈ Finset.univ \ S := Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, haS⟩
  have hbT : b ∈ Finset.univ \ S :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ b, outsideComponent_subset_compl hg b hb⟩
  have hreach : ReachableWithin G (Finset.univ \ S) g a := hbreach.tail ⟨hadj.symm, hbT, haT⟩
  exact (mem_filledRegion.mp ha) (mem_outsideComponent.mpr hreach)

/-- **The filled boundary is still broken bonds** (the key Peierls fact for the filled region):
when `σ_i = -1` and `g` is outside the down-spin droplet, every cut edge of the filled region
`filledRegion G (downComponent G σ i) g` lies in the phase boundary `∂σ`. Filling the holes only
removes inner-boundary edges, so the inclusion is preserved: a cut edge of `F` has its `F`-side
in the droplet (a down-spin, since holes are not adjacent to the outside) and its outside-side an
up-spin. -/
theorem cutEdges_filledRegion_downComponent_subset_phaseBoundary {G : SimpleGraph ι}
    [DecidableRel G.Adj] [Fintype G.edgeSet] {σ : Config ι} {i g : ι} (hi : σ i = Spin.down)
    (hg : g ∉ downComponent G σ i) :
    cutEdges G (filledRegion G (downComponent G σ i) g) ⊆ phaseBoundary G σ := by
  classical
  -- a cut edge of `F` with `F`-side `u` and outside-side `v` has `σ u = -1`, `σ v = +1`
  have key : ∀ u v : ι, G.Adj u v → u ∈ filledRegion G (downComponent G σ i) g →
      v ∉ filledRegion G (downComponent G σ i) g → σ u ≠ σ v := by
    intro u v huv huF hvF
    have hvout : v ∈ outsideComponent G (downComponent G σ i) g := by
      by_contra hvout; exact hvF (mem_filledRegion.mpr hvout)
    have huS : u ∈ downComponent G σ i :=
      mem_droplet_of_mem_filledRegion_adj_outside hg huF hvout huv
    have hu_down : σ u = Spin.down := (mem_downSpins σ u).mp (downComponent_subset_downSpins hi huS)
    have hv_up : σ v ≠ Spin.down := by
      intro hvd
      exact (outsideComponent_subset_compl hg v hvout)
        (mem_downComponent.mpr ((mem_downComponent.mp huS).tail
          ⟨huv, downComponent_subset_downSpins hi huS, (mem_downSpins σ v).mpr hvd⟩))
    rw [hu_down]; exact fun h => hv_up h.symm
  intro e he
  rw [cutEdges, Finset.mem_filter] at he
  obtain ⟨heG, hcross⟩ := he
  rw [mem_phaseBoundary]
  refine ⟨heG, ?_⟩
  induction e with
  | h x y =>
    rw [edgeCrosses, Sym2.lift_mk] at hcross
    rw [edgeDisagrees, Sym2.lift_mk]
    have hadj : G.Adj x y := by
      have := G.mem_edgeFinset.mp heG; rwa [SimpleGraph.mem_edgeSet] at this
    by_cases hx : x ∈ filledRegion G (downComponent G σ i) g <;>
        by_cases hy : y ∈ filledRegion G (downComponent G σ i) g
    · simp [hx, hy] at hcross
    · exact decide_eq_true (key x y hadj hx hy)
    · exact decide_eq_true (fun h => key y x hadj.symm hy hx h.symm)
    · simp [hx, hy] at hcross

end IsingModel

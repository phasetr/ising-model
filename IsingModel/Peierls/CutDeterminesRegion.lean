import IsingModel.Peierls.CutCrossingParity
import IsingModel.Peierls.FilledRegionIdempotent

/-!
# The cut determines the region (FV §3.7.2)

In a connected graph, a vertex set `F` not containing a fixed ground vertex `g` is **completely
determined by its edge cut** `cutEdges G F`: a vertex `v` lies in `F` iff a walk from `g` to `v`
crosses the cut an odd number of times (winding parity). Since the crossing count depends only on
`cutEdges G F`, two such sets with the same cut are equal.

This is a clean, general injectivity of the boundary map (stronger than the connected-droplet
version `cutEdges_injOn_connectedDroplet`, which assumed connectedness of `F`): here only
`g ∉ F` and preconnectedness are needed. It gives injectivity of `cutEdges` on filled regions,
the key to the volume-independent contour count for `m*(β)>0`.

* `mem_iff_odd_cutCrossings` — `v ∈ F ↔ Odd (cutCrossings G F w)` for a walk `w : g → v`.
* `eq_of_cutEdges_eq` — equal cuts (with `g ∉ F₁, F₂`) force `F₁ = F₂`.
* `cutEdges_injOn_not_mem_ground` — `cutEdges` is injective on sets avoiding `g`.
* `isFilled_eq_of_cutEdges_eq` — specialization to filled regions.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset SimpleGraph

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- **Membership via winding parity**: for a ground vertex `g ∉ F` and a walk `w` from `g` to
`v`, the vertex `v` lies in `F` iff `w` crosses the cut of `F` an odd number of times. -/
theorem mem_iff_odd_cutCrossings {G : SimpleGraph ι} [DecidableRel G.Adj] [Fintype G.edgeSet]
    {F : Finset ι} {g v : ι} (hg : g ∉ F) (w : G.Walk g v) :
    v ∈ F ↔ Odd (cutCrossings G F w) := by
  rw [← Nat.not_even_iff_odd, even_cutCrossings_iff]
  exact ⟨fun hv hiff => hg (hiff.mpr hv),
    fun h => by by_contra hvF; exact h (iff_of_false hg hvF)⟩

omit [Fintype ι] in
/-- **The crossing count depends only on the cut**: equal cuts give equal crossing counts along
any walk. -/
theorem cutCrossings_congr {G : SimpleGraph ι} [DecidableRel G.Adj] [Fintype G.edgeSet]
    {F₁ F₂ : Finset ι} (hcut : cutEdges G F₁ = cutEdges G F₂) {u v : ι} (w : G.Walk u v) :
    cutCrossings G F₁ w = cutCrossings G F₂ w := by
  unfold cutCrossings
  rw [hcut]

omit [Fintype ι] in
/-- **The cut determines the region** (for `g ∉ F₁, F₂` in a preconnected graph): if `F₁` and
`F₂` avoid the ground vertex `g` and have the same edge cut, then `F₁ = F₂`. Each vertex's
membership is read off from the parity of its crossing count, which is common to both. -/
theorem eq_of_cutEdges_eq {G : SimpleGraph ι} [DecidableRel G.Adj] [Fintype G.edgeSet]
    (hconn : G.Preconnected) {F₁ F₂ : Finset ι} {g : ι} (hg₁ : g ∉ F₁) (hg₂ : g ∉ F₂)
    (hcut : cutEdges G F₁ = cutEdges G F₂) : F₁ = F₂ := by
  ext v
  obtain ⟨w⟩ := hconn g v
  rw [mem_iff_odd_cutCrossings hg₁ w, mem_iff_odd_cutCrossings hg₂ w, cutCrossings_congr hcut w]

omit [Fintype ι] in
/-- **`cutEdges` is injective on sets avoiding the ground vertex** (in a preconnected graph). -/
theorem cutEdges_injOn_not_mem_ground {G : SimpleGraph ι} [DecidableRel G.Adj] [Fintype G.edgeSet]
    (hconn : G.Preconnected) (g : ι) :
    Set.InjOn (cutEdges G) {F : Finset ι | g ∉ F} :=
  fun _ hF₁ _ hF₂ hcut => eq_of_cutEdges_eq hconn hF₁ hF₂ hcut

/-- **The cut determines a filled region**: two filled regions with the same edge cut are equal
(in a preconnected graph). -/
theorem isFilled_eq_of_cutEdges_eq {G : SimpleGraph ι} [DecidableRel G.Adj] [Fintype G.edgeSet]
    (hconn : G.Preconnected) {g : ι} {F₁ F₂ : Finset ι} (hF₁ : IsFilled G g F₁)
    (hF₂ : IsFilled G g F₂) (hcut : cutEdges G F₁ = cutEdges G F₂) : F₁ = F₂ :=
  eq_of_cutEdges_eq hconn (ground_not_mem_of_isFilled hF₁) (ground_not_mem_of_isFilled hF₂) hcut

end IsingModel

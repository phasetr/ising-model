import IsingModel.Peierls.FilledRegionIdempotent

/-!
# The complement of a filled region is connected (FV §3.7.2)

A filled region `F` (`IsFilled G g F`) has, by definition, `univ \ F = outsideComponent G F g` —
a single complementary component. Hence any two vertices outside `F` are reachable from one
another while staying outside `F`. This is the first input to the discrete Jordan single-curve
theorem (`boundaryDart_single_orbit_of_connected_filled`): together with the connectivity of `F`
itself it forces the boundary darts into a single orbit.

* `reachableWithin_compl_of_isFilled` — outside vertices of a filled region are mutually reachable
  within the complement.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The complement of a filled region is connected**: if `IsFilled G g F` then any two vertices
outside `F` are reachable from one another while staying in `univ \ F` (the single outside
component). -/
theorem reachableWithin_compl_of_isFilled {G : SimpleGraph ι} [DecidableRel G.Adj]
    {F : Finset ι} {g x y : ι} (hfill : IsFilled G g F) (hx : x ∉ F) (hy : y ∉ F) :
    ReachableWithin G (Finset.univ \ F) x y := by
  have hfe : filledRegion G F g = F := hfill
  -- `z ∉ F` lands in the outside component `= univ \ F`
  have hmem : ∀ z : ι, z ∉ F → z ∈ outsideComponent G F g := by
    intro z hz
    rw [← hfe] at hz
    rwa [mem_filledRegion, not_not] at hz
  have hgx : ReachableWithin G (Finset.univ \ F) g x := mem_outsideComponent.mp (hmem x hx)
  have hgy : ReachableWithin G (Finset.univ \ F) g y := mem_outsideComponent.mp (hmem y hy)
  have hsymm : Symmetric
      (fun p q : ι => G.Adj p q ∧ p ∈ Finset.univ \ F ∧ q ∈ Finset.univ \ F) :=
    fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩
  exact (Relation.ReflTransGen.symmetric hsymm hgx).trans hgy

/-- **The complement of a filled region is a connected droplet**: `univ \ F` is connected within
itself. -/
theorem isConnectedDroplet_compl_of_isFilled {G : SimpleGraph ι} [DecidableRel G.Adj]
    {F : Finset ι} {g : ι} (hfill : IsFilled G g F) :
    IsConnectedDroplet G (Finset.univ \ F) := by
  intro x hx y hy
  rw [Finset.mem_sdiff] at hx hy
  exact reachableWithin_compl_of_isFilled hfill hx.2 hy.2

end IsingModel

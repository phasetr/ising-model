import IsingModel.Peierls.ContourCount
import IsingModel.Peierls.ContourCountCover

/-!
# The contour count assembly (FV §3.7.2)

Combining the per-anchor count `card_droplets_le_of_cut_connected` (`≤ (2d)^{2r}` for a fixed
anchor) with the anchor-cover principle `card_le_of_anchor_cover` (`r` ray anchors), the number of
droplets with a connected size-`r` dual cut is bounded by `r · (2d)^{2r}`, *volume-independently*.
The geometric inputs (injectivity, connectivity, per-anchor membership, the anchor set `Z`) are
isolated as hypotheses; the single-orbit Jordan input enters only through `IsEdgeConnected (cut S)`.

* `contour_count_le` — `|D| ≤ |Z| · (2·2)^{2r}` for the droplet family with `r` ray anchors.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, (3.49), pp. 109–116.
-/

namespace IsingModel

open Finset

/-- **The contour count assembly**: a droplet family `D` mapping injectively to connected size-`r`
edge cuts (each through one of the anchors in `Z`) has at most `|Z| · (2·2)^{2r}` members. -/
theorem contour_count_le {Λd : Finset (Fin 2 → ℤ)} (r : ℕ)
    (D : Finset (Finset (Fin 2 → ℤ))) (cut : Finset (Fin 2 → ℤ) → Finset (Sym2 ↑Λd))
    (Z : Finset ↑Λd)
    (hinj : Set.InjOn cut D)
    (hsub : ∀ S ∈ D, cut S ⊆ (Ambient.inducedGraph (latticeGraph 2) Λd).edgeFinset)
    (hconn : ∀ S ∈ D, IsEdgeConnected (cut S))
    (hcard : ∀ S ∈ D, (cut S).card = r)
    (hanchor : ∀ S ∈ D, ∃ z ∈ Z, ∃ e ∈ cut S, z ∈ e) :
    D.card ≤ Z.card * (2 * 2) ^ (2 * r) := by
  classical
  apply card_le_of_anchor_cover D Z (fun S z => ∃ e ∈ cut S, z ∈ e) ((2 * 2) ^ (2 * r)) hanchor
  intro z _hz
  refine card_droplets_le_of_cut_connected z r (D.filter (fun S => ∃ e ∈ cut S, z ∈ e)) cut
    (hinj.mono (by exact_mod_cast Finset.filter_subset _ D)) ?_ ?_ ?_ ?_
  · exact fun S hS => hsub S (Finset.mem_of_mem_filter S hS)
  · exact fun S hS => hconn S (Finset.mem_of_mem_filter S hS)
  · exact fun S hS => hcard S (Finset.mem_of_mem_filter S hS)
  · exact fun S hS => (Finset.mem_filter.mp hS).2

end IsingModel

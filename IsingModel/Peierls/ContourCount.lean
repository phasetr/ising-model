import IsingModel.Conditioning.EdgeWalkCounting
import IsingModel.Peierls.DualCutInBox

/-!
# The contour count capstone (FV §3.7.2)

The volume-independent bound on the number of contours: if a family `D` of droplets maps
**injectively** to connected edge cuts of size `r`, each inside the induced lattice graph over a box
`Λd` and each containing a fixed anchor vertex `z`, then `#D ≤ (2d)^{2r}`. This is the direct
consequence of the walk-counting bound `card_connected_edge_sets_inducedLatticeGraph_le`, with the
geometric inputs (injectivity, connectivity, anchor) isolated as hypotheses.

* `card_droplets_le_of_cut_connected` — the single-anchor contour count.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, (3.49), pp. 109–116.
-/

namespace IsingModel

open Finset

/-- **Contour count capstone** (single anchor): a family `D` of droplets mapping injectively to
connected size-`r` edge cuts (in the induced lattice graph over `Λd`, each through the anchor `z`)
has at most `(2·2)^{2r}` members. -/
theorem card_droplets_le_of_cut_connected {Λd : Finset (Fin 2 → ℤ)} (z : ↑Λd) (r : ℕ)
    (D : Finset (Finset (Fin 2 → ℤ)))
    (cut : Finset (Fin 2 → ℤ) → Finset (Sym2 ↑Λd))
    (hinj : Set.InjOn cut D)
    (hsub : ∀ F ∈ D, cut F ⊆ (Ambient.inducedGraph (latticeGraph 2) Λd).edgeFinset)
    (hconn : ∀ F ∈ D, IsEdgeConnected (cut F))
    (hcard : ∀ F ∈ D, (cut F).card = r)
    (hanchor : ∀ F ∈ D, ∃ e ∈ cut F, z ∈ e) :
    D.card ≤ (2 * 2) ^ (2 * r) := by
  classical
  have hbound : (D.image cut).card ≤ (2 * 2) ^ (2 * r) :=
    card_connected_edge_sets_inducedLatticeGraph_le Λd z r (D.image cut) (by
      intro C hC
      rw [Finset.mem_image] at hC
      obtain ⟨F, hF, rfl⟩ := hC
      exact ⟨hsub F hF, hconn F hF, hcard F hF, hanchor F hF⟩)
  rwa [Finset.card_image_of_injOn hinj] at hbound

end IsingModel

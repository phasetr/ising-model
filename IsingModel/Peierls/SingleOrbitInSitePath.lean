import IsingModel.Peierls.SingleOrbitContactMove
import IsingModel.Peierls.ConnectedDroplet

/-!
# Chaining the per-edge advance along an `F`-path (FV §3.7.2)

The `F`-path induction at the contact-graph level: given a per-edge advance -- for any contact pair
`c` and any `F`-neighbour `a'` of its in-site, a contact pair `c'` at `a'` connected to `c` by
contact moves -- the connectivity chains along a within-`F` path. Hence from any contact pair one
reaches a connected contact pair at any `F`-reachable in-site
(`reflTransGen_contactMove_of_inSite_reachable`).
This is the chaining half of the basepoint connectivity; supplying the per-edge advance (from the
wedge construction) and the same-vertex wedge then closes the global argument.

* `reflTransGen_contactMove_of_inSite_reachable` — the per-edge advance chains along an `F`-path.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- **Chaining the per-edge advance along an `F`-path**: if for every contact pair `c` and every
`F`-neighbour `a'` of `c.inSite` there is a contact pair `c'` at `a'` connected to `c` by contact
moves, then from any contact pair `c` one reaches a connected contact pair at any in-site `a'`
reachable within `F` from `c.inSite`. -/
theorem reflTransGen_contactMove_of_inSite_reachable
    (hstep : ∀ (c : ContactPair F) (a' : Fin 2 → ℤ),
      (latticeGraph 2).Adj c.inSite a' → a' ∈ F →
        ∃ c' : ContactPair F, c'.inSite = a' ∧ Relation.ReflTransGen ContactMove c c')
    (c : ContactPair F) {a' : Fin 2 → ℤ}
    (hpath : ReachableWithin (latticeGraph 2) F c.inSite a') :
    ∃ c' : ContactPair F, c'.inSite = a' ∧ Relation.ReflTransGen ContactMove c c' := by
  induction hpath with
  | refl => exact ⟨c, rfl, Relation.ReflTransGen.refl⟩
  | tail _ hedge ih =>
    obtain ⟨cmid, hmid_in, hmid_conn⟩ := ih
    obtain ⟨hadj, _, ha'F⟩ := hedge
    rw [← hmid_in] at hadj
    obtain ⟨c', hc'_in, hc'_conn⟩ := hstep cmid _ hadj ha'F
    exact ⟨c', hc'_in, hmid_conn.trans hc'_conn⟩

end IsingModel

import IsingModel.Peierls.SingleOrbitGeometric

/-!
# Single orbit from connected-`F` inputs (FV §3.7.2)

The `F`-reachability input `hreach` of `boundaryDart_single_orbit_of_geometric_inputs` is exactly
within-`F` connectivity of `F`, since every contact-pair in-site lies in `F`
(`reachable_inSite_of_connected`). Substituting it gives a capstone needing only a per-edge advance,
same-vertex wedge connectivity, and connectivity of `F`
(`boundaryDart_single_orbit_of_connected_inputs`) — the form in which the connectedness of the spin
droplet enters. Only the per-edge advance and same-vertex inputs (the wedge/filled geometry) then
remain.

* `reachable_inSite_of_connected` — `F`-connectivity gives the `hreach` input.
* `boundaryDart_single_orbit_of_connected_inputs` — `hone` from advance, wedge, `F`-connectivity.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- **`F`-connectivity gives the reachability input**: if any two vertices of `F` are reachable
within `F`, then every contact-pair in-site reaches the basepoint in-site. -/
theorem reachable_inSite_of_connected (c₀ : ContactPair F)
    (hFconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b)
    (c : ContactPair F) : ReachableWithin (latticeGraph 2) F c.inSite c₀.inSite :=
  hFconn c.inSite c.inSite_mem c₀.inSite c₀.inSite_mem

/-- **Single orbit from connected-`F` inputs**: `hone` follows from a per-edge advance `hstep`,
same-vertex wedge connectivity `hsame`, and within-`F` connectivity of `F`. -/
theorem boundaryDart_single_orbit_of_connected_inputs (c₀ : ContactPair F)
    (hstep : ∀ (c : ContactPair F) (a' : Fin 2 → ℤ),
      (latticeGraph 2).Adj c.inSite a' → a' ∈ F →
        ∃ c' : ContactPair F, c'.inSite = a' ∧ Relation.ReflTransGen ContactMove c c')
    (hsame : ∀ c c' : ContactPair F, c.inSite = c'.inSite →
      Relation.ReflTransGen ContactMove c c')
    (hFconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b)
    (d e : BoundaryDart F) : d.SameOrbit e :=
  boundaryDart_single_orbit_of_geometric_inputs c₀ hstep hsame
    (reachable_inSite_of_connected c₀ hFconn) d e

end IsingModel

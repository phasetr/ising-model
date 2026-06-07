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

**Caveat (design):** the `hsame` argument as stated here — connecting *all* contact pairs sharing an
in-site — is too strong to discharge directly: at a pinch vertex of a filled region the complement
splits into two arcs whose darts lie in different local wedges, joined only by traversing the whole
boundary (i.e. by the very single-orbit property being proved). The sound route keeps the global
invariant at the *contact-pair/wedge* level (controlled advances plus same-arc connectivity, as in
`reflTransGen_contactMove_same_inSite_arc` and `reflTransGen_contactMove_advance`) rather than at
the vertex level; this statement is a valid conditional reduction but should not be used as the
final entry point.

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

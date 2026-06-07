import IsingModel.Peierls.SingleOrbitInSitePath

/-!
# Basepoint connectivity from the geometric inputs (FV §3.7.2)

Assembling the `F`-path chaining into basepoint connectivity, isolating the three geometric inputs
the global filled-region argument must supply: a per-edge advance (`hstep`), same-vertex wedge
connectivity (`hsame`, joining contact pairs sharing an in-site), and `F`-reachability of every
in-site to the basepoint's (`hreach`, from connectedness of `F`). Under these, every contact pair
reaches the fixed basepoint by contact moves (`reflTransGen_contactMove_to_basepoint`) — walk the
in-site back to the basepoint vertex (chaining), then rotate within the basepoint wedge.

**Caveat (design):** the `hsame` argument (joining *all* contact pairs at a shared in-site) is too
strong to discharge — at a pinch vertex of a filled region it is circular with single-orbit. This is
a valid conditional reduction; the sound discharge keeps the global invariant at the
contact-pair/wedge level (controlled advances + same-arc connectivity), not the vertex level.

* `reflTransGen_contactMove_to_basepoint` — basepoint connectivity from the three geometric inputs.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- **Basepoint connectivity from the geometric inputs**: given a per-edge advance `hstep`,
same-vertex wedge connectivity `hsame`, and `F`-reachability `hreach` of every in-site to
`c₀.inSite`, every contact pair reaches the basepoint `c₀` by contact moves. -/
theorem reflTransGen_contactMove_to_basepoint (c₀ : ContactPair F)
    (hstep : ∀ (c : ContactPair F) (a' : Fin 2 → ℤ),
      (latticeGraph 2).Adj c.inSite a' → a' ∈ F →
        ∃ c' : ContactPair F, c'.inSite = a' ∧ Relation.ReflTransGen ContactMove c c')
    (hsame : ∀ c c' : ContactPair F, c.inSite = c'.inSite →
      Relation.ReflTransGen ContactMove c c')
    (hreach : ∀ c : ContactPair F,
      ReachableWithin (latticeGraph 2) F c.inSite c₀.inSite)
    (c : ContactPair F) : Relation.ReflTransGen ContactMove c c₀ := by
  obtain ⟨c'', hc''_in, hc''_conn⟩ :=
    reflTransGen_contactMove_of_inSite_reachable hstep c (hreach c)
  exact hc''_conn.trans (hsame c'' c₀ hc''_in)

end IsingModel

import IsingModel.Peierls.SingleOrbitToBasepoint
import IsingModel.Peierls.SingleOrbitFromBasepoint

/-!
# Single orbit from the geometric inputs (FV §3.7.2)

The full reduction capstone: the single-orbit `hone` input of the Peierls bound follows from exactly
three geometric inputs about a region `F` with a basepoint contact pair `c₀` — a per-edge advance
(`hstep`), same-vertex wedge connectivity (`hsame`), and `F`-reachability of every in-site to
`c₀.inSite` (`hreach`). It composes the basepoint reduction
(`reflTransGen_contactMove_to_basepoint`) with the single-orbit capstone
(`boundaryDart_single_orbit_of_contactPair_basepoint`). The remaining work is supplying these three
inputs from connectedness and filledness of `F` — the orbit/contact machinery is otherwise complete.

* `boundaryDart_single_orbit_of_geometric_inputs` — `hone` from the three geometric inputs.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- **Single orbit from the geometric inputs**: given a basepoint contact pair `c₀`, a per-edge
advance `hstep`, same-vertex wedge connectivity `hsame`, and `F`-reachability `hreach` of every
in-site to `c₀.inSite`, every two boundary darts are in the same orbit (the `hone` input). -/
theorem boundaryDart_single_orbit_of_geometric_inputs (c₀ : ContactPair F)
    (hstep : ∀ (c : ContactPair F) (a' : Fin 2 → ℤ),
      (latticeGraph 2).Adj c.inSite a' → a' ∈ F →
        ∃ c' : ContactPair F, c'.inSite = a' ∧ Relation.ReflTransGen ContactMove c c')
    (hsame : ∀ c c' : ContactPair F, c.inSite = c'.inSite →
      Relation.ReflTransGen ContactMove c c')
    (hreach : ∀ c : ContactPair F,
      ReachableWithin (latticeGraph 2) F c.inSite c₀.inSite)
    (d e : BoundaryDart F) : d.SameOrbit e :=
  boundaryDart_single_orbit_of_contactPair_basepoint c₀
    (reflTransGen_contactMove_to_basepoint c₀ hstep hsame hreach) d e

end IsingModel

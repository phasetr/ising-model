import IsingModel.Peierls.SingleOrbitBasepoint
import IsingModel.Peierls.SingleOrbitFromConnected

/-!
# Single orbit from basepoint connectivity (FV §3.7.2)

Composing the basepoint reduction with the connectivity capstone: if every contact pair of `F`
reaches one fixed basepoint by contact moves, then every two boundary darts are in the same orbit
(`boundaryDart_single_orbit_of_contactPair_basepoint`). This is the cleanest entry point for the
remaining global argument — supplying `∀ c, ReflTransGen ContactMove c c₀` (a boundary walk back
to a fixed contact pair) yields the `hone` input of the Peierls bound directly.

* `boundaryDart_single_orbit_of_contactPair_basepoint` — basepoint connectivity gives single orbit.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

variable {F : Finset (Fin 2 → ℤ)}

/-- **Single orbit from basepoint connectivity**: if every contact pair reaches a fixed basepoint
`c₀` by contact moves, then every two boundary darts are in the same orbit (the `hone` input). -/
theorem boundaryDart_single_orbit_of_contactPair_basepoint (c₀ : ContactPair F)
    (h : ∀ c : ContactPair F, Relation.ReflTransGen ContactMove c c₀)
    (d e : BoundaryDart F) : d.SameOrbit e :=
  boundaryDart_single_orbit_of_contactPair_connected
    (reflTransGen_contactMove_of_basepoint c₀ h) d e

end IsingModel

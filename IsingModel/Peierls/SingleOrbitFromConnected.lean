import IsingModel.Peierls.SingleOrbitContactMove

/-!
# Single orbit from contact-pair connectivity (FV §3.7.2)

The capstone reduction: if every two contact pairs of `F` are joined by a chain of contact moves,
then every two boundary darts are in the same orbit
(`boundaryDart_single_orbit_of_contactPair_connected`). This is the `hone` input of the Peierls
bound, now reduced to the orbit-free planar connectivity of the contact graph — the only remaining
content. The reduction is a direct application of the dart-level push-down
`sameOrbit_of_dart_contactMove_chain`.

* `boundaryDart_single_orbit_of_contactPair_connected` — connectivity gives the single-orbit input.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- **Single orbit from contact-pair connectivity**: if every two contact pairs of `F` are joined by
a chain of contact moves, then every two boundary darts are in the same orbit (the `hone` input of
the Peierls bound). -/
theorem boundaryDart_single_orbit_of_contactPair_connected
    (hconn : ∀ c c' : ContactPair F, Relation.ReflTransGen ContactMove c c')
    (d e : BoundaryDart F) : d.SameOrbit e :=
  sameOrbit_of_dart_contactMove_chain d e (hconn d.toContactPair e.toContactPair)

end IsingModel

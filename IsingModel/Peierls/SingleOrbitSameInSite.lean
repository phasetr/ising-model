import IsingModel.Peierls.SingleOrbitSameLeftArc
import IsingModel.Peierls.SingleOrbitContactEquiv

/-!
# Same-in-site contact pairs across an arc (FV §3.7.2)

The same-vertex wedge connectivity at the contact-graph level: two contact pairs sharing an in-site,
whose realizing darts differ by a left rotation through an exposed complement arc, are connected by
contact moves (`reflTransGen_contactMove_same_inSite_arc`). This is the building block of the
`hsame` input of `boundaryDart_single_orbit_of_geometric_inputs`; the global argument supplies
the arc condition so that *any* two contact pairs at a vertex are connected.

* `reflTransGen_contactMove_same_inSite_arc` — same-in-site, arc-connected contact pairs are joined.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- **Same-in-site contact pairs across an arc are connected**: if `c`, `c'` share an in-site,
`c'.toDart.dir = turnLeft^[n] c.toDart.dir`, and the arc out-sites `c.inSite + (turnLeft^[i]
c.toDart.dir).vec` for `i < n` lie outside `F`, then `c` and `c'` are joined by contact moves. -/
theorem reflTransGen_contactMove_same_inSite_arc (c c' : ContactPair F) {n : ℕ}
    (hin : c'.inSite = c.inSite)
    (hdir : c'.toDart.dir = (Dir2.turnLeft^[n]) c.toDart.dir)
    (harc : ∀ i < n, c.inSite + ((Dir2.turnLeft^[i]) c.toDart.dir).vec ∉ F) :
    Relation.ReflTransGen ContactMove c c' := by
  have hso : c.toDart.SameOrbit c'.toDart := by
    apply sameOrbit_of_same_left_arc c.toDart c'.toDart
    · rw [ContactPair.toDart_left, ContactPair.toDart_left]; exact hin
    · exact hdir
    · intro i hi
      rw [ContactPair.toDart_left]
      exact harc i hi
  have hconn := reflTransGen_contactMove_of_sameOrbit c.toDart c'.toDart hso
  rwa [toDart_toContactPair, toDart_toContactPair] at hconn

end IsingModel

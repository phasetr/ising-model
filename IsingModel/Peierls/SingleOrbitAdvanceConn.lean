import IsingModel.Peierls.SingleOrbitAdvanceMem
import IsingModel.Peierls.SingleOrbitContactEquiv

/-!
# Contact-move advance to an adjacent vertex (FV §3.7.2)

The membership-driven orbit advance lifted to contact-move connectivity: under the three local
membership conditions of `sameOrbit_advance_of_membership`, the contact pair of `d` is joined by a
chain of contact moves to the contact pair of the advanced dart, whose in-site is the adjacent
`F`-vertex `d.left + (turnLeft^[n] d.dir).vec` (`reflTransGen_contactMove_advance`). This is
the per-edge step the global `F`-path connectivity argument chains, now stated entirely at the
contact-graph level.

* `reflTransGen_contactMove_advance` — connectivity to the adjacent-vertex contact pair.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- **Contact-move advance to an adjacent vertex**: under the membership conditions of
`sameOrbit_advance_of_membership`, the contact pair of `d` is contact-move connected to the contact
pair of `nextDart^[n+1] d`, whose in-site is `d.left + (turnLeft^[n] d.dir).vec`. -/
theorem reflTransGen_contactMove_advance (d : BoundaryDart F) {n : ℕ}
    (harc : ∀ i < n, d.left + ((Dir2.turnLeft^[i]) d.dir).vec ∉ F)
    (hstop : d.left + ((Dir2.turnLeft^[n]) d.dir).vec ∈ F)
    (hout : rightSite (BoundaryDart.nextDart^[n] d).head ((Dir2.turnLeft^[n]) d.dir) ∉ F) :
    Relation.ReflTransGen ContactMove d.toContactPair
        (BoundaryDart.nextDart^[n + 1] d).toContactPair ∧
      (BoundaryDart.nextDart^[n + 1] d).toContactPair.inSite
        = d.left + ((Dir2.turnLeft^[n]) d.dir).vec := by
  obtain ⟨hso, hleft⟩ := sameOrbit_advance_of_membership d harc hstop hout
  exact ⟨reflTransGen_contactMove_of_sameOrbit d _ hso, hleft⟩

end IsingModel

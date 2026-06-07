import IsingModel.Peierls.SingleOrbitWedge
import IsingModel.Peierls.SingleOrbitFanComplete
import IsingModel.Peierls.SingleOrbitTransport

/-!
# Left-fan reach through a complement arc (FV §3.7.2)

Using the validity criterion `leftFan_next_turnLeft_valid_iff`, a left-fan prefix exists for as long
as the successive out-sites stay outside `F`: `leftFanPrefix_of_outSites_not_mem` builds the prefix
by induction, each step's validity supplied by the membership condition. Consequently, if the
out-sites `d.left + (turnLeft^[i] d.dir).vec` for `i < n` are all outside `F`, the orbit of `d`
contains a dart at the same left site with direction `turnLeft^[n] d.dir`
(`exists_orbit_dart_left_rotated_of_outSites`). This is the (purely local) wedge-existence: rotating
left through an exposed complement arc reaches every direction in the arc, with no global filledness
hypothesis — the global argument later supplies the arc condition.

* `leftFanPrefix_of_outSites_not_mem` — out-side membership builds the fan prefix.
* `exists_orbit_dart_left_rotated_of_outSites` — the wedge reach to a rotated direction.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- **Out-side membership builds a left-fan prefix**: if each out-site
`d.left + (turnLeft^[i] d.dir).vec` for `i < n` lies outside `F`, then `d.LeftFanPrefix n`. -/
theorem leftFanPrefix_of_outSites_not_mem (d : BoundaryDart F) {n : ℕ}
    (h : ∀ i < n, d.left + ((Dir2.turnLeft^[i]) d.dir).vec ∉ F) : d.LeftFanPrefix n := by
  induction n with
  | zero => exact leftFanPrefix_zero d
  | succ m ih =>
    have hm : d.LeftFanPrefix m := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    apply leftFanPrefix_succ d hm
    rw [leftFan_next_turnLeft_valid_iff d hm]
    exact h m (Nat.lt_succ_self m)

/-- **Wedge reach to a rotated direction**: if the out-sites `d.left + (turnLeft^[i] d.dir).vec` for
`i < n` are all outside `F`, then `d`'s orbit contains a dart at the same left site with direction
`turnLeft^[n] d.dir`. -/
theorem exists_orbit_dart_left_rotated_of_outSites (d : BoundaryDart F) {n : ℕ}
    (h : ∀ i < n, d.left + ((Dir2.turnLeft^[i]) d.dir).vec ∉ F) :
    ∃ e : BoundaryDart F, d.SameOrbit e ∧ e.left = d.left ∧ e.dir = (Dir2.turnLeft^[n]) d.dir := by
  have hfan : d.LeftFanPrefix n := leftFanPrefix_of_outSites_not_mem d h
  exact exists_orbit_dart_at_left_with_dir d ((Dir2.turnLeft^[n]) d.dir) hfan
    (dir_eq_iterate_of_leftFanPrefix d hfan)

end IsingModel

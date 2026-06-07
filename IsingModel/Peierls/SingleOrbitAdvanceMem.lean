import IsingModel.Peierls.SingleOrbitAdvance
import IsingModel.Peierls.SingleOrbitWedgeReach
import IsingModel.Peierls.SingleOrbitWedge

/-!
# Membership form of the orbit advance (FV §3.7.2)

The per-edge transport `sameOrbit_iterate_succ_left` restated purely in terms of `F`-membership of
the local sites, the form the global filled-region argument supplies. The left fan rotates while the
out-sites stay outside `F` (`harc`); it stops when the next rotated step lands on an `F`-vertex
(`hstop`, which both halts the fan and provides the straight step's `F`-side); and the straight
slide is valid when its out-site is outside `F` (`hout`). Under these three conditions the orbit
advances to a dart at the adjacent `F`-vertex `d.left + (turnLeft^[n] d.dir).vec`
(`sameOrbit_advance_of_membership`).

* `sameOrbit_advance_of_membership` — the membership-driven per-edge transport.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- **Membership-driven orbit advance**: if the out-sites `d.left + (turnLeft^[i] d.dir).vec` for
`i < n` lie outside `F`, the `n`-th rotated step `d.left + (turnLeft^[n] d.dir).vec` is inside `F`,
and the straight out-site `rightSite (nextDart^[n] d).head (turnLeft^[n] d.dir)` lies outside `F`,
then `d`'s orbit reaches a dart at the adjacent `F`-vertex `d.left + (turnLeft^[n] d.dir).vec`. -/
theorem sameOrbit_advance_of_membership (d : BoundaryDart F) {n : ℕ}
    (harc : ∀ i < n, d.left + ((Dir2.turnLeft^[i]) d.dir).vec ∉ F)
    (hstop : d.left + ((Dir2.turnLeft^[n]) d.dir).vec ∈ F)
    (hout : rightSite (BoundaryDart.nextDart^[n] d).head ((Dir2.turnLeft^[n]) d.dir) ∉ F) :
    d.SameOrbit (BoundaryDart.nextDart^[n + 1] d) ∧
      (BoundaryDart.nextDart^[n + 1] d).left = d.left + ((Dir2.turnLeft^[n]) d.dir).vec := by
  have hfan : d.LeftFanPrefix n := leftFanPrefix_of_outSites_not_mem d harc
  have heL := left_eq_iterate_of_leftFanPrefix d hfan
  have heD := dir_eq_iterate_of_leftFanPrefix d hfan
  have hLinv : ¬ ValidAt F (BoundaryDart.nextDart^[n] d).head
      (BoundaryDart.nextDart^[n] d).dir.turnLeft := by
    rw [leftFan_next_turnLeft_valid_iff d hfan]; exact not_not.mpr hstop
  have hS : ValidAt F (BoundaryDart.nextDart^[n] d).head (BoundaryDart.nextDart^[n] d).dir := by
    refine ⟨?_, ?_⟩
    · have hl : leftSite (BoundaryDart.nextDart^[n] d).head (BoundaryDart.nextDart^[n] d).dir
          = (BoundaryDart.nextDart^[n] d).left + (BoundaryDart.nextDart^[n] d).dir.vec := by
        change leftSite ((BoundaryDart.nextDart^[n] d).tail + (BoundaryDart.nextDart^[n] d).dir.vec)
            (BoundaryDart.nextDart^[n] d).dir
          = leftSite (BoundaryDart.nextDart^[n] d).tail (BoundaryDart.nextDart^[n] d).dir
            + (BoundaryDart.nextDart^[n] d).dir.vec
        rw [leftSite_add]
      rw [hl, heL, heD]; exact hstop
    · rw [heD]; exact hout
  exact sameOrbit_iterate_succ_left d hfan hLinv hS

end IsingModel

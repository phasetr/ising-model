import IsingModel.Peierls.SingleOrbitFanComplete
import IsingModel.Peierls.SingleOrbitContact

/-!
# Straight-slide transport and fan reach (FV §3.7.2)

Two free transport facts the global connectivity argument uses. The **straight slide** transports a
boundary dart across one lattice edge: when `nextDart` goes straight, the new dart is determined by
its sites, so any dart with those sites is in the same orbit (`sameOrbit_of_straight_slide`). And a
**fan reach** picks out, inside `d`'s orbit, a dart with the same left site and a direction reached
by a left-fan prefix (`exists_orbit_dart_at_left_with_dir`). Both are immediate from the existing
orbit/fan lemmas; the only genuinely new ingredient still missing for full connectivity is the
existence of a left-fan prefix reaching the exit direction of the exposed wedge.

* `sameOrbit_of_straight_slide` — a straight step transports the dart across one edge.
* `exists_orbit_dart_at_left_with_dir` — a fan prefix reaches a dart at the same left site.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- **Straight-slide transport**: if `nextDart` goes straight at `d` (left turn invalid, straight
valid) and `d'` carries the straight head sites, then `d` and `d'` are in the same orbit. -/
theorem sameOrbit_of_straight_slide (d d' : BoundaryDart F)
    (hLinv : ¬ ValidAt F d.head d.dir.turnLeft) (hS : ValidAt F d.head d.dir)
    (hL : d'.left = leftSite d.head d.dir) (hR : d'.right = rightSite d.head d.dir) :
    d.SameOrbit d' := by
  have hstep : d.nextDart = d' := by
    rw [nextDart_eq_straight d hLinv hS]
    exact BoundaryDart.ext_of_left_right hL.symm hR.symm
  rw [← hstep]
  exact d.sameOrbit_nextDart

/-- **Fan reach**: a left-fan prefix from `d` reaching direction `δ` produces an orbit dart at the
same left site with direction `δ`. -/
theorem exists_orbit_dart_at_left_with_dir (d : BoundaryDart F) (δ : Dir2) {k : ℕ}
    (hfan : d.LeftFanPrefix k) (hδ : (BoundaryDart.nextDart^[k] d).dir = δ) :
    ∃ e : BoundaryDart F, d.SameOrbit e ∧ e.left = d.left ∧ e.dir = δ :=
  ⟨BoundaryDart.nextDart^[k] d, d.sameOrbit_iterate k, left_eq_iterate_of_leftFanPrefix d hfan, hδ⟩

end IsingModel

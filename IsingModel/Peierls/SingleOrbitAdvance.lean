import IsingModel.Peierls.SingleOrbitWedgeReach
import IsingModel.Peierls.SingleOrbitFanComplete

/-!
# Orbit advance to an adjacent vertex (FV §3.7.2)

Combining a left-fan rotation with one straight slide: after a left-fan prefix of length `n` and a
straight step, the orbit reaches a dart whose left site is the adjacent `F`-vertex
`d.left + (turnLeft^[n] d.dir).vec` (`sameOrbit_iterate_succ_left`). This is how the boundary orbit
moves from one `F`-vertex to a neighbour: rotate to point along the chosen exposed edge, then slide
across it. It is the per-edge transport step of the global connectivity argument.

* `sameOrbit_iterate_succ_left` — the orbit advances to the adjacent vertex along a slide.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- **Orbit advance to an adjacent vertex**: if the first `n` steps from `d` are left turns and the
`n`-th iterate then goes straight, the `(n+1)`-th iterate is in `d`'s orbit and its left site is the
adjacent `F`-vertex `d.left + (turnLeft^[n] d.dir).vec`. -/
theorem sameOrbit_iterate_succ_left (d : BoundaryDart F) {n : ℕ} (hfan : d.LeftFanPrefix n)
    (hLinv : ¬ ValidAt F (BoundaryDart.nextDart^[n] d).head
      (BoundaryDart.nextDart^[n] d).dir.turnLeft)
    (hS : ValidAt F (BoundaryDart.nextDart^[n] d).head (BoundaryDart.nextDart^[n] d).dir) :
    d.SameOrbit (BoundaryDart.nextDart^[n + 1] d) ∧
      (BoundaryDart.nextDart^[n + 1] d).left = d.left + ((Dir2.turnLeft^[n]) d.dir).vec := by
  refine ⟨d.sameOrbit_iterate (n + 1), ?_⟩
  rw [Function.iterate_succ_apply',
    left_nextDart_of_straight (BoundaryDart.nextDart^[n] d) hLinv hS]
  have hadd : leftSite (BoundaryDart.nextDart^[n] d).head (BoundaryDart.nextDart^[n] d).dir
      = (BoundaryDart.nextDart^[n] d).left + (BoundaryDart.nextDart^[n] d).dir.vec := by
    change leftSite ((BoundaryDart.nextDart^[n] d).tail + (BoundaryDart.nextDart^[n] d).dir.vec)
        (BoundaryDart.nextDart^[n] d).dir
      = leftSite (BoundaryDart.nextDart^[n] d).tail (BoundaryDart.nextDart^[n] d).dir
        + (BoundaryDart.nextDart^[n] d).dir.vec
    rw [leftSite_add]
  rw [hadd, left_eq_iterate_of_leftFanPrefix d hfan, dir_eq_iterate_of_leftFanPrefix d hfan]

end IsingModel

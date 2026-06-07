import IsingModel.Peierls.SingleOrbitWedgeReach

/-!
# Same-site darts across a complement arc (FV §3.7.2)

The wedge reach turned into a same-orbit statement: two boundary darts at the **same left site**
whose directions differ by a left rotation through an exposed complement arc are in the same orbit
(`sameOrbit_of_same_left_arc`). This is the same-vertex connectivity — all boundary darts exposed in
one complement wedge at a fixed `F`-vertex lie in one orbit. The auxiliary
`BoundaryDart.ext_of_left_dir` records that a dart is determined by its left site and direction.

* `BoundaryDart.ext_of_left_dir` — a dart is determined by its left site and direction.
* `sameOrbit_of_same_left_arc` — same-site darts across an exposed arc share an orbit.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- **A dart is determined by its left site and direction**. -/
theorem BoundaryDart.ext_of_left_dir {d e : BoundaryDart F} (hL : d.left = e.left)
    (hdir : d.dir = e.dir) : d = e := by
  apply BoundaryDart.ext' _ hdir
  change leftSite d.tail d.dir = leftSite e.tail e.dir at hL
  rw [← hdir] at hL
  exact leftSite_injective_tail d.dir hL

/-- **Same-site darts across a complement arc share an orbit**: if `d` and `d'` have the same left
site, `d'.dir = turnLeft^[n] d.dir`, and the arc out-sites `d.left + (turnLeft^[i] d.dir).vec` for
`i < n` all lie outside `F`, then `d` and `d'` are in the same orbit. -/
theorem sameOrbit_of_same_left_arc (d d' : BoundaryDart F) {n : ℕ}
    (hL : d'.left = d.left) (hdir : d'.dir = (Dir2.turnLeft^[n]) d.dir)
    (h : ∀ i < n, d.left + ((Dir2.turnLeft^[i]) d.dir).vec ∉ F) : d.SameOrbit d' := by
  obtain ⟨e, hso, heL, heDir⟩ := exists_orbit_dart_left_rotated_of_outSites d h
  have hed : e = d' := by
    apply BoundaryDart.ext_of_left_dir
    · rw [heL, hL]
    · rw [heDir, hdir]
  rw [← hed]; exact hso

end IsingModel

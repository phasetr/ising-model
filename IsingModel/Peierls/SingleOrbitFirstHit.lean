import IsingModel.Peierls.SingleOrbitDirCycle
import IsingModel.Peierls.BoundaryDart

/-!
# First exposed direction hitting `F` (FV §3.7.2)

Rotating left from a direction, the lattice point `a + (turnLeft^[k] dir).vec` sweeps the four
neighbours of `a`. If some rotation lands inside `F` then there is a **first** one
(`exists_first_turnLeft_mem`): an index `n < 4` whose rotated point lies in `F` while every earlier
rotation lands outside `F`. The intermediate "outside" run is exactly the cleared complement arc the
wedge advance needs, and the landing point is the adjacent `F`-vertex the orbit slides to. This is
the cyclic-order ingredient of the contact-pair route: it produces the arc-and-stop data for
`sameOrbit_advance_of_membership` from pure membership.

* `exists_first_turnLeft_mem` — the first left-rotation landing inside `F`, with the cleared arc.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

/-- **First exposed direction hitting `F`**: if some rotation `a + (turnLeft^[k] dir).vec` (`k < 4`)
lies in `F`, then there is a first such index `n < 4` — every earlier rotation lies outside `F`, and
the `n`-th lies inside. -/
theorem exists_first_turnLeft_mem (F : Finset (Fin 2 → ℤ)) (a : Fin 2 → ℤ) (dir : Dir2)
    (h : ∃ k, k < 4 ∧ a + ((Dir2.turnLeft^[k]) dir).vec ∈ F) :
    ∃ n, n < 4 ∧ (∀ i < n, a + ((Dir2.turnLeft^[i]) dir).vec ∉ F) ∧
      a + ((Dir2.turnLeft^[n]) dir).vec ∈ F := by
  classical
  obtain ⟨k, hk4, hkF⟩ := h
  have hex : ∃ n, a + ((Dir2.turnLeft^[n]) dir).vec ∈ F := ⟨k, hkF⟩
  refine ⟨Nat.find hex, lt_of_le_of_lt (Nat.find_le hkF) hk4, fun i hi => Nat.find_min hex hi,
    Nat.find_spec hex⟩

end IsingModel

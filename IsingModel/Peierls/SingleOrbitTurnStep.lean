import IsingModel.Peierls.SingleOrbitFanOne
import IsingModel.Peierls.SingleOrbitFanComplete
import IsingModel.Peierls.SingleOrbitContactGen

/-!
# Elementary single-turn steps (FV §3.7.2)

The `k = 1` specialisations of the fan completeness and contact-move generators: a single valid turn
between darts sharing a site. At the dart level, two darts with the same left site whose directions
differ by one valid left turn are in the same orbit (`sameOrbit_of_left_turn_step`), dually for the
right turn (`sameOrbit_of_right_turn_step`). At the contact-pair level these are one-edge
`ReflTransGen ContactMove` facts (`reflTransGen_contactMove_left_turn` / `_right_turn`). These are
atomic wedge rotations the global connectivity argument applies step by step.

* `sameOrbit_of_left_turn_step` / `sameOrbit_of_right_turn_step` — single-turn same-orbit steps.
* `reflTransGen_contactMove_left_turn` / `_right_turn` — single-turn contact-move edges.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- **Single left-turn same-orbit step**: darts sharing a left site whose directions differ by one
valid left turn are in the same orbit. -/
theorem sameOrbit_of_left_turn_step (d e : BoundaryDart F) (hL : e.left = d.left)
    (hvalid : ValidAt F d.head d.dir.turnLeft) (hdir : e.dir = d.dir.turnLeft) :
    d.SameOrbit e := by
  refine sameOrbit_of_leftFanPrefix_dir_eq d e (leftFanPrefix_one d hvalid) hL ?_
  simpa using hdir

/-- **Single right-turn same-orbit step**: darts sharing a right site whose directions differ by one
right turn are in the same orbit. -/
theorem sameOrbit_of_right_turn_step (d e : BoundaryDart F) (hR : e.right = d.right)
    (hL : ¬ ValidAt F d.head d.dir.turnLeft) (hS : ¬ ValidAt F d.head d.dir)
    (hdir : e.dir = d.dir.turnRight) : d.SameOrbit e := by
  refine sameOrbit_of_rightFanPrefix_dir_eq d e (rightFanPrefix_one d hL hS) hR ?_
  simpa using hdir

/-- **Single left-turn contact-move edge**: contact pairs sharing an in-site whose realizing darts
differ by one valid left turn are joined by a contact move. -/
theorem reflTransGen_contactMove_left_turn (c c' : ContactPair F) (hin : c.inSite = c'.inSite)
    (hvalid : ValidAt F c.toDart.head c.toDart.dir.turnLeft)
    (hdir : c'.toDart.dir = c.toDart.dir.turnLeft) :
    Relation.ReflTransGen ContactMove c c' := by
  refine reflTransGen_contactMove_of_same_inSite_leftFanPrefix c c' hin
    (leftFanPrefix_one c.toDart hvalid) ?_
  simpa using hdir

/-- **Single right-turn contact-move edge**: contact pairs sharing an out-site whose realizing darts
differ by one right turn are joined by a contact move. -/
theorem reflTransGen_contactMove_right_turn (c c' : ContactPair F) (hout : c.outSite = c'.outSite)
    (hL : ¬ ValidAt F c.toDart.head c.toDart.dir.turnLeft)
    (hS : ¬ ValidAt F c.toDart.head c.toDart.dir)
    (hdir : c'.toDart.dir = c.toDart.dir.turnRight) :
    Relation.ReflTransGen ContactMove c c' := by
  refine reflTransGen_contactMove_of_same_outSite_rightFanPrefix c c' hout
    (rightFanPrefix_one c.toDart hL hS) ?_
  simpa using hdir

end IsingModel

import IsingModel.Peierls.SingleOrbitContactMove

/-!
# Local generators of contact-move connectivity (FV §3.7.2)

The elementary `ContactMove`s, packaged as `ReflTransGen ContactMove` facts — the local generators a
global planar-connectivity argument will chain. A left-fan rotation about a fixed in-site
(`reflTransGen_contactMove_of_same_inSite_leftFanPrefix`), a right-fan rotation about a fixed
out-site (`reflTransGen_contactMove_of_same_outSite_rightFanPrefix`), and the boundary slide
(`reflTransGen_contactMove_iterate`, exhibiting a whole forward orbit as one contact-move chain).
These hold unconditionally; assembling them into full connectivity for a connected filled region is
the remaining planar step (only there do `F`-connectivity and filledness enter, to cross between
exposed wedges).

* `reflTransGen_contactMove_of_same_inSite_leftFanPrefix` — left-fan generator.
* `reflTransGen_contactMove_of_same_outSite_rightFanPrefix` — right-fan generator.
* `reflTransGen_contactMove_nextDart` / `reflTransGen_contactMove_iterate` — the slide generators.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- **Left-fan generator**: a left-fan rotation about a fixed in-site is a one-edge contact-move
chain. -/
theorem reflTransGen_contactMove_of_same_inSite_leftFanPrefix (c c' : ContactPair F) {k : ℕ}
    (hin : c.inSite = c'.inSite) (hfan : c.toDart.LeftFanPrefix k)
    (hdir : c'.toDart.dir = (Dir2.turnLeft^[k]) c.toDart.dir) :
    Relation.ReflTransGen ContactMove c c' :=
  Relation.ReflTransGen.single (ContactMove.of_contactStep (ContactStep.of_leftFan hin hfan hdir))

/-- **Right-fan generator**: a right-fan rotation about a fixed out-site is a one-edge contact-move
chain. -/
theorem reflTransGen_contactMove_of_same_outSite_rightFanPrefix (c c' : ContactPair F) {k : ℕ}
    (hout : c.outSite = c'.outSite) (hfan : c.toDart.RightFanPrefix k)
    (hdir : c'.toDart.dir = (Dir2.turnRight^[k]) c.toDart.dir) :
    Relation.ReflTransGen ContactMove c c' :=
  Relation.ReflTransGen.single (ContactMove.of_contactStep (ContactStep.of_rightFan hout hfan hdir))

/-- **Slide generator**: one boundary step is a one-edge contact-move chain. -/
theorem reflTransGen_contactMove_nextDart (d : BoundaryDart F) :
    Relation.ReflTransGen ContactMove d.toContactPair d.nextDart.toContactPair :=
  Relation.ReflTransGen.single (ContactMove.of_nextDart d)

/-- **The forward orbit is one contact-move chain**: any forward iterate is reachable from `d` by a
chain of slide moves. -/
theorem reflTransGen_contactMove_iterate (d : BoundaryDart F) (n : ℕ) :
    Relation.ReflTransGen ContactMove d.toContactPair
      (BoundaryDart.nextDart^[n] d).toContactPair := by
  induction n with
  | zero => exact Relation.ReflTransGen.refl
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact ih.tail (ContactMove.of_nextDart (BoundaryDart.nextDart^[m] d))

end IsingModel

import IsingModel.Peierls.SingleOrbitContactStep

/-!
# Contact moves: fans plus the slide (FV §3.7.2)

The two fan contact steps do not suffice to connect the contact graph (a "domino" region has fan
moves only along its sides). The missing move is the **slide**: advancing one boundary step
(`nextDart`), which translates the contact pair. A **contact move** is therefore a contact step or a
single `nextDart` slide. Each move still sends the realizing darts into one orbit
(`sameOrbit_of_contactMove`), so any chain does (`sameOrbit_of_contactMove_chain`,
`sameOrbit_of_dart_contactMove_chain`). Crucially every `nextDart` step is itself a contact move
(`ContactMove.of_nextDart`), so following the boundary is a contact-move chain — the local
compatibility that, together with the planar connectivity of the contact graph, will give the
single-orbit property.

* `ContactMove` — a contact step or a `nextDart` slide.
* `ContactMove.of_contactStep` / `ContactMove.of_nextDart` — the two ways to take a move.
* `sameOrbit_of_contactMove` / `_chain` / `sameOrbit_of_dart_contactMove_chain` — the push-down.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- **A contact move**: a contact step (a fan rotation) or a single `nextDart` slide. -/
def ContactMove (c c' : ContactPair F) : Prop :=
  ContactStep c c' ∨ c' = c.toDart.nextDart.toContactPair

/-- **A contact step is a contact move**. -/
theorem ContactMove.of_contactStep {c c' : ContactPair F} (h : ContactStep c c') :
    ContactMove c c' := Or.inl h

/-- **Every `nextDart` step is a contact move** (the slide): following the boundary one step is a
contact move on the corresponding contact pairs. -/
theorem ContactMove.of_nextDart (d : BoundaryDart F) :
    ContactMove d.toContactPair d.nextDart.toContactPair := by
  right; rw [toContactPair_toDart]

/-- **A contact move sends the realizing darts into one orbit**. -/
theorem sameOrbit_of_contactMove (c c' : ContactPair F) (h : ContactMove c c') :
    c.toDart.SameOrbit c'.toDart := by
  rcases h with hstep | hnext
  · exact sameOrbit_of_contactStep c c' hstep
  · subst hnext
    rw [toContactPair_toDart]
    exact c.toDart.sameOrbit_nextDart

/-- **A chain of contact moves sends the realizing darts into one orbit**. -/
theorem sameOrbit_of_contactMove_chain (c c' : ContactPair F)
    (h : Relation.ReflTransGen ContactMove c c') : c.toDart.SameOrbit c'.toDart := by
  induction h with
  | refl => exact BoundaryDart.SameOrbit.refl _
  | tail _ hstep ih => exact ih.trans (sameOrbit_of_contactMove _ _ hstep)

/-- **The dart-level push-down**: if the contact pairs of two darts are joined by a chain of contact
moves, the darts are in one orbit. -/
theorem sameOrbit_of_dart_contactMove_chain (d e : BoundaryDart F)
    (h : Relation.ReflTransGen ContactMove d.toContactPair e.toContactPair) : d.SameOrbit e := by
  have hso := sameOrbit_of_contactMove_chain d.toContactPair e.toContactPair h
  rwa [toContactPair_toDart, toContactPair_toDart] at hso

end IsingModel

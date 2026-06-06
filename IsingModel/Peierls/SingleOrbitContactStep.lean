import IsingModel.Peierls.SingleOrbitContactPair
import IsingModel.Peierls.SingleOrbitFanComplete
import IsingModel.Peierls.SingleOrbitRightFanPrefix

/-!
# Contact steps and the orbit push-down (FV §3.7.2)

A **contact step** is a proof-carrying edge between contact pairs, independent of the orbit
dynamics: either the in-site is fixed and the realizing darts are related by a **left-fan** prefix
(a rotation about the shared `F`-side site), or the out-site is fixed and they are related by a
**right-fan** prefix (a rotation about the shared complement-side site). By the fan completeness
lemmas each step sends the two realizing darts into one orbit (`sameOrbit_of_contactStep`), and
therefore so does any finite chain of contact steps (`sameOrbit_of_contactStep_chain`). This is the
bridge that will push the (orbit-free) planar connectivity of contact pairs down to the single-orbit
property: once `ReflTransGen ContactStep` holds for a connected filled region, all boundary darts
share one orbit.

* `ContactStep` — a proof-carrying contact-graph edge.
* `sameOrbit_of_contactStep` — a step sends the realizing darts into one orbit.
* `sameOrbit_of_contactStep_chain` — and so does any `ReflTransGen` chain.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- **A contact step**: a proof-carrying edge between contact pairs. Either the in-site is fixed and
the realizing darts are related by a left-fan prefix, or the out-site is fixed and they are related
by a right-fan prefix. -/
def ContactStep (c c' : ContactPair F) : Prop :=
  (c.inSite = c'.inSite ∧ ∃ k, c.toDart.LeftFanPrefix k ∧
      c'.toDart.dir = (Dir2.turnLeft^[k]) c.toDart.dir) ∨
    (c.outSite = c'.outSite ∧ ∃ k, c.toDart.RightFanPrefix k ∧
      c'.toDart.dir = (Dir2.turnRight^[k]) c.toDart.dir)

/-- **Left-fan contact step constructor**. -/
theorem ContactStep.of_leftFan {c c' : ContactPair F} (hin : c.inSite = c'.inSite) {k : ℕ}
    (hfan : c.toDart.LeftFanPrefix k)
    (hdir : c'.toDart.dir = (Dir2.turnLeft^[k]) c.toDart.dir) : ContactStep c c' :=
  Or.inl ⟨hin, k, hfan, hdir⟩

/-- **Right-fan contact step constructor**. -/
theorem ContactStep.of_rightFan {c c' : ContactPair F} (hout : c.outSite = c'.outSite) {k : ℕ}
    (hfan : c.toDart.RightFanPrefix k)
    (hdir : c'.toDart.dir = (Dir2.turnRight^[k]) c.toDart.dir) : ContactStep c c' :=
  Or.inr ⟨hout, k, hfan, hdir⟩

/-- **A contact step sends the realizing darts into one orbit** (by fan completeness). -/
theorem sameOrbit_of_contactStep (c c' : ContactPair F) (h : ContactStep c c') :
    c.toDart.SameOrbit c'.toDart := by
  rcases h with ⟨hin, k, hfan, hdir⟩ | ⟨hout, k, hfan, hdir⟩
  · refine sameOrbit_of_leftFanPrefix_dir_eq c.toDart c'.toDart hfan ?_ hdir
    rw [ContactPair.toDart_left, ContactPair.toDart_left]; exact hin.symm
  · refine sameOrbit_of_rightFanPrefix_dir_eq c.toDart c'.toDart hfan ?_ hdir
    rw [ContactPair.toDart_right, ContactPair.toDart_right]; exact hout.symm

/-- **A chain of contact steps sends the realizing darts into one orbit**. -/
theorem sameOrbit_of_contactStep_chain (c c' : ContactPair F)
    (h : Relation.ReflTransGen ContactStep c c') : c.toDart.SameOrbit c'.toDart := by
  induction h with
  | refl => exact BoundaryDart.SameOrbit.refl _
  | tail _ hstep ih => exact ih.trans (sameOrbit_of_contactStep _ _ hstep)

/-- **The dart-level push-down**: if the contact pairs of two darts are joined by a chain of contact
steps, the darts are in one orbit (via the dart ↔ contact-pair round trip). -/
theorem sameOrbit_of_dart_contactStep_chain (d e : BoundaryDart F)
    (h : Relation.ReflTransGen ContactStep d.toContactPair e.toContactPair) : d.SameOrbit e := by
  have hso := sameOrbit_of_contactStep_chain d.toContactPair e.toContactPair h
  rwa [toContactPair_toDart, toContactPair_toDart] at hso

end IsingModel

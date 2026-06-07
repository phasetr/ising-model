import IsingModel.Peierls.SingleOrbitContactGen

/-!
# Contact-move connectivity equals same-orbit (FV §3.7.2)

The dart-level contact-move connectivity is *exactly* the orbit relation. One direction is the
push-down (`sameOrbit_of_dart_contactMove_chain`); the converse
(`reflTransGen_contactMove_of_sameOrbit`) is the forward-orbit chain
(`reflTransGen_contactMove_iterate`). Hence `ReflTransGen ContactMove` on the contact pairs of two
darts is equivalent to those darts being in the same orbit
(`reflTransGen_contactMove_iff_sameOrbit`). So proving that all contact pairs of a connected filled
region are contact-move connected is *the same problem* as the single-orbit property — the planar
connectivity is the whole remaining content, with no further orbit bookkeeping needed.

* `reflTransGen_contactMove_of_sameOrbit` — same orbit gives a contact-move chain.
* `reflTransGen_contactMove_iff_sameOrbit` — the equivalence.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- **Same orbit gives a contact-move chain**: if `d.SameOrbit e`, their contact pairs are joined by
a chain of contact moves (the forward-orbit slide chain). -/
theorem reflTransGen_contactMove_of_sameOrbit (d e : BoundaryDart F) (h : d.SameOrbit e) :
    Relation.ReflTransGen ContactMove d.toContactPair e.toContactPair := by
  obtain ⟨n, hn⟩ := h
  rw [← hn]
  exact reflTransGen_contactMove_iterate d n

/-- **Contact-move connectivity equals same-orbit**: `ReflTransGen ContactMove` on the contact pairs
of two darts is equivalent to those darts being in the same orbit. -/
theorem reflTransGen_contactMove_iff_sameOrbit (d e : BoundaryDart F) :
    Relation.ReflTransGen ContactMove d.toContactPair e.toContactPair ↔ d.SameOrbit e :=
  ⟨sameOrbit_of_dart_contactMove_chain d e, reflTransGen_contactMove_of_sameOrbit d e⟩

end IsingModel

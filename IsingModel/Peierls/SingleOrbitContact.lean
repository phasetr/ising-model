import IsingModel.Peierls.SingleOrbitBase
import IsingModel.Peierls.DartOfCut
import IsingModel.Peierls.GridEdge2

/-!
# Boundary darts and contact pairs (FV §3.7.2)

A **contact pair** of a region `F` is an ordered adjacent pair `(a, b)` with `a ∈ F` and `b ∉ F`.
Every boundary dart presents such a pair via `(d.left, d.right)` (forward direction,
`BoundaryDart.adj_left_right`), and conversely every contact pair is realised by a boundary dart
(`exists_boundaryDart_of_contact`, strengthening `exists_dart_of_cut`). Together with the
faithfulness of `SingleOrbitBase`, the boundary darts of `F` correspond exactly to its contact
pairs. The planned boundary-slide argument moves along contact pairs, so this correspondence is
the bridge between the geometry (adjacent in/out sites) and the orbit dynamics; the trivial
orbit-step wrappers `sameOrbit_nextDart` / `sameOrbit_iterate` record that a dart is always in the
same orbit as its forward iterates.

* `BoundaryDart.sameOrbit_nextDart` / `sameOrbit_iterate` — forward orbit-step wrappers.
* `BoundaryDart.adj_left_right` — a dart's two sites are adjacent (it is a contact pair).
* `exists_boundaryDart_of_contact` — every contact pair is realised by a boundary dart.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- **A dart is in the same orbit as its successor**: `d.SameOrbit d.nextDart` (`n = 1`). -/
theorem BoundaryDart.sameOrbit_nextDart (d : BoundaryDart F) : d.SameOrbit d.nextDart :=
  ⟨1, by rw [Function.iterate_one]⟩

/-- **A dart is in the same orbit as any forward iterate**: `d.SameOrbit (nextDart^[n] d)`. -/
theorem BoundaryDart.sameOrbit_iterate (d : BoundaryDart F) (n : ℕ) :
    d.SameOrbit (BoundaryDart.nextDart^[n] d) :=
  ⟨n, rfl⟩

/-- **A boundary dart is a contact pair**: its left and right sites are adjacent in the lattice. -/
theorem BoundaryDart.adj_left_right (d : BoundaryDart F) :
    (latticeGraph 2).Adj d.left d.right := by
  change (latticeGraph 2).Adj (leftSite d.tail d.dir) (rightSite d.tail d.dir)
  obtain ⟨k, hk | hk⟩ := leftSite_rightSite_adjacent d.tail d.dir
  · rw [hk]; exact (GridEdge2.latticeGraph_adj_add_unitVec2 _ k).symm
  · rw [hk]; exact GridEdge2.latticeGraph_adj_add_unitVec2 _ k

/-- **Every contact pair is realised by a boundary dart**: if `a ∈ F`, `b ∉ F` and `a, b` are
adjacent, some boundary dart `d` has `d.left = a` and `d.right = b`. This strengthens
`exists_dart_of_cut` (which gives only the unordered cut edge): membership orients the pair. -/
theorem exists_boundaryDart_of_contact {a b : Fin 2 → ℤ}
    (ha : a ∈ F) (hb : b ∉ F) (hadj : (latticeGraph 2).Adj a b) :
    ∃ d : BoundaryDart F, d.left = a ∧ d.right = b := by
  obtain ⟨d, hd⟩ := exists_dart_of_cut hadj ha hb
  have hsym : s(d.left, d.right) = s(a, b) := hd
  rw [Sym2.eq_iff] at hsym
  rcases hsym with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨d, h1, h2⟩
  · exfalso
    apply hb
    have hmem : d.left ∈ F := d.left_mem
    rwa [h1] at hmem

end IsingModel

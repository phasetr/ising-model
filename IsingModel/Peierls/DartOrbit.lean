import IsingModel.Peierls.DartBijective

/-!
# The dart orbit is a cycle in the dual lattice (FV §3.7.2)

Each step of the boundary traversal moves the dart along a unit edge of the dual lattice
(`d.tail` to `d.head = d.tail + d.dir.vec`), and `nextDart` advances the head to the next tail.
Since `nextDart` is a bijection of the finite dart type, every dart is periodic: iterating
`nextDart` returns to the start. The orbit is thus a closed walk in `latticeGraph 2`, which the
existing degree-based walk count bounds — the route to the volume-independent contour count.

* `latticeGraph_adj_dirVec` — a step along any direction is a lattice adjacency.
* `BoundaryDart.tail_adj_head` — the dart's tail and head are adjacent.
* `nextDart_periodic` — every dart returns to itself under iterated `nextDart`.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- **A step along any direction is a lattice adjacency**: `t` and `t + δ.vec` are adjacent in
`latticeGraph 2` (the direction vector is a unit vector, up to sign). -/
theorem latticeGraph_adj_dirVec (t : Fin 2 → ℤ) (δ : Dir2) :
    (latticeGraph 2).Adj t (t + δ.vec) := by
  change (∑ i : Fin 2, |t i - (t + δ.vec) i|) = 1
  rw [Fin.sum_univ_two]
  fin_cases δ <;>
    simp [Dir2.vec, unitVec2, Pi.add_apply, Pi.neg_apply]

/-- **The dart's tail and head are adjacent** in the dual lattice. -/
theorem BoundaryDart.tail_adj_head (d : BoundaryDart F) :
    (latticeGraph 2).Adj d.tail d.head :=
  latticeGraph_adj_dirVec d.tail d.dir

/-- **Every dart is periodic under `nextDart`**: since `nextDart` is a bijection of the finite
dart type, iterating it from any dart eventually returns to that dart. The orbit is a cycle. -/
theorem nextDart_periodic (d : BoundaryDart F) :
    ∃ n, 0 < n ∧ (BoundaryDart.nextDart^[n]) d = d := by
  haveI : Finite (BoundaryDart F) := Finite.of_fintype _
  obtain ⟨m, n, hmn, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun k : ℕ => (BoundaryDart.nextDart^[k]) d)
  rcases lt_or_gt_of_ne hmn with hlt | hlt
  · refine ⟨n - m, by omega, ?_⟩
    apply nextDart_bijective.injective.iterate m
    rw [← Function.iterate_add_apply, show m + (n - m) = n by omega]
    exact heq.symm
  · refine ⟨m - n, by omega, ?_⟩
    apply nextDart_bijective.injective.iterate n
    rw [← Function.iterate_add_apply, show n + (m - n) = m by omega]
    exact heq

end IsingModel

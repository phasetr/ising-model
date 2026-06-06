import IsingModel.Peierls.DartOrbit

/-!
# The dart orbit as an explicit closed walk (FV §3.7.2)

The sequence of dart tails `d.tail, (nextDart d).tail, (nextDart² d).tail, …` is a walk in the
dual lattice `latticeGraph 2`: consecutive tails are adjacent because `(nextDart d).tail = d.head`
and `d.tail` is adjacent to `d.head`. This file realises that sequence as an honest
`SimpleGraph.Walk`, of length equal to the number of steps, and — at the orbit period — a closed
walk from `d.tail` to itself. Bounding the number of such closed walks (by the degree count) is
the final combinatorial input to the contour count.

* `orbitWalk` — the walk along the first `n` darts of the orbit.
* `orbitWalk_length` — its length is `n`.
* `orbitClosedWalk` — the closed walk over a full period.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset SimpleGraph

variable {F : Finset (Fin 2 → ℤ)}

/-- **The orbit walk**: the walk in `latticeGraph 2` along the tails of the first `n` darts of the
forward orbit of `d`, from `d.tail` to `(nextDart^[n] d).tail`. -/
noncomputable def orbitWalk (d : BoundaryDart F) :
    (n : ℕ) → (latticeGraph 2).Walk d.tail (BoundaryDart.nextDart^[n] d).tail
  | 0 => SimpleGraph.Walk.nil
  | n + 1 =>
    ((orbitWalk d n).concat (BoundaryDart.tail_adj_head (BoundaryDart.nextDart^[n] d))).copy rfl
      (by rw [Function.iterate_succ_apply', BoundaryDart.nextDart_tail])

/-- **The orbit walk has length `n`**. -/
theorem orbitWalk_length (d : BoundaryDart F) (n : ℕ) : (orbitWalk d n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [orbitWalk, SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_concat, ih]

/-- **The orbit closed walk**: over a full period `n` (where `nextDart^[n] d = d`), the orbit walk
is a closed walk from `d.tail` back to `d.tail`. -/
noncomputable def orbitClosedWalk (d : BoundaryDart F) {n : ℕ}
    (hn : (BoundaryDart.nextDart^[n] d) = d) : (latticeGraph 2).Walk d.tail d.tail :=
  (orbitWalk d n).copy rfl (by rw [hn])

/-- **The orbit closed walk has length `n`**. -/
theorem orbitClosedWalk_length (d : BoundaryDart F) {n : ℕ}
    (hn : (BoundaryDart.nextDart^[n] d) = d) : (orbitClosedWalk d hn).length = n := by
  rw [orbitClosedWalk, SimpleGraph.Walk.length_copy, orbitWalk_length]

end IsingModel

import Mathlib.Combinatorics.SimpleGraph.Walks.Counting
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity

/-!
# Walk-weight and fixed-length walk-sum framework (FFS Ch 12 / GJ §18)

For the random-walk representation of the Ising two-point function we sum a
**geometric weight** `z^{length}` (later `z = β J`) over the graph walks between
two vertices.  Define

  `walkWeight z w = z ^ w.length`,
  `walkSum G z i j n = ∑_{w : length-n walk i → j} z^{w.length}`.

Since every length-`n` walk has weight `z^n`, the sum is `z^n` times the number
of length-`n` walks, i.e. `z^n · (A^n)_{ij}` with `A` the adjacency matrix.  The
key structural fact is the **neighbour recurrence**

  `walkSum z i j (n+1) = z · ∑_{u ∼ i} walkSum z u j n`,

which mirrors the one-step Simon-Lieb transfer kernel
(`correlation_inducedGraph_simon_lieb_neighbor`): iterating the kernel against
this recurrence (later PR) yields the random-walk bound
`⟨σ_i σ_j⟩ ≤ ∑_{walks i → j} (β J)^{length}`.

## References

* Fernández–Fröhlich–Sokal, *Random Walks, Critical Phenomena, and Triviality*
  (1992), Ch 12.
* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.
-/

namespace IsingModel

namespace Ambient

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The **geometric weight** of a graph walk: `z` raised to the walk's length. -/
noncomputable def walkWeight (z : ℝ) {i j : V} (w : G.Walk i j) : ℝ := z ^ w.length

/-- The **walk sum**: the total weight `∑ z^{length}` over all length-`n` walks
from `i` to `j` (with `z = β J` in the Ising application). -/
noncomputable def walkSum (z : ℝ) (i j : V) (n : ℕ) : ℝ :=
  ∑ w ∈ G.finsetWalkLength n i j, walkWeight G z w

/-- **`walkSum` as a power times a walk count**: every length-`n` walk has weight
`z^n`, so `walkSum z i j n = z^n · #{length-n walks i → j}`. -/
theorem walkSum_eq_pow_mul_card (z : ℝ) (i j : V) (n : ℕ) :
    walkSum G z i j n = z ^ n * (G.finsetWalkLength n i j).card := by
  rw [walkSum]
  have hconst : ∀ w ∈ G.finsetWalkLength n i j, walkWeight G z w = z ^ n := by
    intro w hw
    have hl : w.length = n := mem_finsetWalkLength_iff.mp hw
    simp only [walkWeight, hl]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- **`walkSum` via the adjacency-matrix power**:
`walkSum z i j n = z^n · (A^n)_{ij}`, since `(A^n)_{ij}` counts length-`n` walks
from `i` to `j`. -/
theorem walkSum_eq_pow_mul_adjMatrix_pow (z : ℝ) (i j : V) (n : ℕ) :
    walkSum G z i j n = z ^ n * (G.adjMatrix ℝ ^ n) i j := by
  rw [walkSum_eq_pow_mul_card, adjMatrix_pow_apply_eq_card_walk, ← card_set_walk_length_eq]

/-- The walk sum is nonnegative for `z ≥ 0`. -/
theorem walkSum_nonneg {z : ℝ} (hz : 0 ≤ z) (i j : V) (n : ℕ) :
    0 ≤ walkSum G z i j n := by
  rw [walkSum_eq_pow_mul_card]
  positivity

/-- The length-`0` walk sum is `1` on the diagonal, `0` off it (the only
length-`0` walk is `nil`, which exists iff `i = j`). -/
theorem walkSum_zero (z : ℝ) (i j : V) :
    walkSum G z i j 0 = if i = j then 1 else 0 := by
  rw [walkSum_eq_pow_mul_adjMatrix_pow, pow_zero, pow_zero, one_mul, Matrix.one_apply]

/-- **Neighbour recurrence for the walk sum** (FFS Ch 12 / GJ §18): a length-`(n+1)`
walk from `i` first steps to a neighbour `u ∼ i`, then is a length-`n` walk from
`u`, so

`walkSum z i j (n+1) = z · ∑_{u ∈ neighborFinset i} walkSum z u j n`.

This is the walk-side companion of the one-step Simon-Lieb transfer kernel; the
adjacency-matrix identity `(A · A^n)_{ij} = ∑_{u ∼ i} (A^n)_{uj}`
(`adjMatrix_mul_apply`) supplies the step. -/
theorem walkSum_succ (z : ℝ) (i j : V) (n : ℕ) :
    walkSum G z i j (n + 1) = z * ∑ u ∈ G.neighborFinset i, walkSum G z u j n := by
  conv_rhs => rw [Finset.mul_sum]
  rw [walkSum_eq_pow_mul_adjMatrix_pow, pow_succ' (G.adjMatrix ℝ) n, adjMatrix_mul_apply,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [walkSum_eq_pow_mul_adjMatrix_pow]
  ring

end Ambient

end IsingModel

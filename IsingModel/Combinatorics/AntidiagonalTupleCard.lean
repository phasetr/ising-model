import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Cardinality bound for `Finset.Nat.antidiagonalTuple`

This file records a self-contained arithmetic bound on the number of `k`-tuples of natural
numbers that sum to a fixed value `ℓ`.  An element of `Finset.Nat.antidiagonalTuple k ℓ` is a
tuple `t : Fin k → ℕ` with `∑ i, t i = ℓ`; each coordinate therefore satisfies `t i ≤ ℓ`, so the
whole tuple lives in the product of `Finset.range (ℓ + 1)` over the `k` coordinates.  Counting
that product gives the bound

`(Finset.Nat.antidiagonalTuple k ℓ).card ≤ (ℓ + 1) ^ k`.

This is the composition-count ("stars and bars") factor used in the Glimm–Jaffe §17.6.1 field
cluster-expansion source-configuration fiber count (F5a-2a).  It is purely arithmetic and depends
only on mathlib, so it is kept in its own reusable file.

## References

This elementary tuple-count identity is a project arithmetic lemma; no external
source is claimed.
-/

namespace IsingModel

open scoped BigOperators

/-- The number of `k`-tuples of natural numbers summing to `ℓ` is at most `(ℓ + 1) ^ k`.

Every tuple `t ∈ Finset.Nat.antidiagonalTuple k ℓ` has `∑ i, t i = ℓ`, hence each coordinate
`t i ≤ ℓ`, i.e. `t i ∈ Finset.range (ℓ + 1)`.  Thus the antidiagonal tuple set is a subset of the
product `Fintype.piFinset (fun _ : Fin k => Finset.range (ℓ + 1))`, whose cardinality is
`(ℓ + 1) ^ k`. -/
theorem antidiagonalTuple_card_le (k ℓ : ℕ) :
    (Finset.Nat.antidiagonalTuple k ℓ).card ≤ (ℓ + 1) ^ k := by
  calc
    (Finset.Nat.antidiagonalTuple k ℓ).card
        ≤ (Fintype.piFinset (fun _ : Fin k => Finset.range (ℓ + 1))).card := by
          apply Finset.card_le_card
          intro t ht
          rw [Finset.Nat.mem_antidiagonalTuple] at ht
          rw [Fintype.mem_piFinset]
          intro i
          rw [Finset.mem_range]
          have hle : t i ≤ ∑ j, t j :=
            Finset.single_le_sum (fun j _ => Nat.zero_le (t j)) (Finset.mem_univ i)
          omega
    _ = (ℓ + 1) ^ k := by
          rw [Fintype.card_piFinset_const, Finset.card_range]

end IsingModel

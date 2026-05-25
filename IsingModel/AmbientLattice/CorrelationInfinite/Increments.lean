import IsingModel.AmbientLattice.CorrelationInfinite.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Increments of the correlation along an exhaustion

For a ferromagnetic Ising model the finite-volume correlation
`correlationAlongExhaustion G Λ p A` is monotone increasing in the exhaustion
stage (GKS) and bounded above by `1`, hence convergent to
`correlationInfinite G Λ p A`.  This file records the basic structure of the
consecutive-stage increments
`correlationAlongExhaustion G Λ p A (n + 1) - correlationAlongExhaustion G Λ p A n`:
they are nonnegative and (pointwise in the model data) summable, with total
mass `correlationInfinite - correlationAlongExhaustion G Λ p A 0`.

This is the baseline increment-structure layer for the finite-volume
convergence-rate program (Issue #2931): for correlations the increment series
is automatically summable by monotone convergence, which frames the remaining
task of obtaining a quantitative summable bound on the *β-derivative* increments
used by the GJ §17.5 Lemma 17.5.2 derivative-limit provider.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof and
  Lemma 17.5.2, pp.~311--312.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Nonnegativity of the correlation increment along an exhaustion**: for a
ferromagnetic model the consecutive-stage difference
`correlationAlongExhaustion G Λ p A (n + 1) - correlationAlongExhaustion G Λ p A n`
is nonnegative, since `correlationAlongExhaustion` is monotone in the stage
index by GKS. -/
theorem correlationAlongExhaustion_increment_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset V) (n : ℕ) :
    0 ≤ correlationAlongExhaustion G Λ p A (n + 1) -
        correlationAlongExhaustion G Λ p A n := by
  have hmono :=
    correlationAlongExhaustion_monotone G Λ p hf A (Nat.le_succ n)
  linarith

/-- **Summability of the correlation increments along an exhaustion**: for a
ferromagnetic model the consecutive-stage increment series
`fun n => correlationAlongExhaustion G Λ p A (n + 1) - correlationAlongExhaustion G Λ p A n`
is summable.  The increments are nonnegative (GKS monotonicity) and their
partial sums telescope to
`correlationAlongExhaustion G Λ p A n - correlationAlongExhaustion G Λ p A 0`,
which is bounded above by
`correlationInfinite G Λ p A - correlationAlongExhaustion G Λ p A 0`; summability
of a nonnegative series with bounded partial sums then follows.

For correlations this summability is automatic from monotone convergence; the
analogous statement for the β-derivative increments is the substantive
convergence-rate input tracked by Issue #2931. -/
theorem correlationAlongExhaustion_increment_summable
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset V) :
    Summable (fun n =>
      correlationAlongExhaustion G Λ p A (n + 1) -
        correlationAlongExhaustion G Λ p A n) := by
  refine summable_of_sum_range_le
    (c := correlationInfinite G Λ p A - correlationAlongExhaustion G Λ p A 0)
    (fun n => correlationAlongExhaustion_increment_nonneg G Λ p hf A n) (fun n => ?_)
  rw [Finset.sum_range_sub (correlationAlongExhaustion G Λ p A) n]
  have hle := correlationAlongExhaustion_le_correlationInfinite G Λ p A n
  linarith

end Ambient
end IsingModel

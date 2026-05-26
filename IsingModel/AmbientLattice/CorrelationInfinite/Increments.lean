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
they are nonnegative and (pointwise in the model data) summable, their partial
sums telescoping to `correlationAlongExhaustion G Λ p A n - correlationAlongExhaustion G Λ p A 0`,
bounded above by `correlationInfinite - correlationAlongExhaustion G Λ p A 0`.

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

/-! ## Convergence tail structure

The convergence-rate program (Issue #2931) studies how fast
`correlationAlongExhaustion G Λ p A n` approaches its infinite-volume limit
`correlationInfinite G Λ p A`.  The tail `correlationInfinite - correlationAlongExhaustion … n`
is the nonnegative, antitone quantity tending to `0` whose decay rate is the
substantive remaining input.  These lemmas record its structure (the rate
itself is not yet quantified). -/

/-- **Nonnegativity of the convergence tail**: the gap between the
infinite-volume correlation and the stage-`n` finite-volume correlation is
nonnegative, by the pointwise upper bound. -/
theorem correlationInfinite_sub_correlationAlongExhaustion_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (A : Finset V) (n : ℕ) :
    0 ≤ correlationInfinite G Λ p A - correlationAlongExhaustion G Λ p A n := by
  have hle := correlationAlongExhaustion_le_correlationInfinite G Λ p A n
  linarith

/-- **Antitonicity of the convergence tail**: for a ferromagnetic model the tail
`n ↦ correlationInfinite - correlationAlongExhaustion … n` is antitone (it only
decreases as the volume grows), since `correlationAlongExhaustion` is monotone in
the stage index by GKS. -/
theorem correlationInfinite_sub_correlationAlongExhaustion_antitone
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset V) :
    Antitone (fun n =>
      correlationInfinite G Λ p A - correlationAlongExhaustion G Λ p A n) := by
  intro m n hmn
  have hmono := correlationAlongExhaustion_monotone G Λ p hf A hmn
  dsimp only
  linarith

/-- **The convergence tail tends to zero**: for a ferromagnetic model the gap
`correlationInfinite - correlationAlongExhaustion … n` tends to `0` as `n → ∞`,
since `correlationAlongExhaustion` converges to `correlationInfinite`.  Its rate
of decay is the substantive remaining convergence-rate input (Issue #2931). -/
theorem tendsto_correlationInfinite_sub_correlationAlongExhaustion_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset V) :
    Filter.Tendsto
      (fun n => correlationInfinite G Λ p A - correlationAlongExhaustion G Λ p A n)
      Filter.atTop (nhds 0) := by
  have htend := tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf A
  have := (tendsto_const_nhds (x := correlationInfinite G Λ p A)
    (f := Filter.atTop (α := ℕ))).sub htend
  simpa using this

/-- **Total mass of the correlation increment series**: for a ferromagnetic
model the consecutive-stage increments sum (telescopically) to the full gap
between the infinite-volume correlation and the initial stage:
`∑' n, (correlationAlongExhaustion … (n+1) - correlationAlongExhaustion … n)
   = correlationInfinite … - correlationAlongExhaustion … 0`.

The partial sums telescope to `correlationAlongExhaustion … n - correlationAlongExhaustion … 0`
and converge to `correlationInfinite … - correlationAlongExhaustion … 0`; since
the increment series is summable, uniqueness of limits identifies the `tsum`. -/
theorem correlationAlongExhaustion_increment_tsum_eq
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset V) :
    ∑' n, (correlationAlongExhaustion G Λ p A (n + 1) -
        correlationAlongExhaustion G Λ p A n)
      = correlationInfinite G Λ p A - correlationAlongExhaustion G Λ p A 0 := by
  have hsum := correlationAlongExhaustion_increment_summable G Λ p hf A
  have h1 :
      Filter.Tendsto
        (fun n => ∑ k ∈ Finset.range n,
          (correlationAlongExhaustion G Λ p A (k + 1) -
            correlationAlongExhaustion G Λ p A k))
        Filter.atTop
        (nhds (∑' n, (correlationAlongExhaustion G Λ p A (n + 1) -
          correlationAlongExhaustion G Λ p A n))) :=
    hsum.hasSum.tendsto_sum_nat
  have h2 :
      Filter.Tendsto
        (fun n => ∑ k ∈ Finset.range n,
          (correlationAlongExhaustion G Λ p A (k + 1) -
            correlationAlongExhaustion G Λ p A k))
        Filter.atTop
        (nhds (correlationInfinite G Λ p A - correlationAlongExhaustion G Λ p A 0)) := by
    have hfun :
        (fun n => ∑ k ∈ Finset.range n,
          (correlationAlongExhaustion G Λ p A (k + 1) -
            correlationAlongExhaustion G Λ p A k))
          = fun n => correlationAlongExhaustion G Λ p A n -
              correlationAlongExhaustion G Λ p A 0 := by
      funext n
      exact Finset.sum_range_sub (correlationAlongExhaustion G Λ p A) n
    rw [hfun]
    exact (tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf A).sub_const
      (correlationAlongExhaustion G Λ p A 0)
  exact tendsto_nhds_unique h1 h2

/-- **Stage-`n` convergence tail as the increment tail-sum**: for a ferromagnetic
model the gap between the infinite-volume correlation and the stage-`n`
finite-volume correlation equals the sum of all consecutive-stage increments from
stage `n` onward:
`correlationInfinite … - correlationAlongExhaustion … n
   = ∑' k, (correlationAlongExhaustion … (k+n+1) - correlationAlongExhaustion … (k+n))`.

This expresses the convergence tail directly as the increment tail series: a
quantitative (summable/geometric) bound on the increments from stage `n` would
control this tail's decay rate (Issue #2931).  It follows from
`Summable.sum_add_tsum_nat_add` and the total-mass identity. -/
theorem correlationAlongExhaustion_tail_eq_tsum_increment_shift
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset V) (n : ℕ) :
    correlationInfinite G Λ p A - correlationAlongExhaustion G Λ p A n
      = ∑' k, (correlationAlongExhaustion G Λ p A (k + n + 1) -
          correlationAlongExhaustion G Λ p A (k + n)) := by
  have hsum := correlationAlongExhaustion_increment_summable G Λ p hf A
  have hsplit := hsum.sum_add_tsum_nat_add n
  have hrange :
      ∑ i ∈ Finset.range n,
          (correlationAlongExhaustion G Λ p A (i + 1) -
            correlationAlongExhaustion G Λ p A i)
        = correlationAlongExhaustion G Λ p A n - correlationAlongExhaustion G Λ p A 0 :=
    Finset.sum_range_sub (correlationAlongExhaustion G Λ p A) n
  have htotal :
      ∑' i, (correlationAlongExhaustion G Λ p A (i + 1) -
          correlationAlongExhaustion G Λ p A i)
        = correlationInfinite G Λ p A - correlationAlongExhaustion G Λ p A 0 :=
    correlationAlongExhaustion_increment_tsum_eq G Λ p hf A
  rw [hrange, htotal] at hsplit
  linarith [hsplit]

/-- **Volume-convergence tail bounded by an increment-bound tail**: if the
consecutive-stage correlation increments are dominated by a summable sequence
`g`, then the stage-`n` convergence tail `correlationInfinite − correlationAlongExhaustion … n`
is bounded by the corresponding shifted tail `∑' k, g (k + n)`.

Combining the tail identity `correlationAlongExhaustion_tail_eq_tsum_increment_shift`
with `tsum_le_tsum` turns a per-stage increment bound (e.g. a geometric
convergence rate) into a quantitative bound on the finite-volume → infinite-volume
convergence rate.  Part of Issue #2965 (Phase A→C bridge). -/
theorem correlationInfinite_sub_correlationAlongExhaustion_le_tsum_shift_of_increment_le
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset V)
    {g : ℕ → ℝ} (hg : Summable g)
    (hincr : ∀ k, correlationAlongExhaustion G Λ p A (k + 1) -
        correlationAlongExhaustion G Λ p A k ≤ g k)
    (n : ℕ) :
    correlationInfinite G Λ p A - correlationAlongExhaustion G Λ p A n
      ≤ ∑' k, g (k + n) := by
  rw [correlationAlongExhaustion_tail_eq_tsum_increment_shift G Λ p hf A n]
  exact ((summable_nat_add_iff n).2
      (correlationAlongExhaustion_increment_summable G Λ p hf A)).tsum_le_tsum
    (fun k => hincr (k + n)) ((summable_nat_add_iff n).2 hg)

end Ambient
end IsingModel

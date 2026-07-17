import IsingModel.AmbientLattice.MagnetizationAlongExhaustion
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete along-exhaustion correlation limit wrappers

Narrow child module for concrete `latticeGraph` along-exhaustion correlation
monotonicity, boundedness, eventuality, and infinite-volume limit wrappers. The
theorem names are the same as the former declarations, but callers can
now avoid importing the monolithic concrete module.
-/

namespace IsingModel
namespace Ambient

/-! ### ℤ^d along-exhaustion correlation limit wrappers -/

/-! ## Moved: cubicExhaustion correlationAlongExhaustion monotonicity wrappers

The three wrappers
`correlationAlongExhaustion_latticeGraph_cubicExhaustion_monotone_{h,beta,J}`
now live in `CorrelationExhaustionLimitsCubicMonotone.lean`. -/


/-! ## Moved: correlationAlongExhaustion bound + eventually wrappers

The six wrappers
`correlationAlongExhaustion_latticeGraph_cubicExhaustion_{bddAbove,le_one,nonneg}`,
`abs_correlationAlongExhaustion_latticeGraph_eventually_le_one`,
`correlationAlongExhaustion_latticeGraph_eventually`, and
`abs_correlationAlongExhaustion_latticeGraph_eventually_le_one_general`
now live in `CorrelationExhaustionLimitsBounds.lean`. -/

/-- **ℤ^d shifted correlationΛ sequence is monotone and bounded by 1**
(any-Exhaustion, ferromagnetic). -/
theorem correlationΛ_shifted_monotone_bounded_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {A : Finset (Fin d → ℤ)} {N : ℕ}
    (hN : ∀ n ≥ N, A ⊆ Λ.volume n) :
    Monotone (fun n : ℕ =>
      correlationΛ (IsingModel.latticeGraph d) (Λ.volume (n + N)) p
        (Ambient.liftFinset A (hN (n + N) (Nat.le_add_left N n))))
    ∧ ∀ n : ℕ,
      correlationΛ (IsingModel.latticeGraph d) (Λ.volume (n + N)) p
        (Ambient.liftFinset A (hN (n + N) (Nat.le_add_left N n))) ≤ 1 :=
  correlationΛ_shifted_monotone_bounded (IsingModel.latticeGraph d) Λ p hf hN

/-- **ℤ^d shifted correlationΛ sequence converges** (any-Exhaustion, ferromagnetic). -/
theorem correlationΛ_shifted_tendsto_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {A : Finset (Fin d → ℤ)} {N : ℕ}
    (hN : ∀ n ≥ N, A ⊆ Λ.volume n) :
    ∃ L : ℝ, Filter.Tendsto
      (fun m : ℕ => correlationΛ (IsingModel.latticeGraph d)
        (Λ.volume (m + N)) p
        (Ambient.liftFinset A (hN (m + N) (Nat.le_add_left N m))))
      Filter.atTop (nhds L) :=
  correlationΛ_shifted_tendsto (IsingModel.latticeGraph d) Λ p hf hN

/-- **ℤ^d correlationΛ → correlationInfinite under an explicit subset hypothesis**
(any-Exhaustion). -/
theorem tendsto_correlationΛ_correlationInfinite_of_subset_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {A : Finset (Fin d → ℤ)} {N : ℕ}
    (hN : ∀ n ≥ N, A ⊆ Λ.volume n) :
    Filter.Tendsto
      (fun m : ℕ => correlationΛ (IsingModel.latticeGraph d)
        (Λ.volume (m + N)) p
        (Ambient.liftFinset A (hN (m + N) (Nat.le_add_left N m))))
      Filter.atTop (nhds (correlationInfinite (IsingModel.latticeGraph d) Λ p A)) :=
  tendsto_correlationΛ_correlationInfinite_of_subset
    (IsingModel.latticeGraph d) Λ p hf hN

/-- **ℤ^d physical identification: correlationΛ → correlationInfinite**
(any-Exhaustion). -/
theorem tendsto_correlationΛ_correlationInfinite_latticeGraph_general
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset (Fin d → ℤ)) :
    ∃ N : ℕ, ∃ hN : ∀ n ≥ N, A ⊆ Λ.volume n,
      Filter.Tendsto
        (fun m : ℕ => correlationΛ (IsingModel.latticeGraph d)
          (Λ.volume (m + N)) p
          (Ambient.liftFinset A (hN (m + N) (Nat.le_add_left N m))))
        Filter.atTop (nhds (correlationInfinite (IsingModel.latticeGraph d)
          Λ p A)) :=
  tendsto_correlationΛ_correlationInfinite (IsingModel.latticeGraph d) Λ p hf A

/-- **ℤ^d physical identification: correlationΛ → correlationInfinite**. -/
theorem tendsto_correlationΛ_correlationInfinite_latticeGraph
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset (Fin d → ℤ)) :
    ∃ N : ℕ, ∃ hN : ∀ n ≥ N, A ⊆ (Ambient.cubicExhaustion d).volume n,
      Filter.Tendsto
        (fun m : ℕ => correlationΛ (IsingModel.latticeGraph d)
          ((Ambient.cubicExhaustion d).volume (m + N)) p
          (liftFinset A (hN (m + N) (Nat.le_add_left N m))))
        Filter.atTop (nhds (correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p A)) :=
  tendsto_correlationΛ_correlationInfinite (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf A

/-! ## Moved: correlationAlongExhaustion ciSup / infinite-limit wrappers

The four wrappers
`correlationAlongExhaustion_latticeGraph_tendsto_ciSup_general`,
`correlationAlongExhaustion_latticeGraph_tendsto_ciSup`,
`tendsto_correlationAlongExhaustion_correlationInfinite_latticeGraph`,
`tendsto_correlationAlongExhaustion_correlationInfinite_latticeGraph_general`
now live in `CorrelationExhaustionLimitsAlongExhaustion.lean`. -/


end Ambient
end IsingModel

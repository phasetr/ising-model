import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete partition/free-energy along-exhaustion bounds

Narrow child module for concrete `latticeGraph` partition-function
along-exhaustion volume / parameter monotonicity, positivity, divergence, and
infinite-volume free-energy positivity wrappers. The theorem names are the same
as the former declarations, but callers can now avoid importing the
monolithic concrete module.
-/

namespace IsingModel
namespace Ambient

/-! ### ℤ^d partition/free-energy along-exhaustion wrappers -/

/-- **ℤ^d log partitionFunctionAlongExhaustion volume-monotonicity**
(ferromagnetic, any-Exhaustion). -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_monotone_volume
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        Λ p n)
      ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          Λ p (n + 1)) :=
  log_partitionFunctionAlongExhaustion_monotone_volume
    (IsingModel.latticeGraph d) Λ p hf n

/-- **ℤ^d partitionFunctionAlongExhaustion volume-monotonicity**
(ferromagnetic, any-Exhaustion). -/
theorem partitionFunctionAlongExhaustion_latticeGraph_monotone_volume
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ p n
      ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          Λ p (n + 1) :=
  partitionFunctionAlongExhaustion_monotone_volume
    (IsingModel.latticeGraph d) Λ p hf n

/-! ## Moved: cubicEx volume monotone + pos wrappers

The three wrappers
`log_partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_monotone_volume`,
`partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_monotone_volume`,
`partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_pos` now live
in `PartitionExhaustionBoundsCubic.lean`. -/


/-- **ℤ^d partitionFunctionAlongExhaustion positivity** (any Exhaustion). -/
theorem partitionFunctionAlongExhaustion_latticeGraph_pos
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (n : ℕ) :
    0 < partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ p n :=
  partitionFunctionAlongExhaustion_pos (IsingModel.latticeGraph d) Λ p n

/-! ## Moved: freeEnergyInfinite positivity / non-negativity wrappers

The four `freeEnergyInfinite_latticeGraph_*` wrappers
(`cubicExhaustion_pos`, `cubicExhaustion_nonneg`, `pos`, `nonneg`) now
live in `PartitionExhaustionBoundsFreeEnergyInfinite.lean`. -/



/-! ## Moved: along-ex tendsto_atTop wrappers

The four wrappers
`{log_,}partitionFunctionAlongExhaustion_latticeGraph_tendsto_atTop{_general,}`
now live in `PartitionExhaustionBoundsTendsto.lean`. -/

/-! ## Moved: partitionFunctionAlongExhaustion parameter monotonicity wrappers

The six wrappers
`partitionFunctionAlongExhaustion_latticeGraph_(_cubicExhaustion)?_monotone_{J,h,beta}`
now live in `PartitionExhaustionBoundsMonotoneParams.lean`. -/


end Ambient
end IsingModel

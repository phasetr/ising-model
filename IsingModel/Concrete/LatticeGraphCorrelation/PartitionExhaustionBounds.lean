import IsingModel.Concrete.LatticeGraphBED

/-!
# Concrete partition/free-energy along-exhaustion bounds

Narrow child module for concrete `latticeGraph` partition-function
along-exhaustion volume / parameter monotonicity, positivity, divergence, and
infinite-volume free-energy positivity wrappers. The theorem names are the same
as the former legacy declarations, but callers can now avoid importing the
monolithic concrete legacy module.
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

/-- **ℤ^d log partitionFunctionAlongExhaustion volume-monotonicity** (ferromagnetic). -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_monotone_volume
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p n)
      ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p (n + 1)) :=
  log_partitionFunctionAlongExhaustion_monotone_volume
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p hf n

/-- **ℤ^d partitionFunctionAlongExhaustion volume-monotonicity** (ferromagnetic):
`partitionFunctionAlongExhaustion` at stage `n+1` is ≥ stage `n`. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_monotone_volume
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p n
      ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p (n + 1) :=
  partitionFunctionAlongExhaustion_monotone_volume (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf n

/-- **ℤ^d partitionFunctionAlongExhaustion positivity**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_pos
    (d : ℕ) (p : IsingParams ℝ) (n : ℕ) :
    0 < partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p n :=
  partitionFunctionAlongExhaustion_pos (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p n

/-- **ℤ^d partitionFunctionAlongExhaustion positivity** (any Exhaustion). -/
theorem partitionFunctionAlongExhaustion_latticeGraph_pos
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (n : ℕ) :
    0 < partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ p n :=
  partitionFunctionAlongExhaustion_pos (IsingModel.latticeGraph d) Λ p n

/-- **ℤ^d freeEnergyInfinite is strictly positive** (ferromagnetic). -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_pos
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    0 < freeEnergyInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p := by
  refine freeEnergyInfinite_pos (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf (c := (d : ℝ)) ?_
  intro n _
  exact inducedLatticeGraph_card_edgeFinset_le d
    ((Ambient.cubicExhaustion d).volume n)

/-- **ℤ^d freeEnergyInfinite is nonnegative** (ferromagnetic). -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_nonneg
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    0 ≤ freeEnergyInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p :=
  (freeEnergyInfinite_latticeGraph_cubicExhaustion_pos d p hf).le

/-- **ℤ^d freeEnergyInfinite strictly positive** (ferromagnetic, any Exhaustion). -/
theorem freeEnergyInfinite_latticeGraph_pos
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((Ambient.inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card : ℝ)
        ≤ c * Fintype.card (↑(Λ.volume n) : Type _)) :
    0 < freeEnergyInfinite (IsingModel.latticeGraph d) Λ p :=
  freeEnergyInfinite_pos (IsingModel.latticeGraph d) Λ p hf (c := c) hc

/-- **ℤ^d freeEnergyInfinite nonnegative** (ferromagnetic, any Exhaustion). -/
theorem freeEnergyInfinite_latticeGraph_nonneg
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((Ambient.inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card : ℝ)
        ≤ c * Fintype.card (↑(Λ.volume n) : Type _)) :
    0 ≤ freeEnergyInfinite (IsingModel.latticeGraph d) Λ p :=
  (freeEnergyInfinite_latticeGraph_pos d Λ p hf hc).le

/-- **log Z → ∞ along any-Exhaustion** (ferromagnetic, infinite ℤ^d). -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_tendsto_atTop_general
    (d : ℕ) [Infinite (Fin d → ℤ)]
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    Filter.Tendsto
      (fun n => Real.log (partitionFunctionAlongExhaustion
        (IsingModel.latticeGraph d) Λ p n))
      Filter.atTop Filter.atTop :=
  log_partitionFunctionAlongExhaustion_tendsto_atTop
    (IsingModel.latticeGraph d) Λ p hf

/-- **log Z → ∞ along cubicExhaustion** (ferromagnetic, infinite ℤ^d). -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_tendsto_atTop
    (d : ℕ) [Infinite (Fin d → ℤ)]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    Filter.Tendsto
      (fun n => Real.log (partitionFunctionAlongExhaustion
        (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p n))
      Filter.atTop Filter.atTop :=
  log_partitionFunctionAlongExhaustion_tendsto_atTop
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p hf

/-- **Z → ∞ along any-Exhaustion** (ferromagnetic, infinite ℤ^d). -/
theorem partitionFunctionAlongExhaustion_latticeGraph_tendsto_atTop_general
    (d : ℕ) [Infinite (Fin d → ℤ)]
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    Filter.Tendsto
      (fun n => partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        Λ p n)
      Filter.atTop Filter.atTop :=
  partitionFunctionAlongExhaustion_tendsto_atTop
    (IsingModel.latticeGraph d) Λ p hf

/-- **Z → ∞ along cubicExhaustion** (ferromagnetic, infinite ℤ^d). -/
theorem partitionFunctionAlongExhaustion_latticeGraph_tendsto_atTop
    (d : ℕ) [Infinite (Fin d → ℤ)]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    Filter.Tendsto
      (fun n => partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p n)
      Filter.atTop Filter.atTop :=
  partitionFunctionAlongExhaustion_tendsto_atTop
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p hf

/-! ## Moved: partitionFunctionAlongExhaustion parameter monotonicity wrappers

The six wrappers
`partitionFunctionAlongExhaustion_latticeGraph_(_cubicExhaustion)?_monotone_{J,h,beta}`
now live in `PartitionExhaustionBoundsMonotoneParams.lean`. -/


end Ambient
end IsingModel

import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete partition/free-energy parameter monotonicity wrappers

Thin `ℤ^d` specializations of finite-volume and along-exhaustion partition /
free-energy monotonicity statements.  These wrappers keep downstream users from
importing the original concrete correlation module when they only need parameter
monotonicity or zero-parameter comparison facts.
-/

namespace IsingModel

namespace Ambient

/-! ## Along-exhaustion free-energy bounds and monotonicity -/

/-- **ℤ^d per-stage explicit upper bound on freeEnergyAlongExhaustion**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_upper_bound
    (d : ℕ) (p : IsingParams ℝ) (n : ℕ)
    (hne : ((Ambient.cubicExhaustion d).volume n).Nonempty) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p n ≤ Real.log 2 +
      |p.β| * (|p.J| * (Ambient.inducedGraph (IsingModel.latticeGraph d)
          ((Ambient.cubicExhaustion d).volume n)).edgeFinset.card
          + |p.h| * Fintype.card
            (↑((Ambient.cubicExhaustion d).volume n) : Type _))
        / Fintype.card (↑((Ambient.cubicExhaustion d).volume n) : Type _) :=
  freeEnergyAlongExhaustion_upper_bound (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p n hne

/-- **ℤ^d `freeEnergyAlongExhaustion` per-stage upper bound** (any-Exhaustion):
`≤ log 2 + |β|·(|J|·|E_n|+|h|·|V_n|)/|V_n|`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_upper_bound
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ p n
      ≤ Real.log 2 + |p.β| *
          (|p.J| * (Ambient.inducedGraph (IsingModel.latticeGraph d)
              (Λ.volume n)).edgeFinset.card
            + |p.h| * Fintype.card (↑(Λ.volume n) : Type _))
        / Fintype.card (↑(Λ.volume n) : Type _) :=
  freeEnergyAlongExhaustion_upper_bound
    (IsingModel.latticeGraph d) Λ p n hne

/-! ## Moved: freeEnergyAlongExhaustion monotonicity wrappers

The six wrappers
`freeEnergyAlongExhaustion_latticeGraph_(_cubicExhaustion)?_monotone_{J,h,beta}`
now live in `PartitionFreeEnergyMonotonicityFreeEnergyAlongEx.lean`. -/


/-! ## Moved: along-exhaustion `log_partitionFunctionAlongExhaustion` monotonicity wrappers

The three wrappers
`log_partitionFunctionAlongExhaustion_latticeGraph_monotone_J`,
`log_partitionFunctionAlongExhaustion_latticeGraph_monotone_h`,
`log_partitionFunctionAlongExhaustion_latticeGraph_monotone_beta` now live in
`PartitionFreeEnergyMonotonicityAlongExLog.lean`. -/


/-- **ℤ^d freeEnergyAlongExhaustion ≥ zero_params**: `f(0,0,β) ≤ f(J,h,β)`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_ge_zero_params
    (d : ℕ) {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨0, 0, β⟩ n
      ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, h, β⟩ n :=
  freeEnergyAlongExhaustion_ge_zero_params (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hh hβ n

/-- **ℤ^d partitionFunctionAlongExhaustion ≥ zero_params** analog. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_ge_zero_params
    (d : ℕ) {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨0, 0, β⟩ n
      ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, h, β⟩ n :=
  partitionFunctionAlongExhaustion_ge_zero_params (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hh hβ n

/-! ## Lambda-layer partition-function monotonicity -/

/-! ## Moved: Λ-layer partitionFunctionΛ / log_partitionFunctionΛ monotonicity wrappers

The six wrappers `partitionFunctionΛ_latticeGraph_monotone_{J,h,beta}`
and `log_partitionFunctionΛ_latticeGraph_monotone_{J,h,beta}` now live in
`PartitionFreeEnergyMonotonicityLambda.lean`. -/

/-! ## Moved: cubic log monotone wrappers

The three
`log_partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_monotone_{J,h,beta}`
wrappers now live in `PartitionFreeEnergyMonotonicityCubicLog.lean`. -/



end Ambient

end IsingModel

import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete partition/free-energy lower and upper bound wrappers

Thin `ℤ^d` specializations of partition-function and free-energy bounds,
nonnegativity facts, and infinite-volume bridge statements.  These wrappers keep
downstream imports away from the original concrete correlation module when only
order-theoretic or bound facts are needed.
-/

namespace IsingModel

namespace Ambient

/-! ## Lambda-layer partition and free-energy bounds -/

/-- **ℤ^d partitionFunctionΛ ≥ 1** (ferromagnetic). -/
theorem partitionFunctionΛ_latticeGraph_ge_one
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (hf : Ferromagnetic p) :
    1 ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ p :=
  partitionFunctionΛ_ge_one_of_ferromagnetic (IsingModel.latticeGraph d) Λ p hf

/-- **ℤ^d partitionFunctionΛ ≥ 2^|Λ|** (ferromagnetic, per-Λ). -/
theorem partitionFunctionΛ_latticeGraph_ge_two_pow_card
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (hf : Ferromagnetic p) :
    (2 : ℝ) ^ Λ.card
      ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ p :=
  partitionFunctionΛ_ge_two_pow_card_of_ferromagnetic
    (IsingModel.latticeGraph d) Λ p hf

/-- **ℤ^d log partitionFunctionΛ ≥ |Λ|·log 2** (ferromagnetic). -/
theorem log_partitionFunctionΛ_latticeGraph_ge_card_mul_log_two
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (hf : Ferromagnetic p) :
    (Λ.card : ℝ) * Real.log 2
      ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ p) :=
  log_partitionFunctionΛ_ge_card_mul_log_two_of_ferromagnetic
    (IsingModel.latticeGraph d) Λ p hf

/-- **ℤ^d `log Z_Λ ≥ 0`** (ferromagnetic). -/
theorem log_partitionFunctionΛ_latticeGraph_nonneg
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (hf : Ferromagnetic p) :
    0 ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ p) :=
  log_partitionFunctionΛ_nonneg_of_ferromagnetic
    (IsingModel.latticeGraph d) Λ p hf

/-! ## Moved: ℤ^d freeEnergyΛ identity/nonneg wrappers

The three wrappers
`freeEnergyΛ_latticeGraph_eq_inv_card_mul_log`,
`freeEnergyΛ_latticeGraph_eq_inv_Λcard_mul_log`,
`freeEnergyΛ_latticeGraph_nonneg_of_ferromagnetic` now live in
`PartitionFreeEnergyBoundsFreeEnergyLambda.lean`. -/


/-! ## Moved: ℤ^d partition (2 cosh)^|Λ| sharp bound wrappers

The two wrappers
`partitionFunctionΛ_latticeGraph_ge_two_cosh_pow_card`,
`log_partitionFunctionΛ_latticeGraph_ge_card_mul_log_two_cosh` now live
in `PartitionFreeEnergyBoundsCosh.lean`. -/


/-! ## Moved: ℤ^d freeEnergyAlongExhaustion identity wrappers

The 4 ℤ^d `freeEnergyAlongExhaustion_latticeGraph_*` per-stage
identity / nonneg wrappers (`eq_inv_card_mul_log`,
`eq_inv_Λcard_mul_log`, `nonneg_of_ferromagnetic`, `eq_log_div_card`)
now live in
`IsingModel.Concrete.LatticeGraphCorrelation.PartitionFreeEnergyBoundsFeAlongExId`.
The earlier import path is preserved by re-importing the new child.
-/


/-! ## Moved: ℤ^d AlongExhaustion partition / log-partition bounds

The 8 ℤ^d `partitionFunctionAlongExhaustion_latticeGraph_*` and
`log_partitionFunctionAlongExhaustion_latticeGraph_*` ferromagnetic
bound wrappers (`ge_one`, `ge_one_general`, `ge_two_pow_card`,
`ge_two_cosh_pow_card`, `nonneg_general`, `nonneg`,
`ge_card_mul_log_two`, `ge_card_mul_log_two_cosh`) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.PartitionFreeEnergyBoundsAlongEx`.
The earlier import path is preserved by re-importing the new child.
-/


/-! ## Moved: ℤ^d freeEnergyInfinite bridge / BED upper-bound wrappers

The 6 ℤ^d `freeEnergyInfinite_latticeGraph_*` bridge wrappers
(`eq_of_tendsto`, `of_eventually_const`, `cubicExhaustion_eq_of_tendsto`,
`cubicExhaustion_of_eventually_const`, `le_uniform_upper_bound`,
`cubicExhaustion_le_uniform_upper_bound`) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.PartitionFreeEnergyBoundsInfinite`.
The earlier import path is preserved by re-importing the new child.
-/


/-! ## Moved: ℤ^d freeEnergyAlongExhaustion bridge / per-stage bound wrappers

The 8 ℤ^d `freeEnergyAlongExhaustion_latticeGraph_*` BddAbove /
per-stage upper-bound / per-stage `log 2` and `log(2 cosh)`
lower-bound / ferromagnetic per-stage nonneg wrappers now live in
`IsingModel.Concrete.LatticeGraphCorrelation.PartitionFreeEnergyBoundsAlongExBridges`.
The earlier import path is preserved by re-importing the new child.
-/

end Ambient

end IsingModel

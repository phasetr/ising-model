import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete ℤ^d AlongExhaustion partition / log-partition bounds

Narrow child module for the 8 ℤ^d
`partitionFunctionAlongExhaustion_latticeGraph_*` and
`log_partitionFunctionAlongExhaustion_latticeGraph_*` ferromagnetic
bound wrappers (`ge_one`, `ge_one_general`, `ge_two_pow_card`,
`ge_two_cosh_pow_card`, `nonneg_general`, `nonneg`,
`ge_card_mul_log_two`, `ge_card_mul_log_two_cosh`) extracted from
`PartitionFreeEnergyBounds.lean` in PR #2056. Each is a thin
pass-through to the corresponding ambient
`partitionFunctionAlongExhaustion_*` /
`log_partitionFunctionAlongExhaustion_*` bound lemma at
`IsingModel.latticeGraph d`. The theorem names are unchanged from
the former `PartitionFreeEnergyBounds` declarations.
-/

namespace IsingModel

namespace Ambient

/-- **ℤ^d partitionFunctionAlongExhaustion ≥ 1** (ferromagnetic). -/
theorem partitionFunctionAlongExhaustion_latticeGraph_ge_one
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    1 ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p n :=
  partitionFunctionAlongExhaustion_ge_one_of_ferromagnetic
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p hf n

/-- **ℤ^d partitionFunctionAlongExhaustion ≥ 1** (ferromagnetic, any Exhaustion). -/
theorem partitionFunctionAlongExhaustion_latticeGraph_ge_one_general
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    1 ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ p n :=
  partitionFunctionAlongExhaustion_ge_one_of_ferromagnetic
    (IsingModel.latticeGraph d) Λ p hf n

/-- **ℤ^d log Z_n ≥ 0** (ferromagnetic, any Exhaustion). -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_nonneg_general
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    0 ≤ Real.log (partitionFunctionAlongExhaustion
        (IsingModel.latticeGraph d) Λ p n) :=
  log_partitionFunctionAlongExhaustion_nonneg_of_ferromagnetic
    (IsingModel.latticeGraph d) Λ p hf n

/-- **ℤ^d log partitionFunctionAlongExhaustion ≥ 0** (ferromagnetic). -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_nonneg
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    0 ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p n) :=
  log_partitionFunctionAlongExhaustion_nonneg_of_ferromagnetic
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p hf n

/-! ## Moved: partitionFunctionAlongEx 2^|Λ_n| / (2 cosh)^|Λ_n|

The four wrappers
`partitionFunctionAlongExhaustion_latticeGraph_ge_two_pow_card`,
`partitionFunctionAlongExhaustion_latticeGraph_ge_two_cosh_pow_card`,
`log_partitionFunctionAlongExhaustion_latticeGraph_ge_card_mul_log_two`,
`log_partitionFunctionAlongExhaustion_latticeGraph_ge_card_mul_log_two_cosh`
now live in `PartitionFreeEnergyBoundsAlongExCosh.lean`. -/


end Ambient

end IsingModel

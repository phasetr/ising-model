import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioLogFeLogBoundOnlySingletons

/-!
# Ambient alongExhaustion ferromagnetic log Z ratio_bound_bundle wrapper at h = 0

Narrow child module for the §18.3-§18.4 ambient alongExhaustion
ferromagnetic
`log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound_bundle_ferromagnetic`
wrapper extracted from
`HighTemperatureBoundsRatioLogFeLogBoundOnly.lean`.

To avoid an import cycle, the proof builds the conjunction
directly from the two
`HighTemperatureBoundsRatioLogFeLogBoundOnlySingletons`
slice-singleton wrappers under `mul_nonneg hβ.le hJ`. Theorem name
is unchanged from the former
`HighTemperatureBoundsRatioLogFeLogBound` declaration.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Along-ex ferromagnetic log Z ratio bound bundle at stage `n`**. -/
theorem
log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound_bundle_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n)
        - Real.log (partitionFunctionAlongExhaustion G Λ
            (⟨0, 0, β⟩ : IsingParams ℝ) n)
        ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card ∧
    Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n)
        - Real.log (partitionFunctionAlongExhaustion G Λ
            (⟨J, 0, 0⟩ : IsingParams ℝ) n)
        ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card :=
  ⟨log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound
      G Λ J β (mul_nonneg hβ.le hJ) n,
   log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound_beta_zero
      G Λ J β (mul_nonneg hβ.le hJ) n⟩

end Ambient

end IsingModel

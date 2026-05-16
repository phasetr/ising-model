import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioBoundsBoundOnly

/-!
# Ambient alongExhaustion ferromagnetic Z ratio_bound_bundle wrapper at h = 0

Narrow child module for the §18.3-§18.4 ambient alongExhaustion
ferromagnetic
`partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound_bundle_ferromagnetic`
wrapper extracted from `HighTemperatureBoundsRatioBoundsBound.lean`.

To avoid an import cycle, the proof builds the conjunction directly
from the two non-bundle slice wrappers `_ratio_bound` /
`_ratio_bound_beta_zero` in
`HighTemperatureBoundsRatioBoundsBoundOnly`, derived under
`mul_nonneg hβ.le hJ`. The theorem name is unchanged from the former
`HighTemperatureBoundsRatioBounds` declaration.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Along-ex ferromagnetic Z ratio upper bound bundle at stage `n`**. -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound_bundle_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n /
        partitionFunctionAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n
        ≤ Real.exp (β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card) ∧
    partitionFunctionAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n /
        partitionFunctionAlongExhaustion G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) n
        ≤ Real.exp (β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card) :=
  ⟨partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound
      G Λ J β (mul_nonneg hβ.le hJ) n,
   partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound_beta_zero
      G Λ J β (mul_nonneg hβ.le hJ) n⟩

end Ambient

end IsingModel

import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioBoundsSingletons

/-!
# Ambient alongExhaustion ferromagnetic Z ratio_sandwich_bundle wrapper at h = 0

Narrow child module for the §18.3-§18.4 ambient alongExhaustion
ferromagnetic
`partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_sandwich_bundle_ferromagnetic`
wrapper extracted from `HighTemperatureBoundsRatioBounds.lean`.

To avoid an import cycle, the proof builds the conjunction directly
from the two
`HighTemperatureBoundsRatioBoundsSingletons` slice-singleton
wrappers under `mul_nonneg hβ.le hJ`. The theorem name is unchanged
from the former `HighTemperatureBounds` declaration.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Along-ex ferromagnetic Z ratio sandwich bundle at stage `n`**. -/
theorem
partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_sandwich_bundle_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    (Real.cosh (β * J) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card
        ≤ partitionFunctionAlongExhaustion G Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n /
            partitionFunctionAlongExhaustion G Λ
              (⟨0, 0, β⟩ : IsingParams ℝ) n ∧
      partitionFunctionAlongExhaustion G Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n /
          partitionFunctionAlongExhaustion G Λ
            (⟨0, 0, β⟩ : IsingParams ℝ) n
        ≤ Real.exp (β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card)) ∧
    (Real.cosh (β * J) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card
        ≤ partitionFunctionAlongExhaustion G Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n /
            partitionFunctionAlongExhaustion G Λ
              (⟨J, 0, 0⟩ : IsingParams ℝ) n ∧
      partitionFunctionAlongExhaustion G Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n /
          partitionFunctionAlongExhaustion G Λ
            (⟨J, 0, 0⟩ : IsingParams ℝ) n
        ≤ Real.exp (β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card)) :=
  ⟨partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_sandwich
      G Λ J β (mul_nonneg hβ.le hJ) n,
   partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_sandwich_beta_zero
      G Λ J β (mul_nonneg hβ.le hJ) n⟩

end Ambient

end IsingModel

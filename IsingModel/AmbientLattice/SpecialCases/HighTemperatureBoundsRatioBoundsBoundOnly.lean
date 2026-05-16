import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioBounds
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioBoundsBoundOnlyFerro

/-!
# Ambient alongExhaustion Z ratio_bound non-bundle wrappers at h = 0

Narrow child module for the four §18.3-§18.4 ambient alongExhaustion
`partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound*`
non-bundle wrappers (`J = 0`, `β = 0`, plus their ferromagnetic
counterparts). The non-ferromagnetic wrappers extract from
`_ratio_sandwich*`; the ferromagnetic variants call their
non-ferromagnetic siblings under `mul_nonneg hβ.le hJ`. Theorem
names are unchanged from the former
`HighTemperatureBoundsRatioBoundsBound` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Along-ex Z ratio upper bound at J=0, stage `n`**. -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n /
        partitionFunctionAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n
      ≤ Real.exp (β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card) :=
  (partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_sandwich
    G Λ J β hβJ n).2

/-- **Along-ex Z ratio upper bound at β=0, stage `n`**. -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n /
        partitionFunctionAlongExhaustion G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) n
      ≤ Real.exp (β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card) :=
  (partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_sandwich_beta_zero
    G Λ J β hβJ n).2

/-! ## Moved: 2 ferromagnetic ratio_bound wrappers

The two ferromagnetic `_ratio_bound*_ferromagnetic` non-bundle
wrappers
(`partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound_ferromagnetic`,
`partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound_beta_zero_ferromagnetic`)
now live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioBoundsBoundOnlyFerro`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

end Ambient

end IsingModel

import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioLogFeLogBoundOnlySingletons

/-!
# Ambient alongExhaustion log Z ratio_bound wrappers at h = 0

Narrow child module for the four §18.3-§18.4 ambient alongExhaustion
`log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound*`
wrappers (`J = 0`, `β = 0`, the general `_bundle`, and the
ferromagnetic `_bundle_ferromagnetic`). Each wrapper is a thin
pass-through to the corresponding `log_partitionFunctionΛ_*`
ambient lemma. Theorem names are unchanged from the former
`HighTemperatureBoundsRatioLogFeLogBound` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-! ## Moved: 2 log Z ratio_bound singleton wrappers

The two slice-singleton wrappers
(`log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound`
[J = 0 trivial slice],
`log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound_beta_zero`
[β = 0 trivial slice]) now live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioLogFeLogBoundOnlySingletons`.
The legacy import path is preserved by re-exporting the new child
from this parent module and from the umbrella.
-/

/-- **Along-ex log Z ratio bound bundle at stage `n`**. -/
theorem log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound_bundle
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
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
      G Λ J β hβJ n,
   log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound_beta_zero
      G Λ J β hβJ n⟩

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
  log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound_bundle
    G Λ J β (mul_nonneg hβ.le hJ) n

end Ambient

end IsingModel

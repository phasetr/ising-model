import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharperComplete
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharperCompleteFerroFE

/-!
# Ambient alongExhaustion sharper-exp complete-summary ferromagnetic wrappers at h = 0

Narrow child module for the three §18.3-§18.4 ambient
alongExhaustion `complete_summary_exp_ferromagnetic` wrappers
covering `partitionFunctionAlongExhaustion`,
`log_partitionFunctionAlongExhaustion`, and
`freeEnergyAlongExhaustion`. Each wrapper is a thin pass-through to
its non-ferromagnetic sibling in the parent under
`mul_nonneg hβ.le hJ`. Theorem names are unchanged from the former
`HighTemperatureBoundsExpSharperComplete` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Along-ex ferromagnetic Z complete-summary exp bundle at stage `n`**. -/
theorem
partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_complete_summary_exp_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    (2 : ℝ) ^ (Λ.volume n).card *
        Real.cosh (β * J) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card
      ≤ partitionFunctionAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n ∧
    partitionFunctionAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
      ≤ (2 : ℝ) ^ (Λ.volume n).card *
          Real.exp (β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card) ∧
    partitionFunctionAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n
      = (2 : ℝ) ^ (Λ.volume n).card ∧
    partitionFunctionAlongExhaustion G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) n
      = (2 : ℝ) ^ (Λ.volume n).card :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_complete_summary_exp
    G Λ J β (mul_nonneg hβ.le hJ) n

/-- **Along-ex ferromagnetic log Z complete-summary exp bundle at stage `n`**. -/
theorem
log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_complete_summary_exp_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    ((Λ.volume n).card : ℝ) * Real.log 2
        + ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) *
            Real.log (Real.cosh (β * J))
      ≤ Real.log (partitionFunctionAlongExhaustion G Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n) ∧
    Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n)
      ≤ ((Λ.volume n).card : ℝ) * Real.log 2
        + β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card ∧
    Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) n) = ((Λ.volume n).card : ℝ) * Real.log 2 ∧
    Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ) n) = ((Λ.volume n).card : ℝ) * Real.log 2 :=
  log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_complete_summary_exp
    G Λ J β (mul_nonneg hβ.le hJ) n

/-! ## Moved: 1 ferromagnetic f complete-summary exp wrapper

The
`freeEnergyAlongExhaustion_high_temp_h_zero_complete_summary_exp_ferromagnetic`
wrapper now lives in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharperCompleteFerroFE`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

end Ambient

end IsingModel

import IsingModel.AmbientLattice.SpecialCases.FreeEnergyHighTempExp

/-!
# Ambient alongExhaustion f/Z/log Z deviation wrappers at h = 0

Narrow child module for the §18.3-§18.4 ambient alongExhaustion
`deviation_bound_exp` / `deviation_sandwich` wrappers (with
ferromagnetic variants for f and log Z). The 4
`freeEnergyAlongExhaustion_*_continuity_*` wrappers were further
narrowed into `HighTemperatureBoundsDeviationContinuity` (PR #2024)
and the 10 strict-deviation wrappers (`relative_sandwich`,
`deviation_pos`, `pow_two_lt`, `_strict_deviation_bundle`) were
further narrowed into `HighTemperatureBoundsDeviationStrict`
(PR #2018). The theorem names are unchanged from the former
`HighTemperatureBounds` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]



/-- **Along-ex sharper f deviation bound at stage `n`**: under
`0 ≤ β·J` and `0 < |Λ_n|`,
`f_n - log 2 ≤ β·J·|E_n|/|Λ_n|`. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_deviation_bound_exp
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n - Real.log 2
      ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
          (Λ.volume n).card := by
  have h := freeEnergyAlongExhaustion_high_temp_h_zero_upper_bound_exp
    G Λ J β hβJ n hne
  linarith

/-! ## Moved: f continuity wrappers

The 4 ambient alongExhaustion `freeEnergyAlongExhaustion_high_temp_h_zero_continuity_*`
wrappers (`_at_J_zero`, `_at_beta_zero`, `_bundle`,
`_bundle_ferromagnetic`) now live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviationContinuity`.
The earlier import path is preserved by re-importing the new child
via the umbrella.
-/


/-- **Along-ex f deviation sandwich at stage `n`**. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_deviation_sandwich
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    0 ≤ freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n - Real.log 2 ∧
    freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n - Real.log 2
      ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
          (Λ.volume n).card := by
  change 0 ≤ freeEnergyΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
      - Real.log 2 ∧ freeEnergyΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
      - Real.log 2 ≤ _
  exact freeEnergyΛ_high_temp_h_zero_deviation_sandwich
    G (Λ.volume n) J β hβJ hne

/-- **Along-ex log Z deviation sandwich at stage `n`**. -/
theorem log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_deviation_sandwich
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    0 ≤ Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n)
        - ((Λ.volume n).card : ℝ) * Real.log 2 ∧
    Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n)
        - ((Λ.volume n).card : ℝ) * Real.log 2
      ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card := by
  change 0 ≤ Real.log (partitionFunctionΛ G (Λ.volume n)
      (⟨J, 0, β⟩ : IsingParams ℝ)) - _ ∧ Real.log (partitionFunctionΛ G
      (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)) - _ ≤ _
  exact log_partitionFunctionΛ_high_temp_expansion_h_zero_deviation_sandwich
    G (Λ.volume n) J β hβJ

/-! ## Moved: ferromagnetic deviation wrappers

The three `*_deviation_*_ferromagnetic` wrappers
(`freeEnergyAlongExhaustion_..._deviation_bound_exp_ferromagnetic`,
`freeEnergyAlongExhaustion_..._deviation_sandwich_ferromagnetic`,
`log_partitionFunctionAlongExhaustion_..._deviation_sandwich_ferromagnetic`)
now live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviationFerro`.
The earlier import path is preserved by re-exporting the new child
from the umbrella `HighTemperatureBounds.lean`.
-/

/-! ## Moved: strict-deviation wrappers

The 10 ambient alongExhaustion strict-deviation wrappers covering
`*_relative_sandwich`, `*_deviation_pos`, `*_pow_two_lt`,
`log_partitionFunctionAlongExhaustion_*_deviation_pos`, and
`_strict_deviation_bundle` (with ferromagnetic variants) now live
in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviationStrict`.
The earlier import path is preserved by re-importing the new child
via the umbrella.
-/

end Ambient

end IsingModel

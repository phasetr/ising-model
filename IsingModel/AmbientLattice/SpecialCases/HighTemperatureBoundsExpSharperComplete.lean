import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansion
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharper
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharperSandwich
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansionClosedSlices

/-!
# Ambient alongExhaustion sharper-exp complete-summary wrappers at h = 0

Narrow child module for 6 §18.3-§18.4 ambient alongExhaustion
`complete_summary_exp` wrappers covering
`freeEnergyAlongExhaustion`, `partitionFunctionAlongExhaustion`, and
`log_partitionFunctionAlongExhaustion` complete-summary-exp bundles
under `0 ≤ β·J` / `0 < |Λ_n|` with ferromagnetic variants under
`0 ≤ J`, `0 < β`. Theorem names are unchanged from the former
`HighTemperatureBoundsExpSharper` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-! ## Moved: 1 freeEnergy complete-summary exp wrapper

The
`freeEnergyAlongExhaustion_high_temp_h_zero_complete_summary_exp`
wrapper now lives in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharperCompleteFE`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

/-- **Along-ex sharper Z complete-summary exp bundle at stage `n`**:
under `0 ≤ β·J`, single statement bundling sharper sandwich +
trivial-slice values. -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_complete_summary_exp
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    (2 : ℝ) ^ (Λ.volume n).card *
        Real.cosh (β * J) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card
      ≤ partitionFunctionAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n ∧
    partitionFunctionAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
      ≤ (2 : ℝ) ^ (Λ.volume n).card *
          Real.exp (β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card) ∧
    partitionFunctionAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n
      = (2 : ℝ) ^ (Λ.volume n).card ∧
    partitionFunctionAlongExhaustion G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) n
      = (2 : ℝ) ^ (Λ.volume n).card := by
  obtain ⟨h1, h2⟩ :=
    partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_sandwich_exp
      G Λ J β hβJ n
  exact ⟨h1, h2,
    partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_closed_at_J_zero
      G Λ β n,
    partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_closed_at_beta_zero
      G Λ J n⟩

/-- **Along-ex sharper log Z complete-summary exp bundle at stage `n`**:
under `0 ≤ β·J`, single statement bundling sharper sandwich +
trivial-slice values. -/
theorem log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_complete_summary_exp
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
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
        (⟨J, 0, 0⟩ : IsingParams ℝ) n) = ((Λ.volume n).card : ℝ) * Real.log 2 := by
  change ((Λ.volume n).card : ℝ) * _ + _ * _ ≤
      Real.log (partitionFunctionΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)) ∧
      Real.log (partitionFunctionΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)) ≤ _
        ∧ Real.log (partitionFunctionΛ G (Λ.volume n) (⟨0, 0, β⟩ : IsingParams ℝ)) = _
        ∧ Real.log (partitionFunctionΛ G (Λ.volume n) (⟨J, 0, 0⟩ : IsingParams ℝ)) = _
  exact log_partitionFunctionΛ_high_temp_expansion_h_zero_complete_summary_exp
    G (Λ.volume n) J β hβJ

/-! ## Moved: ferromagnetic complete-summary exp wrappers

The three ferromagnetic `complete_summary_exp_ferromagnetic`
wrappers (for `partitionFunction`, `log_partitionFunction`,
`freeEnergy`) now live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharperCompleteFerro`.
The earlier import path is preserved by re-exporting the new child
from the umbrella `HighTemperatureBounds.lean`.
-/

end Ambient

end IsingModel

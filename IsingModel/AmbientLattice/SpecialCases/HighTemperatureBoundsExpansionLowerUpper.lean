import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansionLowerUpperFE
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansionLowerUpperConsistency

/-!
# Ambient alongExhaustion expansion lower/upper-bound wrappers at h = 0

Narrow child module for the §18.3-§18.4 ambient alongExhaustion
partition function / free energy / log partition function
high-temperature expansion lower-bound, upper-bound, closed-form, and
lower_le_upper consistency wrappers. 8 theorems wrapping the Λ-level
versions through the stage-`n` subtype `↑(Λ.volume n)`. The theorem
names are unchanged from the former
`HighTemperatureBoundsExpansion` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-! ## Along-exhaustion high-temperature lower bounds (GJ §18.3) -/

/-- **Along-exhaustion log Z high-temperature decomposition (GJ §18.3 / FV (3.45))**:
under `0 ≤ β·J`, at every stage `n`,
`log Z_n(⟨J, 0, β⟩) = |Λ_n| · log 2 + |E_n| · log(cosh βJ) + log(∑_{X even} tanh^|X|)`.
Per-stage application of `log_partitionFunctionΛ_high_temp_expansion_h_zero_closed`
(Step 316). -/
theorem log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_closed
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n)
      = ((Λ.volume n).card : ℝ) * Real.log 2
        + ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) *
            Real.log (Real.cosh (β * J))
        + Real.log
            (∑ X ∈ (inducedGraph G (Λ.volume n)).edgeFinset.powerset.filter
                (fun X : Finset (Sym2 ↑(Λ.volume n)) =>
                  ∀ v : ↑(Λ.volume n), Even ((X.filter (v ∈ ·)).card)),
              Real.tanh (β * J) ^ X.card) := by
  change Real.log (partitionFunctionΛ G (Λ.volume n)
      (⟨J, 0, β⟩ : IsingParams ℝ)) = _
  exact log_partitionFunctionΛ_high_temp_expansion_h_zero_closed
    G (Λ.volume n) J β hβJ

/-- **Along-exhaustion Z high-temperature upper bound (GJ §18.3 / FV (3.45))**:
under `0 ≤ β·J`, at every stage `n`,
`Z_n(⟨J, 0, β⟩) ≤ 2^(|Λ_n|+|E_n|) · cosh(βJ)^|E_n|`.
Per-stage application of `partitionFunctionΛ_high_temp_expansion_h_zero_upper_bound`. -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_upper_bound
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
      ≤ (2 : ℝ) ^ ((Λ.volume n).card +
            (inducedGraph G (Λ.volume n)).edgeFinset.card) *
        Real.cosh (β * J) ^
            (inducedGraph G (Λ.volume n)).edgeFinset.card := by
  change partitionFunctionΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ) ≤ _
  exact partitionFunctionΛ_high_temp_expansion_h_zero_upper_bound
    G (Λ.volume n) J β hβJ

/-! ## Moved: 2 lower_le_upper consistency wrappers

The two `lower ≤ upper` bound consistency wrappers
(`partitionFunctionAlongExhaustion_high_temp_h_zero_lower_le_upper`,
`freeEnergyAlongExhaustion_high_temp_h_zero_lower_le_upper`) now
live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansionLowerUpperConsistency`.
The legacy import path is preserved by re-exporting the new child
from this parent module and from `Legacy.lean`.
-/

/-- **Along-exhaustion partition function high-temperature lower bound**:
under `0 ≤ β * J`, at every stage `n`,
`partitionFunctionAlongExhaustion G Λ ⟨J, 0, β⟩ n
  ≥ 2^|Λ.volume n| · (cosh(βJ))^|E_{Λ.volume n}|`.
Per-stage application of `partitionFunctionΛ_high_temp_expansion_h_zero_lower_bound`
(Step 287). -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_lower_bound
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    (2 : ℝ) ^ (Λ.volume n).card *
        Real.cosh (β * J) ^
          (inducedGraph G (Λ.volume n)).edgeFinset.card
      ≤ partitionFunctionAlongExhaustion G Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n := by
  change _ ≤ partitionFunctionΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
  exact partitionFunctionΛ_high_temp_expansion_h_zero_lower_bound
    G (Λ.volume n) J β hβJ

/-! ## Moved: freeEnergyAlongExhaustion HT expansion lower/upper wrappers

The three trailing `freeEnergyAlongExhaustion_high_temp_*` wrappers
(`expansion_h_zero_closed`, `h_zero_upper_bound`, `h_zero_lower_bound`)
now live in `HighTemperatureBoundsExpansionLowerUpperFE.lean`. They are
re-imported here so downstream consumers continue to see the symbols. -/



end Ambient

end IsingModel

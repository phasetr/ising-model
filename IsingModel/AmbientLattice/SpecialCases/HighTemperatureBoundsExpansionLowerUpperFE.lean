import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.AmbientLattice.Analyticity

/-!
# Ambient freeEnergyAlongExhaustion HT expansion lower/upper wrappers

Narrow child module for 3 ambient
`freeEnergyAlongExhaustion_high_temp_*` lower/upper-bound wrappers
extracted from `HighTemperatureBoundsExpansionLowerUpper.lean`:

* `freeEnergyAlongExhaustion_high_temp_expansion_h_zero_closed`,
* `freeEnergyAlongExhaustion_high_temp_h_zero_upper_bound`,
* `freeEnergyAlongExhaustion_high_temp_h_zero_lower_bound`.

Each is a per-stage application of the corresponding Λ-level
`freeEnergyΛ_high_temp_*` lemma. The theorem names are unchanged
from the former `HighTemperatureBoundsExpansionLowerUpper`
declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]


/-- **Along-exhaustion freeEnergy high-temperature decomposition (GJ §18.3 / FV (3.45))**:
under `0 ≤ β·J` and `0 < |Λ.volume n|`, at every stage `n`,
`f_n = log 2 + (|E_n|/|Λ_n|) · log(cosh βJ) + log(∑ tanh^|X|) / |Λ_n|`.
Per-stage application of `freeEnergyΛ_high_temp_expansion_h_zero_closed`
(Step 318). -/
theorem freeEnergyAlongExhaustion_high_temp_expansion_h_zero_closed
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
      = Real.log 2
        + ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
            (Λ.volume n).card * Real.log (Real.cosh (β * J))
        + Real.log
            (∑ X ∈ (inducedGraph G (Λ.volume n)).edgeFinset.powerset.filter
                (fun X : Finset (Sym2 ↑(Λ.volume n)) =>
                  ∀ v : ↑(Λ.volume n), Even ((X.filter (v ∈ ·)).card)),
              Real.tanh (β * J) ^ X.card) / (Λ.volume n).card := by
  change freeEnergyΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ) = _
  exact freeEnergyΛ_high_temp_expansion_h_zero_closed
    G (Λ.volume n) J β hβJ hne

/-- **Along-exhaustion freeEnergy high-temperature upper bound (FV (3.45))**:
under `0 ≤ β·J` and `0 < |Λ.volume n|`, at every stage `n`,
`f_n ≤ log 2 + (|E_n|/|Λ_n|) · log(2 · cosh βJ)`.
Per-stage application of `freeEnergyΛ_high_temp_h_zero_upper_bound`. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_upper_bound
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
      ≤ Real.log 2
        + ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
            (Λ.volume n).card * Real.log (2 * Real.cosh (β * J)) := by
  change freeEnergyΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ) ≤ _
  exact freeEnergyΛ_high_temp_h_zero_upper_bound G (Λ.volume n) J β hβJ hne

/-- **Along-exhaustion free-energy high-temperature lower bound**:
under `0 ≤ β * J` and `0 < |Λ.volume n|`,
`freeEnergyAlongExhaustion G Λ ⟨J, 0, β⟩ n
  ≥ log 2 + (|E_{Λ.volume n}|/|Λ.volume n|) · log(cosh(β·J))`.
Per-stage application of `freeEnergyΛ_high_temp_h_zero_lower_bound`
(Step 289). -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_lower_bound
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    Real.log 2 +
        ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
          (Λ.volume n).card * Real.log (Real.cosh (β * J))
      ≤ freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n := by
  change _ ≤ freeEnergyΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
  exact freeEnergyΛ_high_temp_h_zero_lower_bound
    G (Λ.volume n) J β hβJ hne

end Ambient

end IsingModel

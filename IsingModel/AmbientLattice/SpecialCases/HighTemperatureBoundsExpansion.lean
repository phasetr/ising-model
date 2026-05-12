import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.AmbientLattice.Analyticity

/-!
# Ambient alongExhaustion partition/free-energy expansion wrappers at h = 0

Narrow child module for the §18.3-§18.4 ambient alongExhaustion
partition function / free energy expansion / closed-form / lower-bound /
upper-bound / sandwich / complete-summary wrappers. 20 theorems for
`partitionFunctionAlongExhaustion`, `freeEnergyAlongExhaustion`,
`log_partitionFunctionAlongExhaustion`, `correlationAlongExhaustion`
closed forms, plus `one_le_sum_pow_tanh_even_subgraph_alongExhaustion`
helper. The theorem names are unchanged from the former
`HighTemperatureBounds` declarations.
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

omit [DecidableEq V] in
/-- **Along-exhaustion Z bounds consistency**: lower ≤ upper. -/
theorem partitionFunctionAlongExhaustion_high_temp_h_zero_lower_le_upper
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    (2 : ℝ) ^ (Λ.volume n).card *
        Real.cosh (β * J) ^
          (inducedGraph G (Λ.volume n)).edgeFinset.card
      ≤ (2 : ℝ) ^ ((Λ.volume n).card +
            (inducedGraph G (Λ.volume n)).edgeFinset.card) *
        Real.cosh (β * J) ^
            (inducedGraph G (Λ.volume n)).edgeFinset.card :=
  partitionFunctionΛ_high_temp_h_zero_lower_le_upper G (Λ.volume n) J β

omit [DecidableEq V] in
/-- **Along-exhaustion freeEnergy bounds consistency**: lower ≤ upper. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_lower_le_upper
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    Real.log 2 +
        ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
          (Λ.volume n).card * Real.log (Real.cosh (β * J))
      ≤ Real.log 2
        + ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
            (Λ.volume n).card * Real.log (2 * Real.cosh (β * J)) :=
  freeEnergyΛ_high_temp_h_zero_lower_le_upper G (Λ.volume n) J β hβJ

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
/-! ## Moved: expansion variant + one_le_sum helper

The 4 ambient alongExhaustion `_high_temp_expansion_h_zero` /
`_high_temp_expansion` / `_high_temp_expansion_subset_form` and
`one_le_sum_pow_tanh_even_subgraph_alongExhaustion` wrappers now
live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansionVariants`.
The legacy import path is preserved by re-importing the new child
via the umbrella.
-/


/-! ## Moved: closed-form / sandwich / complete-summary wrappers

The 8 ambient alongExhaustion closed-form / sandwich /
complete-summary wrappers (`*_closed_at_J_zero`,
`*_closed_at_beta_zero`, redundant `*_closed`,
`correlationAlongExhaustion_*_nonneg`, `_closed`,
`*_sandwich`, `*_complete_summary`, freeEnergy
complete_summary) now live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansionClosedForms`.
The legacy import path is preserved by re-importing the new child
via the umbrella.
-/

end Ambient

end IsingModel

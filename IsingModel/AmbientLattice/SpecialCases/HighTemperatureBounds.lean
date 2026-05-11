import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansion

/-!
# High-temperature expansion and bound wrappers along an exhaustion

Narrow child module for the §18.3-§18.4 high-temperature expansion,
lower/upper bound, sandwich, correlation, and deviation wrappers along an
exhaustion. The theorem names are the same as the former legacy declarations,
but callers can now avoid importing the monolithic special-cases legacy module.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]


/-! ## Moved: alongExhaustion partition/free-energy expansion wrappers

The §18.3-§18.4 ambient alongExhaustion partition function / free energy
expansion / closed-form / lower-bound / upper-bound / sandwich /
complete-summary wrappers (20 theorems for
`partitionFunctionAlongExhaustion`, `freeEnergyAlongExhaustion`,
`log_partitionFunctionAlongExhaustion`, `correlationAlongExhaustion` closed
forms, plus the `one_le_sum_pow_tanh_even_subgraph_alongExhaustion` helper)
now live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansion`.
The legacy import path is preserved by re-importing the new child.
-/


/-- **Along-ex sharper Z upper bound at stage `n`**: under `0 ≤ β·J`,
`Z_n(⟨J, 0, β⟩) ≤ 2^|Λ_n| · exp(β·J·|E_n|)`. Stage-`n` Λ-level
specialization of
`partitionFunction_high_temp_expansion_h_zero_upper_bound_exp`. -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_upper_bound_exp
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
      ≤ (2 : ℝ) ^ (Λ.volume n).card *
          Real.exp (β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card) := by
  change partitionFunctionΛ G (Λ.volume n)
      (⟨J, 0, β⟩ : IsingParams ℝ) ≤ _
  exact partitionFunctionΛ_high_temp_expansion_h_zero_upper_bound_exp
    G (Λ.volume n) J β hβJ

/-- **Along-ex sharper log Z upper bound at stage `n`**: under
`0 ≤ β·J`, `log Z_n ≤ |Λ_n|·log 2 + β·J·|E_n|`. Stage-`n` Λ-level
specialization of
`log_partitionFunction_high_temp_expansion_h_zero_upper_bound_exp`. -/
theorem log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_upper_bound_exp
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n)
      ≤ ((Λ.volume n).card : ℝ) * Real.log 2
        + β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card := by
  change Real.log (partitionFunctionΛ G (Λ.volume n)
      (⟨J, 0, β⟩ : IsingParams ℝ)) ≤ _
  exact log_partitionFunctionΛ_high_temp_expansion_h_zero_upper_bound_exp
    G (Λ.volume n) J β hβJ

/-- **Along-ex sharper log Z sandwich at stage `n`**: under `0 ≤ β·J`,
`|Λ_n|·log 2 + |E_n|·log cosh(β·J) ≤ log Z_n ≤ |Λ_n|·log 2 + β·J·|E_n|`. -/
theorem log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_sandwich_exp
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
        + β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card := by
  change ((Λ.volume n).card : ℝ) * _ + _ * _ ≤
      Real.log (partitionFunctionΛ G (Λ.volume n)
        (⟨J, 0, β⟩ : IsingParams ℝ)) ∧ _
  exact log_partitionFunctionΛ_high_temp_expansion_h_zero_sandwich_exp
    G (Λ.volume n) J β hβJ

/-- **Along-ex ferromagnetic Z sharper upper bound at stage `n`**:
under `0 ≤ J, 0 < β`,
`Z_n ≤ 2^|Λ_n| · exp(β·J·|E_n|)`. Stage-`n` Λ-level ferromagnetic
specialization. -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_upper_bound_exp_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
      ≤ (2 : ℝ) ^ (Λ.volume n).card *
          Real.exp (β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card) :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_upper_bound_exp
    G Λ J β (mul_nonneg hβ.le hJ) n

/-- **Along-ex ferromagnetic log Z sharper upper bound at stage `n`**:
under `0 ≤ J, 0 < β`,
`log Z_n ≤ |Λ_n|·log 2 + β·J·|E_n|`. -/
theorem
log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_upper_bound_exp_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n)
      ≤ ((Λ.volume n).card : ℝ) * Real.log 2
        + β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card :=
  log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_upper_bound_exp
    G Λ J β (mul_nonneg hβ.le hJ) n

/-- **Along-ex ferromagnetic f sharper upper bound at stage `n`**:
under `0 ≤ J, 0 < β` and `0 < |Λ_n|`,
`f_n ≤ log 2 + β·J·|E_n|/|Λ_n|`. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_upper_bound_exp_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ)
    (hne : 0 < (Λ.volume n).card) :
    freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
      ≤ Real.log 2 +
          β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
            (Λ.volume n).card :=
  freeEnergyAlongExhaustion_high_temp_h_zero_upper_bound_exp
    G Λ J β (mul_nonneg hβ.le hJ) n hne

/-- **Along-ex sharper Z high-temp sandwich at stage `n`**: under `0 ≤ β·J`,
`2^|Λ_n|·cosh^|E_n| ≤ Z_n ≤ 2^|Λ_n|·exp(β·J·|E_n|)`. -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_sandwich_exp
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    (2 : ℝ) ^ (Λ.volume n).card *
        Real.cosh (β * J) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card
      ≤ partitionFunctionAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n ∧
    partitionFunctionAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
      ≤ (2 : ℝ) ^ (Λ.volume n).card *
          Real.exp (β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card) :=
  ⟨partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_lower_bound
      G Λ J β hβJ n,
   partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_upper_bound_exp
      G Λ J β hβJ n⟩

/-- **Along-ex sharper f high-temp sandwich at stage `n`**: under
`0 ≤ β·J` and `0 < |Λ_n|`,
`log 2 + (|E_n|/|Λ_n|)·log cosh(β·J) ≤ f_n ≤ log 2 + β·J·|E_n|/|Λ_n|`. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_sandwich_exp
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    Real.log 2 +
        ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
          (Λ.volume n).card * Real.log (Real.cosh (β * J))
      ≤ freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n ∧
    freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
      ≤ Real.log 2 +
          β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
            (Λ.volume n).card :=
  ⟨freeEnergyAlongExhaustion_high_temp_h_zero_lower_bound G Λ J β hβJ n hne,
   freeEnergyAlongExhaustion_high_temp_h_zero_upper_bound_exp G Λ J β hβJ n hne⟩

/-- **Along-ex ferromagnetic Z sharper sandwich at stage `n`**: under
`0 ≤ J, 0 < β`,
`2^|Λ_n|·cosh^|E_n| ≤ Z_n ≤ 2^|Λ_n|·exp(β·J·|E_n|)`. -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_sandwich_exp_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    (2 : ℝ) ^ (Λ.volume n).card *
        Real.cosh (β * J) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card
      ≤ partitionFunctionAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n ∧
    partitionFunctionAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
      ≤ (2 : ℝ) ^ (Λ.volume n).card *
          Real.exp (β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card) :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_sandwich_exp
    G Λ J β (mul_nonneg hβ.le hJ) n

/-- **Along-ex ferromagnetic f sharper sandwich at stage `n`**: under
`0 ≤ J, 0 < β` and `0 < |Λ_n|`,
`log 2 + (|E_n|/|Λ_n|)·log cosh(β·J) ≤ f_n ≤ log 2 + β·J·|E_n|/|Λ_n|`. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_sandwich_exp_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ)
    (hne : 0 < (Λ.volume n).card) :
    Real.log 2 +
        ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
          (Λ.volume n).card * Real.log (Real.cosh (β * J))
      ≤ freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n ∧
    freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
      ≤ Real.log 2 +
          β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
            (Λ.volume n).card :=
  freeEnergyAlongExhaustion_high_temp_h_zero_sandwich_exp G Λ J β
    (mul_nonneg hβ.le hJ) n hne

/-- **Along-ex sharper f complete-summary exp bundle at stage `n`**:
under `0 ≤ β·J` and `0 < |Λ_n|`, single statement bundling sharper
sandwich + trivial-slice values. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_complete_summary_exp
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    Real.log 2 +
        ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
          (Λ.volume n).card * Real.log (Real.cosh (β * J))
      ≤ freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n ∧
    freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
      ≤ Real.log 2 +
          β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
            (Λ.volume n).card ∧
    freeEnergyAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n = Real.log 2 ∧
    freeEnergyAlongExhaustion G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) n = Real.log 2 := by
  have hcard : 0 < (Λ.volume n).card := hne.card_pos
  obtain ⟨h1, h2⟩ := freeEnergyAlongExhaustion_high_temp_h_zero_sandwich_exp
    G Λ J β hβJ n hcard
  refine ⟨h1, h2, ?_, ?_⟩
  · exact freeEnergyAlongExhaustion_zero_params G Λ β n hne
  · exact freeEnergyAlongExhaustion_beta_zero G Λ J 0 n hne

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

/-- **Along-ex ferromagnetic f complete-summary exp bundle at stage `n`**. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_complete_summary_exp_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ)
    (hne : (Λ.volume n).Nonempty) :
    Real.log 2 +
        ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
          (Λ.volume n).card * Real.log (Real.cosh (β * J))
      ≤ freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n ∧
    freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
      ≤ Real.log 2 +
          β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
            (Λ.volume n).card ∧
    freeEnergyAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n = Real.log 2 ∧
    freeEnergyAlongExhaustion G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) n = Real.log 2 :=
  freeEnergyAlongExhaustion_high_temp_h_zero_complete_summary_exp
    G Λ J β (mul_nonneg hβ.le hJ) n hne

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

/-- **Along-ex ferromagnetic f deviation bound at stage `n`**: under
`0 ≤ J, 0 < β`, `f_n - log 2 ≤ β·J·|E_n|/|Λ_n|`. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_deviation_bound_exp_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ)
    (hne : 0 < (Λ.volume n).card) :
    freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n - Real.log 2
      ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
          (Λ.volume n).card :=
  freeEnergyAlongExhaustion_high_temp_h_zero_deviation_bound_exp
    G Λ J β (mul_nonneg hβ.le hJ) n hne

/-- **Along-ex f continuity at `J = 0` at stage `n`**. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_continuity_at_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    |freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
        - freeEnergyAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n|
      ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
          (Λ.volume n).card := by
  change |freeEnergyΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
      - freeEnergyΛ G (Λ.volume n) (⟨0, 0, β⟩ : IsingParams ℝ)| ≤ _
  exact freeEnergyΛ_high_temp_h_zero_continuity_at_J_zero
    G (Λ.volume n) J β hβJ hne

/-- **Along-ex f continuity at `β = 0` at stage `n`**. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_continuity_at_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    |freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
        - freeEnergyAlongExhaustion G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) n|
      ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
          (Λ.volume n).card := by
  change |freeEnergyΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
      - freeEnergyΛ G (Λ.volume n) (⟨J, 0, 0⟩ : IsingParams ℝ)| ≤ _
  exact freeEnergyΛ_high_temp_h_zero_continuity_at_beta_zero
    G (Λ.volume n) J β hβJ hne

/-- **Along-ex f continuity bundle at stage `n`**. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_continuity_bundle
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    |freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
        - freeEnergyAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n|
        ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
            (Λ.volume n).card ∧
    |freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
        - freeEnergyAlongExhaustion G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) n|
        ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
            (Λ.volume n).card :=
  ⟨freeEnergyAlongExhaustion_high_temp_h_zero_continuity_at_J_zero
      G Λ J β hβJ n hne,
   freeEnergyAlongExhaustion_high_temp_h_zero_continuity_at_beta_zero
      G Λ J β hβJ n hne⟩

/-- **Along-ex ferromagnetic f continuity bundle at stage `n`**. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_continuity_bundle_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ)
    (hne : 0 < (Λ.volume n).card) :
    |freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
        - freeEnergyAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n|
        ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
            (Λ.volume n).card ∧
    |freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
        - freeEnergyAlongExhaustion G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) n|
        ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
            (Λ.volume n).card :=
  freeEnergyAlongExhaustion_high_temp_h_zero_continuity_bundle
    G Λ J β (mul_nonneg hβ.le hJ) n hne

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

/-- **Along-ex ferromagnetic f deviation sandwich at stage `n`**. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_deviation_sandwich_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ)
    (hne : 0 < (Λ.volume n).card) :
    0 ≤ freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n - Real.log 2 ∧
    freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n - Real.log 2
      ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
          (Λ.volume n).card :=
  freeEnergyAlongExhaustion_high_temp_h_zero_deviation_sandwich
    G Λ J β (mul_nonneg hβ.le hJ) n hne

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

/-- **Along-ex ferromagnetic log Z deviation sandwich at stage `n`**. -/
theorem
log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_deviation_sandwich_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    0 ≤ Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n)
        - ((Λ.volume n).card : ℝ) * Real.log 2 ∧
    Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n)
        - ((Λ.volume n).card : ℝ) * Real.log 2
      ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card :=
  log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_deviation_sandwich
    G Λ J β (mul_nonneg hβ.le hJ) n

/-- **Along-ex Z relative-deviation sandwich at stage `n`**. -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_relative_sandwich
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    Real.cosh (β * J) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card
      ≤ partitionFunctionAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n /
          (2 : ℝ) ^ (Λ.volume n).card ∧
    partitionFunctionAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n /
        (2 : ℝ) ^ (Λ.volume n).card
      ≤ Real.exp (β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card) := by
  change _ ≤ partitionFunctionΛ G (Λ.volume n)
      (⟨J, 0, β⟩ : IsingParams ℝ) / _ ∧ partitionFunctionΛ G (Λ.volume n)
      (⟨J, 0, β⟩ : IsingParams ℝ) / _ ≤ _
  exact partitionFunctionΛ_high_temp_expansion_h_zero_relative_sandwich
    G (Λ.volume n) J β hβJ

/-- **Along-ex ferromagnetic Z relative-deviation sandwich at stage `n`**. -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_relative_sandwich_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    Real.cosh (β * J) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card
      ≤ partitionFunctionAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n /
          (2 : ℝ) ^ (Λ.volume n).card ∧
    partitionFunctionAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n /
        (2 : ℝ) ^ (Λ.volume n).card
      ≤ Real.exp (β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card) :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_relative_sandwich
    G Λ J β (mul_nonneg hβ.le hJ) n

/-- **Along-ex f strict deviation at stage `n`**. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_deviation_pos
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 < β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card)
    (hEpos : 0 < (inducedGraph G (Λ.volume n)).edgeFinset.card) :
    0 < freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n - Real.log 2 := by
  change 0 < freeEnergyΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ) - Real.log 2
  exact freeEnergyΛ_high_temp_h_zero_deviation_pos
    G (Λ.volume n) J β hβJ hne hEpos

/-- **Along-ex ferromagnetic f strict deviation at stage `n`**. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_deviation_pos_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 < J) (hβ : 0 < β) (n : ℕ)
    (hne : 0 < (Λ.volume n).card)
    (hEpos : 0 < (inducedGraph G (Λ.volume n)).edgeFinset.card) :
    0 < freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n - Real.log 2 :=
  freeEnergyAlongExhaustion_high_temp_h_zero_deviation_pos
    G Λ J β (mul_pos hβ hJ) n hne hEpos

/-- **Along-ex Z strict deviation at stage `n`**. -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_pow_two_lt
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 < β * J) (n : ℕ)
    (hEpos : 0 < (inducedGraph G (Λ.volume n)).edgeFinset.card) :
    (2 : ℝ) ^ (Λ.volume n).card
      < partitionFunctionAlongExhaustion G Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n := by
  change _ < partitionFunctionΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
  exact partitionFunctionΛ_high_temp_expansion_h_zero_pow_two_lt
    G (Λ.volume n) J β hβJ hEpos

/-- **Along-ex log Z strict deviation at stage `n`**. -/
theorem log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_deviation_pos
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 < β * J) (n : ℕ)
    (hEpos : 0 < (inducedGraph G (Λ.volume n)).edgeFinset.card) :
    0 < Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n)
        - ((Λ.volume n).card : ℝ) * Real.log 2 := by
  change 0 < Real.log (partitionFunctionΛ G (Λ.volume n)
      (⟨J, 0, β⟩ : IsingParams ℝ)) - _
  exact log_partitionFunctionΛ_high_temp_expansion_h_zero_deviation_pos
    G (Λ.volume n) J β hβJ hEpos

/-- **Along-ex Z + log Z + f strict deviation bundle at stage `n`**. -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_strict_deviation_bundle
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 < β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card)
    (hEpos : 0 < (inducedGraph G (Λ.volume n)).edgeFinset.card) :
    (2 : ℝ) ^ (Λ.volume n).card
        < partitionFunctionAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n ∧
    0 < Real.log (partitionFunctionAlongExhaustion G Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n)
        - ((Λ.volume n).card : ℝ) * Real.log 2 ∧
    0 < freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n - Real.log 2 :=
  ⟨partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_pow_two_lt
     G Λ J β hβJ n hEpos,
   log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_deviation_pos
     G Λ J β hβJ n hEpos,
   freeEnergyAlongExhaustion_high_temp_h_zero_deviation_pos
     G Λ J β hβJ n hne hEpos⟩

/-- **Along-ex ferromagnetic Z + log Z + f strict deviation bundle at stage `n`**. -/
theorem
partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_strict_deviation_bundle_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 < J) (hβ : 0 < β) (n : ℕ) (hne : 0 < (Λ.volume n).card)
    (hEpos : 0 < (inducedGraph G (Λ.volume n)).edgeFinset.card) :
    (2 : ℝ) ^ (Λ.volume n).card
        < partitionFunctionAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n ∧
    0 < Real.log (partitionFunctionAlongExhaustion G Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n)
        - ((Λ.volume n).card : ℝ) * Real.log 2 ∧
    0 < freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n - Real.log 2 :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_strict_deviation_bundle
    G Λ J β (mul_pos hβ hJ) n hne hEpos

/-- **Along-ex ferromagnetic Z strict deviation at stage `n`**. -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_pow_two_lt_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 < J) (hβ : 0 < β) (n : ℕ)
    (hEpos : 0 < (inducedGraph G (Λ.volume n)).edgeFinset.card) :
    (2 : ℝ) ^ (Λ.volume n).card
      < partitionFunctionAlongExhaustion G Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_pow_two_lt
    G Λ J β (mul_pos hβ hJ) n hEpos

/-- **Along-ex ferromagnetic log Z strict deviation at stage `n`**. -/
theorem log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_deviation_pos_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 < J) (hβ : 0 < β) (n : ℕ)
    (hEpos : 0 < (inducedGraph G (Λ.volume n)).edgeFinset.card) :
    0 < Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n)
        - ((Λ.volume n).card : ℝ) * Real.log 2 :=
  log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_deviation_pos
    G Λ J β (mul_pos hβ hJ) n hEpos

/-- **Along-ex Z ratio sandwich at stage `n`, J=0 trivial slice**. -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_sandwich
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    Real.cosh (β * J) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card
      ≤ partitionFunctionAlongExhaustion G Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n /
          partitionFunctionAlongExhaustion G Λ
            (⟨0, 0, β⟩ : IsingParams ℝ) n ∧
    partitionFunctionAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n /
        partitionFunctionAlongExhaustion G Λ
          (⟨0, 0, β⟩ : IsingParams ℝ) n
      ≤ Real.exp (β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card) := by
  change _ ≤ partitionFunctionΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ) /
      partitionFunctionΛ G (Λ.volume n) (⟨0, 0, β⟩ : IsingParams ℝ) ∧
      partitionFunctionΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ) /
        partitionFunctionΛ G (Λ.volume n) (⟨0, 0, β⟩ : IsingParams ℝ) ≤ _
  exact partitionFunctionΛ_high_temp_expansion_h_zero_ratio_sandwich
    G (Λ.volume n) J β hβJ

/-- **Along-ex Z ratio sandwich at β=0 trivial slice, stage `n`**. -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_sandwich_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    Real.cosh (β * J) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card
      ≤ partitionFunctionAlongExhaustion G Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n /
          partitionFunctionAlongExhaustion G Λ
            (⟨J, 0, 0⟩ : IsingParams ℝ) n ∧
    partitionFunctionAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n /
        partitionFunctionAlongExhaustion G Λ
          (⟨J, 0, 0⟩ : IsingParams ℝ) n
      ≤ Real.exp (β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card) := by
  change _ ≤ partitionFunctionΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ) /
      partitionFunctionΛ G (Λ.volume n) (⟨J, 0, 0⟩ : IsingParams ℝ) ∧
      partitionFunctionΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ) /
        partitionFunctionΛ G (Λ.volume n) (⟨J, 0, 0⟩ : IsingParams ℝ) ≤ _
  exact partitionFunctionΛ_high_temp_expansion_h_zero_ratio_sandwich_beta_zero
    G (Λ.volume n) J β hβJ

/-- **Along-ex Z ratio sandwich bundle at stage `n`**. -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_sandwich_bundle
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
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
      G Λ J β hβJ n,
   partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_sandwich_beta_zero
      G Λ J β hβJ n⟩

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
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_sandwich_bundle
    G Λ J β (mul_nonneg hβ.le hJ) n

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

/-- **Along-ex ferromagnetic Z ratio upper bound at J=0, stage `n`**. -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n /
        partitionFunctionAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n
      ≤ Real.exp (β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card) :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound
    G Λ J β (mul_nonneg hβ.le hJ) n

/-- **Along-ex ferromagnetic Z ratio upper bound at β=0, stage `n`**. -/
theorem
partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound_beta_zero_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n /
        partitionFunctionAlongExhaustion G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) n
      ≤ Real.exp (β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card) :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound_beta_zero
    G Λ J β (mul_nonneg hβ.le hJ) n

/-- **Along-ex Z ratio upper bound bundle at stage `n`**. -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound_bundle
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n /
        partitionFunctionAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n
        ≤ Real.exp (β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card) ∧
    partitionFunctionAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n /
        partitionFunctionAlongExhaustion G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) n
        ≤ Real.exp (β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card) :=
  ⟨partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound
      G Λ J β hβJ n,
   partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound_beta_zero
      G Λ J β hβJ n⟩

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
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound_bundle
    G Λ J β (mul_nonneg hβ.le hJ) n

/-- **Along-ex f ratio sandwich bundle at stage `n`**. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_ratio_sandwich_bundle
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    (((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) / (Λ.volume n).card *
        Real.log (Real.cosh (β * J))
        ≤ freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
            - freeEnergyAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n ∧
      freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
          - freeEnergyAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n
          ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
              (Λ.volume n).card) ∧
    (((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) / (Λ.volume n).card *
        Real.log (Real.cosh (β * J))
        ≤ freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
            - freeEnergyAlongExhaustion G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) n ∧
      freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
          - freeEnergyAlongExhaustion G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) n
          ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
              (Λ.volume n).card) := by
  change (_ ≤ freeEnergyΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
      - freeEnergyΛ G (Λ.volume n) (⟨0, 0, β⟩ : IsingParams ℝ) ∧ _) ∧
      (_ ≤ freeEnergyΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
          - freeEnergyΛ G (Λ.volume n) (⟨J, 0, 0⟩ : IsingParams ℝ) ∧ _)
  exact freeEnergyΛ_high_temp_h_zero_ratio_sandwich_bundle
    G (Λ.volume n) J β hβJ hne

/-- **Along-ex ferromagnetic f ratio sandwich bundle at stage `n`**. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_ratio_sandwich_bundle_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    (((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) / (Λ.volume n).card *
        Real.log (Real.cosh (β * J))
        ≤ freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
            - freeEnergyAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n ∧
      freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
          - freeEnergyAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n
          ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
              (Λ.volume n).card) ∧
    (((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) / (Λ.volume n).card *
        Real.log (Real.cosh (β * J))
        ≤ freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
            - freeEnergyAlongExhaustion G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) n ∧
      freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
          - freeEnergyAlongExhaustion G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) n
          ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
              (Λ.volume n).card) :=
  freeEnergyAlongExhaustion_high_temp_h_zero_ratio_sandwich_bundle
    G Λ J β (mul_nonneg hβ.le hJ) n hne

/-- **Along-ex log Z ratio sandwich bundle at stage `n`**. -/
theorem log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_sandwich_bundle
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    (((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) *
        Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunctionAlongExhaustion G Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n)
            - Real.log (partitionFunctionAlongExhaustion G Λ
                (⟨0, 0, β⟩ : IsingParams ℝ) n) ∧
      Real.log (partitionFunctionAlongExhaustion G Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n)
          - Real.log (partitionFunctionAlongExhaustion G Λ
              (⟨0, 0, β⟩ : IsingParams ℝ) n)
          ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card) ∧
    (((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) *
        Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunctionAlongExhaustion G Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n)
            - Real.log (partitionFunctionAlongExhaustion G Λ
                (⟨J, 0, 0⟩ : IsingParams ℝ) n) ∧
      Real.log (partitionFunctionAlongExhaustion G Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n)
          - Real.log (partitionFunctionAlongExhaustion G Λ
              (⟨J, 0, 0⟩ : IsingParams ℝ) n)
          ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card) := by
  change (_ ≤ Real.log (partitionFunctionΛ G (Λ.volume n)
      (⟨J, 0, β⟩ : IsingParams ℝ))
      - Real.log (partitionFunctionΛ G (Λ.volume n)
          (⟨0, 0, β⟩ : IsingParams ℝ)) ∧ _) ∧
      (_ ≤ Real.log (partitionFunctionΛ G (Λ.volume n)
          (⟨J, 0, β⟩ : IsingParams ℝ))
          - Real.log (partitionFunctionΛ G (Λ.volume n)
              (⟨J, 0, 0⟩ : IsingParams ℝ)) ∧ _)
  exact log_partitionFunctionΛ_high_temp_expansion_h_zero_ratio_sandwich_bundle
    G (Λ.volume n) J β hβJ

/-- **Along-ex ferromagnetic log Z ratio sandwich bundle at stage `n`**. -/
theorem
log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_sandwich_bundle_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    (((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) *
        Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunctionAlongExhaustion G Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n)
            - Real.log (partitionFunctionAlongExhaustion G Λ
                (⟨0, 0, β⟩ : IsingParams ℝ) n) ∧
      Real.log (partitionFunctionAlongExhaustion G Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n)
          - Real.log (partitionFunctionAlongExhaustion G Λ
              (⟨0, 0, β⟩ : IsingParams ℝ) n)
          ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card) ∧
    (((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) *
        Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunctionAlongExhaustion G Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n)
            - Real.log (partitionFunctionAlongExhaustion G Λ
                (⟨J, 0, 0⟩ : IsingParams ℝ) n) ∧
      Real.log (partitionFunctionAlongExhaustion G Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n)
          - Real.log (partitionFunctionAlongExhaustion G Λ
              (⟨J, 0, 0⟩ : IsingParams ℝ) n)
          ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card) :=
  log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_sandwich_bundle
    G Λ J β (mul_nonneg hβ.le hJ) n

/-- **Along-ex log Z ratio bound at J=0, stage `n`**. -/
theorem log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n)
        - Real.log (partitionFunctionAlongExhaustion G Λ
            (⟨0, 0, β⟩ : IsingParams ℝ) n)
      ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card := by
  change Real.log (partitionFunctionΛ G (Λ.volume n)
      (⟨J, 0, β⟩ : IsingParams ℝ))
      - Real.log (partitionFunctionΛ G (Λ.volume n)
          (⟨0, 0, β⟩ : IsingParams ℝ)) ≤ _
  exact log_partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound
    G (Λ.volume n) J β hβJ

/-- **Along-ex log Z ratio bound at β=0, stage `n`**. -/
theorem log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n)
        - Real.log (partitionFunctionAlongExhaustion G Λ
            (⟨J, 0, 0⟩ : IsingParams ℝ) n)
      ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card := by
  change Real.log (partitionFunctionΛ G (Λ.volume n)
      (⟨J, 0, β⟩ : IsingParams ℝ))
      - Real.log (partitionFunctionΛ G (Λ.volume n)
          (⟨J, 0, 0⟩ : IsingParams ℝ)) ≤ _
  exact log_partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound_beta_zero
    G (Λ.volume n) J β hβJ

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

/-- **Along-ex f ratio bound bundle at stage `n`**. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_ratio_bound_bundle
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
        - freeEnergyAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n
        ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
            (Λ.volume n).card ∧
    freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
        - freeEnergyAlongExhaustion G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) n
        ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
            (Λ.volume n).card := by
  change freeEnergyΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
      - freeEnergyΛ G (Λ.volume n) (⟨0, 0, β⟩ : IsingParams ℝ) ≤ _ ∧
      freeEnergyΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
        - freeEnergyΛ G (Λ.volume n) (⟨J, 0, 0⟩ : IsingParams ℝ) ≤ _
  exact freeEnergyΛ_high_temp_h_zero_ratio_bound_bundle
    G (Λ.volume n) J β hβJ hne

/-- **Along-ex ferromagnetic f ratio bound bundle at stage `n`**. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_ratio_bound_bundle_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
        - freeEnergyAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n
        ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
            (Λ.volume n).card ∧
    freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
        - freeEnergyAlongExhaustion G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) n
        ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
            (Λ.volume n).card :=
  freeEnergyAlongExhaustion_high_temp_h_zero_ratio_bound_bundle
    G Λ J β (mul_nonneg hβ.le hJ) n hne

/-- **Along-ex f deviation bound under `(Λ.volume n).Nonempty`**:
under `0 ≤ β·J` and `(Λ.volume n).Nonempty`,
`f_n - log 2 ≤ β·J·|E_n|/|Λ_n|`. Bridges from the Nonempty hypothesis. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_deviation_bound_exp_of_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n - Real.log 2
      ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
          (Λ.volume n).card :=
  freeEnergyAlongExhaustion_high_temp_h_zero_deviation_bound_exp
    G Λ J β hβJ n hne.card_pos

/-- **Along-ex f strict deviation under nonempty volume**. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_deviation_pos_of_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 < β * J) (n : ℕ) (hne : (Λ.volume n).Nonempty)
    (hEpos : 0 < (inducedGraph G (Λ.volume n)).edgeFinset.card) :
    0 < freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n - Real.log 2 :=
  freeEnergyAlongExhaustion_high_temp_h_zero_deviation_pos
    G Λ J β hβJ n hne.card_pos hEpos

/-- **Along-ex Z strict deviation under nonempty volume**. -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_pow_two_lt_of_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 < β * J) (n : ℕ)
    (hEpos : 0 < (inducedGraph G (Λ.volume n)).edgeFinset.card) :
    (2 : ℝ) ^ (Λ.volume n).card
      < partitionFunctionAlongExhaustion G Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_pow_two_lt
    G Λ J β hβJ n hEpos

/-- **Along-ex f ratio bound at J=0**. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_ratio_bound
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
        - freeEnergyAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n
      ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
          (Λ.volume n).card := by
  change freeEnergyΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
      - freeEnergyΛ G (Λ.volume n) (⟨0, 0, β⟩ : IsingParams ℝ) ≤ _
  exact freeEnergyΛ_high_temp_h_zero_ratio_bound G (Λ.volume n) J β hβJ hne

/-- **Along-ex f ratio bound at β=0**. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_ratio_bound_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
        - freeEnergyAlongExhaustion G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) n
      ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
          (Λ.volume n).card := by
  change freeEnergyΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
      - freeEnergyΛ G (Λ.volume n) (⟨J, 0, 0⟩ : IsingParams ℝ) ≤ _
  exact freeEnergyΛ_high_temp_h_zero_ratio_bound_beta_zero
    G (Λ.volume n) J β hβJ hne

/-- **Along-ex ferromagnetic f ratio bound at J=0**. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_ratio_bound_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ)
    (hne : 0 < (Λ.volume n).card) :
    freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
        - freeEnergyAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n
      ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
          (Λ.volume n).card :=
  freeEnergyAlongExhaustion_high_temp_h_zero_ratio_bound
    G Λ J β (mul_nonneg hβ.le hJ) n hne

/-- **Along-ex ferromagnetic f ratio bound at β=0**. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_ratio_bound_beta_zero_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ)
    (hne : 0 < (Λ.volume n).card) :
    freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
        - freeEnergyAlongExhaustion G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) n
      ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
          (Λ.volume n).card :=
  freeEnergyAlongExhaustion_high_temp_h_zero_ratio_bound_beta_zero
    G Λ J β (mul_nonneg hβ.le hJ) n hne

/-- **Along-ex triple (Z + log Z + f) ratio sandwich bundle at J=0, stage `n`**. -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_triple_ratio_sandwich_bundle
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    (Real.cosh (β * J) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card
        ≤ partitionFunctionAlongExhaustion G Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n /
            partitionFunctionAlongExhaustion G Λ
              (⟨0, 0, β⟩ : IsingParams ℝ) n ∧
      partitionFunctionAlongExhaustion G Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n /
          partitionFunctionAlongExhaustion G Λ
            (⟨0, 0, β⟩ : IsingParams ℝ) n
          ≤ Real.exp (β * J *
              (inducedGraph G (Λ.volume n)).edgeFinset.card)) ∧
    (((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) *
        Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunctionAlongExhaustion G Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n)
            - Real.log (partitionFunctionAlongExhaustion G Λ
                (⟨0, 0, β⟩ : IsingParams ℝ) n) ∧
      Real.log (partitionFunctionAlongExhaustion G Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n)
          - Real.log (partitionFunctionAlongExhaustion G Λ
              (⟨0, 0, β⟩ : IsingParams ℝ) n)
          ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card) ∧
    (((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
        (Λ.volume n).card * Real.log (Real.cosh (β * J))
        ≤ freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
            - freeEnergyAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n ∧
      freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
          - freeEnergyAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n
          ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
              (Λ.volume n).card) :=
  ⟨(partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_sandwich_bundle
      G Λ J β hβJ n).1,
   (log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_sandwich_bundle
      G Λ J β hβJ n).1,
   (freeEnergyAlongExhaustion_high_temp_h_zero_ratio_sandwich_bundle
      G Λ J β hβJ n hne).1⟩

/-- **Along-ex triple ratio sandwich bundle at β=0, stage `n`**. -/
theorem
partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_triple_ratio_sandwich_bundle_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    (Real.cosh (β * J) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card
        ≤ partitionFunctionAlongExhaustion G Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n /
            partitionFunctionAlongExhaustion G Λ
              (⟨J, 0, 0⟩ : IsingParams ℝ) n ∧
      partitionFunctionAlongExhaustion G Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n /
          partitionFunctionAlongExhaustion G Λ
            (⟨J, 0, 0⟩ : IsingParams ℝ) n
          ≤ Real.exp (β * J *
              (inducedGraph G (Λ.volume n)).edgeFinset.card)) ∧
    (((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) *
        Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunctionAlongExhaustion G Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n)
            - Real.log (partitionFunctionAlongExhaustion G Λ
                (⟨J, 0, 0⟩ : IsingParams ℝ) n) ∧
      Real.log (partitionFunctionAlongExhaustion G Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n)
          - Real.log (partitionFunctionAlongExhaustion G Λ
              (⟨J, 0, 0⟩ : IsingParams ℝ) n)
          ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card) ∧
    (((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
        (Λ.volume n).card * Real.log (Real.cosh (β * J))
        ≤ freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
            - freeEnergyAlongExhaustion G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) n ∧
      freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
          - freeEnergyAlongExhaustion G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) n
          ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
              (Λ.volume n).card) :=
  ⟨(partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_sandwich_bundle
      G Λ J β hβJ n).2,
   (log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_sandwich_bundle
      G Λ J β hβJ n).2,
   (freeEnergyAlongExhaustion_high_temp_h_zero_ratio_sandwich_bundle
      G Λ J β hβJ n hne).2⟩

/-- **Along-ex ferromagnetic triple ratio sandwich bundle at β=0, stage `n`**. -/
theorem partitionFunctionAlongExhaustion_h_zero_triple_ratio_sandwich_bundle_beta_zero_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    (Real.cosh (β * J) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card
        ≤ partitionFunctionAlongExhaustion G Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n /
            partitionFunctionAlongExhaustion G Λ
              (⟨J, 0, 0⟩ : IsingParams ℝ) n ∧
      partitionFunctionAlongExhaustion G Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n /
          partitionFunctionAlongExhaustion G Λ
            (⟨J, 0, 0⟩ : IsingParams ℝ) n
          ≤ Real.exp (β * J *
              (inducedGraph G (Λ.volume n)).edgeFinset.card)) ∧
    (((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) *
        Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunctionAlongExhaustion G Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n)
            - Real.log (partitionFunctionAlongExhaustion G Λ
                (⟨J, 0, 0⟩ : IsingParams ℝ) n) ∧
      Real.log (partitionFunctionAlongExhaustion G Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n)
          - Real.log (partitionFunctionAlongExhaustion G Λ
              (⟨J, 0, 0⟩ : IsingParams ℝ) n)
          ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card) ∧
    (((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
        (Λ.volume n).card * Real.log (Real.cosh (β * J))
        ≤ freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
            - freeEnergyAlongExhaustion G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) n ∧
      freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
          - freeEnergyAlongExhaustion G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) n
          ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
              (Λ.volume n).card) :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_triple_ratio_sandwich_bundle_beta_zero
    G Λ J β (mul_nonneg hβ.le hJ) n hne

/-- **Along-ex ferromagnetic triple ratio sandwich bundle at J=0, stage `n`**. -/
theorem partitionFunctionAlongExhaustion_h_zero_triple_ratio_sandwich_bundle_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    (Real.cosh (β * J) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card
        ≤ partitionFunctionAlongExhaustion G Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n /
            partitionFunctionAlongExhaustion G Λ
              (⟨0, 0, β⟩ : IsingParams ℝ) n ∧
      partitionFunctionAlongExhaustion G Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n /
          partitionFunctionAlongExhaustion G Λ
            (⟨0, 0, β⟩ : IsingParams ℝ) n
          ≤ Real.exp (β * J *
              (inducedGraph G (Λ.volume n)).edgeFinset.card)) ∧
    (((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) *
        Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunctionAlongExhaustion G Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n)
            - Real.log (partitionFunctionAlongExhaustion G Λ
                (⟨0, 0, β⟩ : IsingParams ℝ) n) ∧
      Real.log (partitionFunctionAlongExhaustion G Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n)
          - Real.log (partitionFunctionAlongExhaustion G Λ
              (⟨0, 0, β⟩ : IsingParams ℝ) n)
          ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card) ∧
    (((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
        (Λ.volume n).card * Real.log (Real.cosh (β * J))
        ≤ freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
            - freeEnergyAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n ∧
      freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
          - freeEnergyAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n
          ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
              (Λ.volume n).card) :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_triple_ratio_sandwich_bundle
    G Λ J β (mul_nonneg hβ.le hJ) n hne

/-- **Along-ex triple (Z + log Z + f) ratio bound bundle at J=0, stage `n`**. -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_triple_ratio_bound_bundle
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    partitionFunctionAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n /
        partitionFunctionAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n
        ≤ Real.exp (β * J *
            (inducedGraph G (Λ.volume n)).edgeFinset.card) ∧
    Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n)
        - Real.log (partitionFunctionAlongExhaustion G Λ
            (⟨0, 0, β⟩ : IsingParams ℝ) n)
        ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card ∧
    freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
        - freeEnergyAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n
        ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
            (Λ.volume n).card :=
  ⟨partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound
     G Λ J β hβJ n,
   log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound
     G Λ J β hβJ n,
   freeEnergyAlongExhaustion_high_temp_h_zero_ratio_bound G Λ J β hβJ n hne⟩

/-- **Along-ex triple ratio bound bundle at β=0, stage `n`**. -/
theorem
partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_triple_ratio_bound_bundle_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    partitionFunctionAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n /
        partitionFunctionAlongExhaustion G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) n
        ≤ Real.exp (β * J *
            (inducedGraph G (Λ.volume n)).edgeFinset.card) ∧
    Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n)
        - Real.log (partitionFunctionAlongExhaustion G Λ
            (⟨J, 0, 0⟩ : IsingParams ℝ) n)
        ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card ∧
    freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
        - freeEnergyAlongExhaustion G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) n
        ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
            (Λ.volume n).card :=
  ⟨partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound_beta_zero
     G Λ J β hβJ n,
   log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound_beta_zero
     G Λ J β hβJ n,
   freeEnergyAlongExhaustion_high_temp_h_zero_ratio_bound_beta_zero
     G Λ J β hβJ n hne⟩

/-- **Along-ex ferromagnetic triple ratio bound bundle at J=0, stage `n`**. -/
theorem
partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_triple_ratio_bound_bundle_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    partitionFunctionAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n /
        partitionFunctionAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n
        ≤ Real.exp (β * J *
            (inducedGraph G (Λ.volume n)).edgeFinset.card) ∧
    Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n)
        - Real.log (partitionFunctionAlongExhaustion G Λ
            (⟨0, 0, β⟩ : IsingParams ℝ) n)
        ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card ∧
    freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
        - freeEnergyAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n
        ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
            (Λ.volume n).card :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_triple_ratio_bound_bundle
    G Λ J β (mul_nonneg hβ.le hJ) n hne

/-- **Along-exhaustion freeEnergy high-temp sandwich (FV (3.45))**: under
`0 ≤ β·J` and `0 < |Λ_n|`, at every stage `n`,
`log 2 + (|E_n|/|Λ_n|) log cosh(βJ) ≤ f_n ≤ log 2 + (|E_n|/|Λ_n|) log(2·cosh βJ)`. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_sandwich
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    Real.log 2 +
        ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
          (Λ.volume n).card * Real.log (Real.cosh (β * J))
      ≤ freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
    ∧ freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
      ≤ Real.log 2
        + ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
            (Λ.volume n).card * Real.log (2 * Real.cosh (β * J)) :=
  ⟨freeEnergyAlongExhaustion_high_temp_h_zero_lower_bound G Λ J β hβJ n hne,
   freeEnergyAlongExhaustion_high_temp_h_zero_upper_bound G Λ J β hβJ n hne⟩

/-- **Along-exhaustion FV (3.46) numerator filter empty for odd `|A|`**:
at every stage `n`, for any `A : Finset ↑(Λ.volume n)` of odd cardinality,
the FV (3.46) numerator filter set is *literally empty*.
Per-stage application of `high_temp_numerator_filter_eq_empty_of_odd_card_Λ`
(Step 299), via the edge-vertex handshake. -/
theorem high_temp_numerator_filter_eq_empty_of_odd_card_alongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (n : ℕ) (A : Finset ↑(Λ.volume n)) (hA_odd : Odd A.card) :
    (inducedGraph G (Λ.volume n)).edgeFinset.powerset.filter
        (fun X : Finset (Sym2 ↑(Λ.volume n)) => ∀ v : ↑(Λ.volume n),
          Even ((if v ∈ A then (1 : ℕ) else 0)
                + (X.filter (v ∈ ·)).card)) = ∅ :=
  high_temp_numerator_filter_eq_empty_of_odd_card_Λ G (Λ.volume n) A hA_odd

/-- **Along-exhaustion correlation Z₂ symmetry at h = 0 (GJ §18.3)**:
for any ambient `A : Finset V` with odd cardinality, at every stage `n`
where `A ⊆ Λ.volume n`, the per-stage correlation
`correlationAlongExhaustion G Λ ⟨J, 0, β⟩ A n = 0`.

When `A ⊄ Λ.volume n`, `correlationAlongExhaustion` is `0` by definition,
trivially satisfying the equation. When `A ⊆ Λ.volume n`, lift via
`liftFinset` (preserves cardinality) and apply
`correlationΛ_high_temp_h_zero_odd_card_eq_zero` (Step 299). -/
theorem correlationAlongExhaustion_high_temp_h_zero_odd_card_eq_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (A : Finset V) (hA_odd : Odd A.card) (n : ℕ) :
    correlationAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) A n = 0 := by
  unfold correlationAlongExhaustion
  by_cases hAn : A ⊆ Λ.volume n
  · simp only [dif_pos hAn]
    have hcard : (liftFinset A hAn).card = A.card := liftFinset_card hAn
    refine correlationΛ_high_temp_h_zero_odd_card_eq_zero G (Λ.volume n) J β
      (liftFinset A hAn) ?_
    rw [hcard]; exact hA_odd
  · simp only [dif_neg hAn]

/-- **Along-exhaustion FV (3.46) at A = ∅ consistency check**:
under `0 ≤ β·J`, at every stage `n`,
`correlationAlongExhaustion G Λ ⟨J, 0, β⟩ ∅ n = 1`.
The empty Finset is always a subset of `Λ.volume n`, so we lift via
`liftFinset`, then apply `correlationΛ_high_temp_h_zero_at_empty_A` (Step 314). -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_empty_A
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    correlationAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) (∅ : Finset V) n = 1 := by
  unfold correlationAlongExhaustion
  rw [dif_pos (Finset.empty_subset _)]
  have h_lift : liftFinset (∅ : Finset V) (Finset.empty_subset (Λ.volume n))
      = (∅ : Finset ↑(Λ.volume n)) := by
    ext v; simp [liftFinset]
  rw [h_lift]
  exact correlationΛ_high_temp_h_zero_at_empty_A G (Λ.volume n) J β hβJ

/-- **Along-ex pair correlation ≤ 1 at h = 0**: at every stage `n`,
`correlationAlongExhaustion G Λ ⟨J, 0, β⟩ {i, j} n ≤ 1`. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_pair_le_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (i j : V) (n : ℕ) :
    correlationAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset V) n ≤ 1 := by
  unfold correlationAlongExhaustion
  by_cases hAn : ({i, j} : Finset V) ⊆ Λ.volume n
  · rw [dif_pos hAn]
    exact correlationΛ_le_one G (Λ.volume n) _ _
  · rw [dif_neg hAn]; exact zero_le_one

/-- **Along-exhaustion pair correlation nonneg at h = 0**:
under `0 ≤ β·J`, at every stage `n`,
`0 ≤ correlationAlongExhaustion G Λ ⟨J, 0, β⟩ {i, j} n`. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_pair_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (i j : V) (n : ℕ) :
    0 ≤ correlationAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset V) n :=
  correlationAlongExhaustion_high_temp_h_zero_nonneg G Λ J β hβJ {i, j} n

/-- **Along-ex pair sandwich at h = 0**: under `0 ≤ β·J`,
`0 ≤ correlationAlongExhaustion G Λ ⟨J, 0, β⟩ {i, j} n ≤ 1`. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_pair_sandwich
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (i j : V) (n : ℕ) :
    0 ≤ correlationAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset V) n ∧
      correlationAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset V) n ≤ 1 :=
  ⟨correlationAlongExhaustion_high_temp_h_zero_at_pair_nonneg G Λ J β hβJ i j n,
   correlationAlongExhaustion_high_temp_h_zero_at_pair_le_one G Λ J β i j n⟩

/-- **Along-ex pair ferromagnetic sandwich at h = 0**: under `0 ≤ J, 0 < β`,
`0 ≤ correlationAlongExhaustion ⟨J,0,β⟩ {i,j} n ≤ 1`. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_pair_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (i j : V) (n : ℕ) :
    0 ≤ correlationAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset V) n ∧
      correlationAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset V) n ≤ 1 :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_sandwich
    G Λ J β (mul_nonneg hβ.le hJ) i j n

/-- **Along-ex pair at J=0,h=0 vanishes**: at every stage `n`,
`correlationAlongExhaustion G Λ ⟨0, 0, β⟩ {i, j} n = 0`. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_pair_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (i j : V) (n : ℕ) :
    correlationAlongExhaustion G Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset V) n = 0 := by
  unfold correlationAlongExhaustion
  by_cases hAn : ({i, j} : Finset V) ⊆ Λ.volume n
  · rw [dif_pos hAn, correlationΛ_J_zero, mul_zero, Real.tanh_zero]
    have hcard_pos : 0 < (liftFinset ({i, j} : Finset V) hAn).card := by
      rw [liftFinset_card]
      exact Finset.card_pos.mpr ⟨i, by simp⟩
    exact zero_pow hcard_pos.ne'
  · rw [dif_neg hAn]

/-- **Along-ex pair at β=0,h=0 vanishes**: at every stage `n`,
`correlationAlongExhaustion G Λ ⟨J, 0, 0⟩ {i, j} n = 0`. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_pair_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) (i j : V) (n : ℕ) :
    correlationAlongExhaustion G Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ) ({i, j} : Finset V) n = 0 := by
  unfold correlationAlongExhaustion
  by_cases hAn : ({i, j} : Finset V) ⊆ Λ.volume n
  · rw [dif_pos hAn]
    apply IsingModel.correlation_beta_zero_vanish_of_nonempty_A
    have : (liftFinset ({i, j} : Finset V) hAn).card ≥ 1 := by
      rw [liftFinset_card]
      exact Finset.card_pos.mpr ⟨i, by simp⟩
    exact Finset.card_pos.mp this
  · rw [dif_neg hAn]

/-- **Along-ex singleton at J=0,h=0 vanishes**. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_singleton_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (i : V) (n : ℕ) :
    correlationAlongExhaustion G Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) ({i} : Finset V) n = 0 := by
  refine correlationAlongExhaustion_high_temp_h_zero_odd_card_eq_zero
    G Λ 0 β {i} ?_ n
  rw [Finset.card_singleton]; exact ⟨0, rfl⟩

/-- **Along-ex singleton at β=0,h=0 vanishes**. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_singleton_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) (i : V) (n : ℕ) :
    correlationAlongExhaustion G Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ) ({i} : Finset V) n = 0 := by
  unfold correlationAlongExhaustion
  by_cases hAn : ({i} : Finset V) ⊆ Λ.volume n
  · rw [dif_pos hAn]
    exact correlationΛ_high_temp_h_zero_at_singleton_beta_zero
      G (Λ.volume n) J ⟨i, hAn (by simp)⟩
  · rw [dif_neg hAn]

/-- **Along-exhaustion magnetization vanishes at h = 0**: at every stage `n`,
`correlationAlongExhaustion G Λ ⟨J, 0, β⟩ {i} n = 0` for any
ambient site `i : V`. Specialization at `A = {i}`. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_singleton
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (i : V) (n : ℕ) :
    correlationAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset V) n = 0 := by
  refine correlationAlongExhaustion_high_temp_h_zero_odd_card_eq_zero
    G Λ J β {i} ?_ n
  rw [Finset.card_singleton]; exact ⟨0, rfl⟩

/-- **Along-ex singleton sandwich at h = 0**: `= 0 ∧ ≤ 1`. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_singleton_eq_zero_le_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (i : V) (n : ℕ) :
    correlationAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset V) n = 0 ∧
      correlationAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset V) n ≤ 1 :=
  ⟨correlationAlongExhaustion_high_temp_h_zero_at_singleton G Λ J β i n,
   (correlationAlongExhaustion_high_temp_h_zero_at_singleton G Λ J β i n).symm
      ▸ zero_le_one⟩

/-- **Along-ex pair+singleton bundle at h=0**. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_pair_singleton_bundle
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (i j : V) (n : ℕ) :
    correlationAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset V) n = 0 ∧
      0 ≤ correlationAlongExhaustion G Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset V) n ∧
      correlationAlongExhaustion G Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset V) n ≤ 1 :=
  ⟨correlationAlongExhaustion_high_temp_h_zero_at_singleton G Λ J β i n,
   correlationAlongExhaustion_high_temp_h_zero_at_pair_nonneg G Λ J β hβJ i j n,
   correlationAlongExhaustion_high_temp_h_zero_at_pair_le_one G Λ J β i j n⟩

/-- **Along-ex pair + singleton complete-summary bundle at h = 0**:
under `0 ≤ β·J`, at every stage `n` packages pair upper bound, pair
sandwich lower, singleton vanishing, and pair vanishing at `J = 0` /
`β = 0` trivial slices. Along-exhaustion wrapper of
`correlation_high_temp_h_zero_at_pair_singleton_complete_summary`. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_pair_singleton_complete_summary
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (i j : V) (n : ℕ) :
    correlationAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset V) n ≤ 1 ∧
      0 ≤ correlationAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset V) n ∧
      correlationAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset V) n = 0 ∧
      correlationAlongExhaustion G Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset V) n = 0 ∧
      correlationAlongExhaustion G Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ) ({i, j} : Finset V) n = 0 :=
  ⟨correlationAlongExhaustion_high_temp_h_zero_at_pair_le_one G Λ J β i j n,
   correlationAlongExhaustion_high_temp_h_zero_at_pair_nonneg G Λ J β hβJ i j n,
   correlationAlongExhaustion_high_temp_h_zero_at_singleton G Λ J β i n,
   correlationAlongExhaustion_high_temp_h_zero_at_pair_J_zero G Λ β i j n,
   correlationAlongExhaustion_high_temp_h_zero_at_pair_beta_zero G Λ J i j n⟩

/-- **Along-ex pair + singleton trivial-slices full bundle at h = 0**:
at `J = 0` and `β = 0`, both pair and singleton correlations vanish at
every stage `n`. Along-exhaustion wrapper of
`correlation_high_temp_h_zero_at_pair_singleton_trivial_slices_bundle`. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_pair_singleton_trivial_slices_bundle
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (i j : V) (n : ℕ) :
    correlationAlongExhaustion G Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) ({i} : Finset V) n = 0 ∧
      correlationAlongExhaustion G Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ) ({i} : Finset V) n = 0 ∧
      correlationAlongExhaustion G Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset V) n = 0 ∧
      correlationAlongExhaustion G Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ) ({i, j} : Finset V) n = 0 :=
  ⟨correlationAlongExhaustion_high_temp_h_zero_at_singleton_J_zero G Λ β i n,
   correlationAlongExhaustion_high_temp_h_zero_at_singleton_beta_zero G Λ J i n,
   correlationAlongExhaustion_high_temp_h_zero_at_pair_J_zero G Λ β i j n,
   correlationAlongExhaustion_high_temp_h_zero_at_pair_beta_zero G Λ J i j n⟩

/-- **Along-ex pair+singleton bundle under ferromagnetic at h = 0**:
under `0 ≤ J, 0 < β`, packages `⟨σ_i⟩ = 0`, `0 ≤ ⟨σ_iσ_j⟩`, and
`⟨σ_iσ_j⟩ ≤ 1` at every stage `n`. Along-exhaustion wrapper of
`correlation_high_temp_h_zero_at_pair_singleton_bundle_ferromagnetic`. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_pair_singleton_bundle_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (i j : V) (n : ℕ) :
    correlationAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset V) n = 0 ∧
      0 ≤ correlationAlongExhaustion G Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset V) n ∧
      correlationAlongExhaustion G Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset V) n ≤ 1 :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_singleton_bundle
    G Λ J β (mul_nonneg hβ.le hJ) i j n

/-- **Along-ex pair correlation single-edge tanh lower bound at stage `n` (GJ §18.3 / FV (3.46))**:
applies the Λ-level single-edge lower bound at the stage-`n`
subtype `↑(Λ.volume n)`. Along-exhaustion wrapper for
`correlationΛ_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges`. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ)
    (i j : ↑(Λ.volume n)) (hij : i ≠ j)
    (he : s(i, j) ∈ (inducedGraph G (Λ.volume n)).edgeSet) :
    Real.tanh (β * J) /
        (2 : ℝ) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card
      ≤ correlationΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
          ({i, j} : Finset ↑(Λ.volume n)) :=
  correlationΛ_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges
    G (Λ.volume n) J β hβJ i j hij he

/-- **Along-ex §18.7 capstone: high-temperature exponential decay of
the pair correlation in graph distance, at stage `n`**. Under
`0 ≤ β·J`, for `i, j : ↑(Λ.volume n)`,
`⟨σ_iσ_j⟩^{Λ_n}_{β,0} ≤ 2^{|E_{Λ_n}|} ·
    tanh(β·J)^{(inducedGraph G (Λ.volume n)).dist i j}`.
Stage-`n` Λ-level specialization of
`correlationΛ_high_temp_h_zero_at_pair_le_two_pow_edges_mul_tanh_pow_dist`. -/
theorem
correlationAlongExhaustion_high_temp_h_zero_at_pair_le_two_pow_edges_mul_tanh_pow_dist
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) (i j : ↑(Λ.volume n)) :
    correlationΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
        ({i, j} : Finset ↑(Λ.volume n))
      ≤ (2 : ℝ) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.tanh (β * J) ^ (inducedGraph G (Λ.volume n)).dist i j :=
  correlationΛ_high_temp_h_zero_at_pair_le_two_pow_edges_mul_tanh_pow_dist
    G (Λ.volume n) J β hβJ i j

/-- **Along-ex §18.7 ferromagnetic capstone**: under `0 ≤ J, 0 < β`,
the same exponential-decay bound at stage `n`. -/
theorem
correlationAlongExhaustion_high_temp_h_zero_at_pair_le_two_pow_edges_mul_tanh_pow_dist_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) (i j : ↑(Λ.volume n)) :
    correlationΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
        ({i, j} : Finset ↑(Λ.volume n))
      ≤ (2 : ℝ) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.tanh (β * J) ^ (inducedGraph G (Λ.volume n)).dist i j :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_le_two_pow_edges_mul_tanh_pow_dist
    G Λ J β (mul_nonneg hβ.le hJ) n i j

/-- **Along-ex §18.7 rate-form capstone at stage `n`**: under
`0 ≤ β·J`, the pair-correlation distance bound at `Λ.volume n` is
written with the explicit decay rate `-log(tanh(β·J))`. -/
theorem
correlationAlongExhaustion_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_rate_dist
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) (i j : ↑(Λ.volume n)) :
    correlationΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
        ({i, j} : Finset ↑(Λ.volume n))
      ≤ (2 : ℝ) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.exp (-(-Real.log (Real.tanh (β * J))) *
          ((inducedGraph G (Λ.volume n)).dist i j : ℝ)) :=
  correlationΛ_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_rate_dist
    G (Λ.volume n) J β hβJ i j

/-- **Along-ex ferromagnetic §18.7 rate-form capstone at stage `n`**:
under `0 ≤ J, 0 < β`, the same explicit-rate pair-correlation bound
holds at `Λ.volume n`. -/
theorem
correlationAlongExhaustion_high_temp_h_zero_at_pair_le_exp_rate_dist_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) (i j : ↑(Λ.volume n)) :
    correlationΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
        ({i, j} : Finset ↑(Λ.volume n))
      ≤ (2 : ℝ) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.exp (-(-Real.log (Real.tanh (β * J))) *
          ((inducedGraph G (Λ.volume n)).dist i j : ℝ)) :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_rate_dist
    G Λ J β (mul_nonneg hβ.le hJ) n i j

/-- **Along-ex §18.7 named-rate capstone at stage `n`**: the stage-`n`
pair-correlation distance bound written with `highTempExpRate`. -/
theorem
correlationAlongExhaustion_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_highTempExpRate_dist
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ)
    (i j : ↑(Λ.volume n)) :
    correlationΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
        ({i, j} : Finset ↑(Λ.volume n))
      ≤ (2 : ℝ) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.exp (-(highTempExpRate β J) *
          ((inducedGraph G (Λ.volume n)).dist i j : ℝ)) :=
  correlationΛ_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_highTempExpRate_dist
    G (Λ.volume n) J β hβJ i j

/-- **Along-ex §18.7 monotone-rate capstone at stage `n`**: any
`α ≤ -log(tanh(β·J))` may replace the exact high-temperature rate in the
pair-correlation distance bound at `Λ.volume n`. -/
theorem
correlationAlongExhaustion_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_alpha_dist
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β α : ℝ) (hβJ : 0 ≤ β * J)
    (hα : α ≤ -Real.log (Real.tanh (β * J))) (n : ℕ)
    (i j : ↑(Λ.volume n)) :
    correlationΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
        ({i, j} : Finset ↑(Λ.volume n))
      ≤ (2 : ℝ) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.exp (-α * ((inducedGraph G (Λ.volume n)).dist i j : ℝ)) :=
  correlationΛ_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_alpha_dist
    G (Λ.volume n) J β α hβJ hα i j

/-- **Along-ex §18.7 named monotone-rate capstone at stage `n`**:
any `α ≤ highTempExpRate β J` gives the stage-`n` pair-correlation
distance bound with rate `α`. -/
theorem
correlationAlongExhaustion_high_temp_h_zero_at_pair_le_exp_alpha_dist_of_le_highTempExpRate
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β α : ℝ) (hβJ : 0 ≤ β * J)
    (hα : α ≤ highTempExpRate β J) (n : ℕ)
    (i j : ↑(Λ.volume n)) :
    correlationΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
        ({i, j} : Finset ↑(Λ.volume n))
      ≤ (2 : ℝ) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.exp (-α * ((inducedGraph G (Λ.volume n)).dist i j : ℝ)) :=
  correlationΛ_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_alpha_dist_of_le_highTempExpRate
    G (Λ.volume n) J β α hβJ hα i j

/-- **Along-ex ferromagnetic §18.7 monotone-rate capstone at stage `n`**:
under `0 ≤ J, 0 < β`, any `α ≤ -log(tanh(β·J))` gives the stage-`n`
pair-correlation distance bound with rate `α`. -/
theorem
correlationAlongExhaustion_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_alpha_dist_ferro
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β α : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    (hα : α ≤ -Real.log (Real.tanh (β * J))) (n : ℕ)
    (i j : ↑(Λ.volume n)) :
    correlationΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
        ({i, j} : Finset ↑(Λ.volume n))
      ≤ (2 : ℝ) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.exp (-α * ((inducedGraph G (Λ.volume n)).dist i j : ℝ)) :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_alpha_dist
    G Λ J β α (mul_nonneg hβ.le hJ) hα n i j

/-- **Along-ex pair correlation strict positivity under edge at stage `n` (GJ §18.3 / FV (3.46))**:
under `0 < β·J` and an edge in the stage-`n` induced subgraph,
`0 < ⟨σ_iσ_j⟩^{Λ_n}`. Stage-`n` Λ-level specialization of
`correlation_high_temp_h_zero_at_pair_pos_of_edge`. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_pair_pos_of_edge
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 < β * J) (n : ℕ)
    (i j : ↑(Λ.volume n)) (hij : i ≠ j)
    (he : s(i, j) ∈ (inducedGraph G (Λ.volume n)).edgeSet) :
    0 < correlationΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
        ({i, j} : Finset ↑(Λ.volume n)) :=
  correlationΛ_high_temp_h_zero_at_pair_pos_of_edge
    G (Λ.volume n) J β hβJ i j hij he

/-- **Along-ex ferromagnetic pair single-edge tanh lower bound at stage `n`**:
under `0 ≤ J, 0 < β` and an edge in the stage-`n` induced subgraph,
`⟨σ_iσ_j⟩^{Λ_n} ≥ tanh(β·J) / 2^|E_{Λ_n}|`. Stage-`n` Λ-level
specialization of
`correlation_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges_ferromagnetic`. -/
theorem
    correlationAlongExhaustion_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ)
    (i j : ↑(Λ.volume n)) (hij : i ≠ j)
    (he : s(i, j) ∈ (inducedGraph G (Λ.volume n)).edgeSet) :
    Real.tanh (β * J) /
        (2 : ℝ) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card
      ≤ correlationΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
          ({i, j} : Finset ↑(Λ.volume n)) :=
  correlationΛ_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges_ferromagnetic
    G (Λ.volume n) J β hJ hβ i j hij he

/-- **Along-ex ferromagnetic pair strict positivity under edge at stage `n`**:
under `0 < J, 0 < β` and an edge in the stage-`n` induced subgraph,
`0 < ⟨σ_iσ_j⟩^{Λ_n}`. Stage-`n` Λ-level specialization of
`correlation_high_temp_h_zero_at_pair_pos_of_edge_ferromagnetic`. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_pair_pos_of_edge_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 < J) (hβ : 0 < β) (n : ℕ)
    (i j : ↑(Λ.volume n)) (hij : i ≠ j)
    (he : s(i, j) ∈ (inducedGraph G (Λ.volume n)).edgeSet) :
    0 < correlationΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
        ({i, j} : Finset ↑(Λ.volume n)) :=
  correlationΛ_high_temp_h_zero_at_pair_pos_of_edge_ferromagnetic
    G (Λ.volume n) J β hJ hβ i j hij he

/-- **Along-ex singleton ferromagnetic vanish at h = 0**: under
`0 ≤ J, 0 < β`, `correlationAlongExhaustion G Λ ⟨J, 0, β⟩ {i} n = 0`. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_singleton_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (_hJ : 0 ≤ J) (_hβ : 0 < β) (i : V) (n : ℕ) :
    correlationAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset V) n = 0 :=
  correlationAlongExhaustion_high_temp_h_zero_at_singleton G Λ J β i n

end Ambient
end IsingModel

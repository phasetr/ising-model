import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansion
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansionLowerUpper

/-!
# Ambient alongExhaustion sharper-exp Z/f/log Z wrappers at h = 0

Narrow child module for the §18.3-§18.4 ambient alongExhaustion
sharper-exp upper-bound / sandwich / complete-summary wrappers. 16
theorems for `partitionFunctionAlongExhaustion`,
`freeEnergyAlongExhaustion`, and `log_partitionFunctionAlongExhaustion`
high-temperature wrappers with `_exp` suffix at `h = 0` plus
ferromagnetic variants. The theorem names are unchanged from the former
`HighTemperatureBounds` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]


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

/-! ## Moved: complete_summary_exp wrappers

The 6 ambient alongExhaustion `complete_summary_exp` wrappers
(`freeEnergyAlongExhaustion`, `partitionFunctionAlongExhaustion`,
`log_partitionFunctionAlongExhaustion` with ferromagnetic variants)
now live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharperComplete`.
The legacy import path is preserved by re-importing the new child
via the umbrella.
-/

end Ambient

end IsingModel

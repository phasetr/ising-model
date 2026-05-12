import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansion
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharper

/-!
# Ambient alongExhaustion f/Z/log Z deviation / continuity wrappers at h = 0

Narrow child module for the §18.3-§18.4 ambient alongExhaustion
deviation_bound_exp / continuity_bundle / deviation_sandwich /
relative_sandwich / deviation_pos / pow_two_lt /
strict_deviation_bundle wrappers. 20 theorems for
`freeEnergyAlongExhaustion`, `partitionFunctionAlongExhaustion`, and
`log_partitionFunctionAlongExhaustion` plus ferromagnetic variants. The
theorem names are unchanged from the former `HighTemperatureBounds`
declarations.
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

/-! ## Moved: strict-deviation wrappers

The 10 ambient alongExhaustion strict-deviation wrappers covering
`*_relative_sandwich`, `*_deviation_pos`, `*_pow_two_lt`,
`log_partitionFunctionAlongExhaustion_*_deviation_pos`, and
`_strict_deviation_bundle` (with ferromagnetic variants) now live
in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviationStrict`.
The legacy import path is preserved by re-importing the new child
via the umbrella.
-/

end Ambient

end IsingModel

import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviationStrict

/-!
# Ambient alongExhaustion ferromagnetic strict-deviation + bundle wrappers at h = 0

Narrow child module for six §18.3-§18.4 ambient alongExhaustion
strict-deviation wrappers: the four ferromagnetic variants
(`_relative_sandwich_ferromagnetic`, `_deviation_pos_ferromagnetic`,
`_pow_two_lt_ferromagnetic`, `log_*_deviation_pos_ferromagnetic`)
and the two strict-deviation bundles
(`_strict_deviation_bundle`, `_strict_deviation_bundle_ferromagnetic`).
Theorem names are unchanged from the former
`HighTemperatureBoundsDeviationStrict` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

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

end Ambient

end IsingModel

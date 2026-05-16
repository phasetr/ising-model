import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansion
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansionLowerUpper
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharper

/-!
# Ambient alongExhaustion ferromagnetic sharper-exp sandwich wrappers at h = 0

Narrow child module for the two §18.3-§18.4 ambient alongExhaustion
ferromagnetic sharper-exp `_sandwich_exp_ferromagnetic` wrappers
extracted from `HighTemperatureBoundsExpSharperSandwich.lean`:

* `partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_sandwich_exp_ferromagnetic`
* `freeEnergyAlongExhaustion_high_temp_h_zero_sandwich_exp_ferromagnetic`

Each ferromagnetic wrapper derives `0 ≤ β * J` from `0 ≤ J` and
`0 < β` and assembles the sandwich from the existing lower / sharper
exp upper bounds (the same construction as the corresponding general
sandwich wrapper in
`HighTemperatureBoundsExpSharperSandwich.lean`). Theorem names are
unchanged from the former `HighTemperatureBoundsExpSharper`
declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

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
  ⟨partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_lower_bound
      G Λ J β (mul_nonneg hβ.le hJ) n,
   partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_upper_bound_exp
      G Λ J β (mul_nonneg hβ.le hJ) n⟩

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
  ⟨freeEnergyAlongExhaustion_high_temp_h_zero_lower_bound
      G Λ J β (mul_nonneg hβ.le hJ) n hne,
   freeEnergyAlongExhaustion_high_temp_h_zero_upper_bound_exp
      G Λ J β (mul_nonneg hβ.le hJ) n hne⟩

end Ambient

end IsingModel

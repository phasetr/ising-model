import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansion
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansionLowerUpper
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharper
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharperSandwichFerro
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharperSandwichLogZ

/-!
# Two-sided zero-field bounds on `Z` and `f` in exponential form

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

Write `|E|` for the edge count of the stage subgraph and `|Λ|` for the cardinality of the
stage volume.

Under `0 ≤ β * J`, the partition function at the parameter record `⟨J, 0, β⟩` lies between
`2 ^ |Λ| * Real.cosh (β * J) ^ |E|` and `2 ^ |Λ| * Real.exp (β * J * |E|)`. Under the same
hypothesis together with `0 < |Λ|`, the free energy lies between
`Real.log 2 + (|E| / |Λ|) * Real.log (Real.cosh (β * J))` and
`Real.log 2 + β * J * |E| / |Λ|`.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

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

end Ambient

end IsingModel

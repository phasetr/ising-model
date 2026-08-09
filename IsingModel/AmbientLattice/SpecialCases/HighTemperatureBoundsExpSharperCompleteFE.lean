import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansion
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharper
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharperSandwich

/-!
# A packaged summary of the zero-field free energy in exponential form

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

Write `|E|` for the edge count of the stage subgraph and `|Λ|` for the cardinality of the
stage volume.

Under `0 ≤ β * J` and a nonempty stage volume, a conjunction records the two-sided bound
`Real.log 2 + (|E| / |Λ|) * Real.log (Real.cosh (β * J)) ≤ f` and
`f ≤ Real.log 2 + β * J * |E| / |Λ|` at the parameter record `⟨J, 0, β⟩`, together with the
values `f = Real.log 2` at `⟨0, 0, β⟩` and at `⟨J, 0, 0⟩`.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

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

end Ambient

end IsingModel

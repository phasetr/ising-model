import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansion
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviation
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviationStrict

/-!
# Zero-field free-energy deviation stated from a nonempty stage volume

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

Write `|E|` for the edge count of the stage subgraph and `|Λ|` for the cardinality of the
stage volume. Each statement takes the stage volume's nonemptiness as a hypothesis.

Under `0 ≤ β * J`, the free energy at the parameter record `⟨J, 0, β⟩` exceeds `Real.log 2`
by at most `β * J * |E| / |Λ|`. Under `0 < β * J` and `0 < |E|`, that excess is strictly
positive.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

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

end Ambient
end IsingModel

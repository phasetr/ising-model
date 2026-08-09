import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansionLowerUpperFEClosed

/-!
# Two-sided zero-field bounds on the free energy in `Real.cosh` form

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

Write `|E|` for the edge count of the stage subgraph and `|Λ|` for the cardinality of the
stage volume.

Under `0 ≤ β * J` and `0 < |Λ|`, the free energy at the parameter record `⟨J, 0, β⟩` is at
least `Real.log 2 + (|E| / |Λ|) * Real.log (Real.cosh (β * J))` and at most
`Real.log 2 + (|E| / |Λ|) * Real.log (2 * Real.cosh (β * J))`.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

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

import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansionLowerUpperFE
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansionLowerUpperConsistency
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansionLowerUpperClosed

/-!
# Two-sided zero-field bounds on `Z` in `Real.cosh` form, along an exhaustion

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

Write `|E|` for the edge count of the stage subgraph and `|Λ|` for the cardinality of the
stage volume.

Under `0 ≤ β * J`, the partition function at the parameter record `⟨J, 0, β⟩` is at least
`2 ^ |Λ| * Real.cosh (β * J) ^ |E|` and at most `2 ^ (|Λ| + |E|) * Real.cosh (β * J) ^ |E|`.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

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

end Ambient

end IsingModel

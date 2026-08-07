import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansion
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansionLowerUpper
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansionClosedCorrelation
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansionClosedSlices

/-!
# Ambient alongExhaustion partitionFunction closed form at h = 0

Gives the closed even-subgraph form of the zero-field partition function along an exhaustion
(GJ §18.3–§18.4), the identity the cluster-expansion capstones rewrite with. It passes
through to the `partitionFunctionΛ_*` ambient lemma at the stage volume.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Along-exhaustion partition function high-temperature closed form (FV §3.7.3 eq. (3.45))**:
at every stage `n`,
`partitionFunctionAlongExhaustion G Λ ⟨J, 0, β⟩ n = 2^|Λ.volume n| · cosh(βJ)^|E_{Λ.volume n}|
  · ∑_{X ⊆ E_{Λ.volume n}, even-degree} tanh(βJ)^|X|`.
Per-stage application of `partitionFunctionΛ_high_temp_expansion_h_zero_closed`
(Step 285). -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_closed
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n
      = (2 : ℝ) ^ (Λ.volume n).card *
        Real.cosh (β * J) ^
          (inducedGraph G (Λ.volume n)).edgeFinset.card *
        ∑ X ∈ (inducedGraph G (Λ.volume n)).edgeFinset.powerset.filter
          (fun X => ∀ v : ↑(Λ.volume n),
            Even ((X.filter (v ∈ ·)).card)),
          Real.tanh (β * J) ^ X.card := by
  change partitionFunctionΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ) = _
  exact partitionFunctionΛ_high_temp_expansion_h_zero_closed
    G (Λ.volume n) J β

end Ambient

end IsingModel

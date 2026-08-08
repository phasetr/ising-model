import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansion
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansionVariantsGeneralH

/-!
# Ambient alongExhaustion high-temp expansion variant wrappers at h = 0

States the GJ §18.3 high-temperature expansion
`Z_n = (cosh βJ)^|E_n| · ∑_σ ∏_e (1 + tanh(βJ) σ_iσ_j)` stagewise, together with the
even-subgraph sum lower bound it is paired with, each a per-stage application of
the corresponding Λ-level lemma.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]


/-- **Along-exhaustion partition function high-temperature expansion at `h = 0`**:
`Z_n(⟨J, 0, β⟩) = (cosh βJ)^|E_n| · ∑_σ ∏_e (1 + tanh(βJ) σ_iσ_j)`
at every stage `n`. Per-stage application of
`partitionFunctionΛ_high_temp_expansion_h_zero` (Step 312). -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n =
      Real.cosh (β * J) ^
          (inducedGraph G (Λ.volume n)).edgeFinset.card *
      ∑ σ : Config ↑(Λ.volume n),
        ∏ e ∈ (inducedGraph G (Λ.volume n)).edgeFinset,
          (1 + Real.tanh (β * J) * edgeSpin σ e) := by
  change partitionFunctionΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ) = _
  exact partitionFunctionΛ_high_temp_expansion_h_zero G (Λ.volume n) J β

/-- **Along-exhaustion high-temperature even-subgraph sum is `≥ 1`**:
under `0 ≤ β * J`, at every stage `n`,
`∑_{X ⊆ E_{Λ.volume n}, even-degree} tanh(β J)^|X| ≥ 1`.
Per-stage application of `one_le_sum_pow_tanh_even_subgraph_Λ`
(Step 296). -/
theorem one_le_sum_pow_tanh_even_subgraph_alongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    (1 : ℝ) ≤ ∑ X ∈
        (inducedGraph G (Λ.volume n)).edgeFinset.powerset.filter
          (fun X : Finset (Sym2 ↑(Λ.volume n)) =>
            ∀ v : ↑(Λ.volume n), Even ((X.filter (v ∈ ·)).card)),
        Real.tanh (β * J) ^ X.card :=
  one_le_sum_pow_tanh_even_subgraph_Λ G (Λ.volume n) J β hβJ

end Ambient

end IsingModel

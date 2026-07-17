import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaCapstones

/-!
# §18.4 partitionFunctionAlongExhaustion polymer/even-subgraph closed forms

Narrow child module for the two §18.4 ambient alongExhaustion
partition-function high-temperature expansion closed-form wrappers
extracted from `HighTemperatureCapstones.lean`:

* `partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_polymer_family`
* `partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_closed_evenSubgraphs`

Each wrapper is a thin pass-through to the corresponding
`partitionFunctionΛ_high_temp_expansion_h_zero_*` ambient lemma
expressing `Z_n(⟨J, 0, β⟩)` either in the polymer-family form or
in the closed even-subgraph form. Theorem names are unchanged from
the former `HighTemperatureCapstones` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: §18.4 partitionFunction polymer-family form**. -/
theorem
partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_polymer_family
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ ⟨J, 0, β⟩ n =
      (2 : ℝ) ^ Fintype.card ↑(Λ.volume n : Finset V) *
        Real.cosh (β * J) ^
          (inducedGraph G (Λ.volume n)).edgeFinset.card *
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card :=
  partitionFunctionΛ_high_temp_expansion_h_zero_polymer_family
    G (Λ.volume n) J β

/-- **Along-ex: §18.4 partitionFunction even-subgraph form**. -/
theorem
partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_closed_evenSubgraphs
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ ⟨J, 0, β⟩ n =
      (2 : ℝ) ^ Fintype.card ↑(Λ.volume n : Finset V) *
        Real.cosh (β * J) ^
          (inducedGraph G (Λ.volume n)).edgeFinset.card *
        ∑ X ∈ IsingModel.evenSubgraphs (inducedGraph G (Λ.volume n)),
          Real.tanh (β * J) ^ X.card :=
  partitionFunctionΛ_high_temp_expansion_h_zero_closed_evenSubgraphs
    G (Λ.volume n) J β

end Ambient
end IsingModel

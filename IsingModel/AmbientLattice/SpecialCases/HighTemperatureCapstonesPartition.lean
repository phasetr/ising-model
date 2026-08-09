import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaCapstones

/-!
# Closed forms for the zero-field partition function, along an exhaustion

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

Write `|E|` for the edge count of the stage subgraph and `|Λ|` for the cardinality of the
stage volume. Each is stated for arbitrary `J` and `β`.

The partition function at the parameter record `⟨J, 0, β⟩` is
`2 ^ |Λ| * Real.cosh (β * J) ^ |E|` times a combinatorial factor: the sum of
`∏ P ∈ Γ, Real.tanh (β * J) ^ P.card` over the stage subgraph's vertex-disjoint compatible
polymer families in one form, and the sum of `Real.tanh (β * J) ^ X.card` over that
subgraph's `IsingModel.evenSubgraphs` in the other.
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

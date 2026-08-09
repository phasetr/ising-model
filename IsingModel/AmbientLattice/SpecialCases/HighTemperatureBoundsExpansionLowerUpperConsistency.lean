import IsingModel.AmbientLattice.Exhaustion

/-!
# Consistency of the zero-field high-temperature lower and upper bounds

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Each statement takes the
stagewise `Fintype` instance on that subgraph's edge set and omits `DecidableEq V`.

Write `|E|` for the edge count of the stage subgraph and `|Λ|` for the cardinality of the
stage volume. Each statement compares two bounding expressions of the high-temperature
sandwich directly.

For arbitrary `J` and `β`,
`2 ^ |Λ| * Real.cosh (β * J) ^ |E| ≤ 2 ^ (|Λ| + |E|) * Real.cosh (β * J) ^ |E|`. Under
`0 ≤ β * J`, `Real.log 2 + (|E| / |Λ|) * Real.log (Real.cosh (β * J))` is at most
`Real.log 2 + (|E| / |Λ|) * Real.log (2 * Real.cosh (β * J))`.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
/-- **Along-exhaustion Z bounds consistency**: lower ≤ upper. -/
theorem partitionFunctionAlongExhaustion_high_temp_h_zero_lower_le_upper
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    (2 : ℝ) ^ (Λ.volume n).card *
        Real.cosh (β * J) ^
          (inducedGraph G (Λ.volume n)).edgeFinset.card
      ≤ (2 : ℝ) ^ ((Λ.volume n).card +
            (inducedGraph G (Λ.volume n)).edgeFinset.card) *
        Real.cosh (β * J) ^
            (inducedGraph G (Λ.volume n)).edgeFinset.card :=
  partitionFunctionΛ_high_temp_h_zero_lower_le_upper G (Λ.volume n) J β

omit [DecidableEq V] in
/-- **Along-exhaustion freeEnergy bounds consistency**: lower ≤ upper. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_lower_le_upper
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    Real.log 2 +
        ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
          (Λ.volume n).card * Real.log (Real.cosh (β * J))
      ≤ Real.log 2
        + ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
            (Λ.volume n).card * Real.log (2 * Real.cosh (β * J)) :=
  freeEnergyΛ_high_temp_h_zero_lower_le_upper G (Λ.volume n) J β hβJ

end Ambient

end IsingModel

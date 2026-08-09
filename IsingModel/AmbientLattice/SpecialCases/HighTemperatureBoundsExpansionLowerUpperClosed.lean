import IsingModel.AmbientLattice.Exhaustion

/-!
# The zero-field high-temperature closed form for `log Z`, along an exhaustion

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

Write `|E|` for the edge count of the stage subgraph and `|Λ|` for the cardinality of the
stage volume.

Under `0 ≤ β * J`, the logarithm of the partition function at the parameter record
`⟨J, 0, β⟩` is `|Λ| * Real.log 2 + |E| * Real.log (Real.cosh (β * J))` plus the logarithm of
`∑ X, Real.tanh (β * J) ^ X.card`, the sum running over the subsets `X` of the stage edge
finset in which every site has even degree.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Along-exhaustion log Z high-temperature decomposition (GJ §18.3 / FV (3.45))**:
under `0 ≤ β·J`, at every stage `n`,
`log Z_n(⟨J, 0, β⟩) = |Λ_n| · log 2 + |E_n| · log(cosh βJ) + log(∑_{X even} tanh^|X|)`.
Per-stage application of `log_partitionFunctionΛ_high_temp_expansion_h_zero_closed`
(Step 316). -/
theorem log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_closed
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n)
      = ((Λ.volume n).card : ℝ) * Real.log 2
        + ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) *
            Real.log (Real.cosh (β * J))
        + Real.log
            (∑ X ∈ (inducedGraph G (Λ.volume n)).edgeFinset.powerset.filter
                (fun X : Finset (Sym2 ↑(Λ.volume n)) =>
                  ∀ v : ↑(Λ.volume n), Even ((X.filter (v ∈ ·)).card)),
              Real.tanh (β * J) ^ X.card) := by
  change Real.log (partitionFunctionΛ G (Λ.volume n)
      (⟨J, 0, β⟩ : IsingParams ℝ)) = _
  exact log_partitionFunctionΛ_high_temp_expansion_h_zero_closed
    G (Λ.volume n) J β hβJ

end Ambient

end IsingModel

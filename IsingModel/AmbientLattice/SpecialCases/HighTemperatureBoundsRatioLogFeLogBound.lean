import IsingModel.AmbientLattice.Exhaustion

/-!
# The packaged two-sided bound on the zero-field `log Z` difference

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

Write `|E|` for the edge count of the stage subgraph. The difference taken is the logarithm
of the partition function at `⟨J, 0, β⟩` minus its value at one of the trivial slices
`⟨0, 0, β⟩` and `⟨J, 0, 0⟩`.

Under `0 ≤ β * J`, a conjunction records for each of those two differences that it lies
between `|E| * Real.log (Real.cosh (β * J))` and `β * J * |E|`.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Along-ex log Z ratio sandwich bundle at stage `n`**. -/
theorem log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_sandwich_bundle
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    (((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) *
        Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunctionAlongExhaustion G Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n)
            - Real.log (partitionFunctionAlongExhaustion G Λ
                (⟨0, 0, β⟩ : IsingParams ℝ) n) ∧
      Real.log (partitionFunctionAlongExhaustion G Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n)
          - Real.log (partitionFunctionAlongExhaustion G Λ
              (⟨0, 0, β⟩ : IsingParams ℝ) n)
          ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card) ∧
    (((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) *
        Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunctionAlongExhaustion G Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n)
            - Real.log (partitionFunctionAlongExhaustion G Λ
                (⟨J, 0, 0⟩ : IsingParams ℝ) n) ∧
      Real.log (partitionFunctionAlongExhaustion G Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n)
          - Real.log (partitionFunctionAlongExhaustion G Λ
              (⟨J, 0, 0⟩ : IsingParams ℝ) n)
          ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card) := by
  change (_ ≤ Real.log (partitionFunctionΛ G (Λ.volume n)
      (⟨J, 0, β⟩ : IsingParams ℝ))
      - Real.log (partitionFunctionΛ G (Λ.volume n)
          (⟨0, 0, β⟩ : IsingParams ℝ)) ∧ _) ∧
      (_ ≤ Real.log (partitionFunctionΛ G (Λ.volume n)
          (⟨J, 0, β⟩ : IsingParams ℝ))
          - Real.log (partitionFunctionΛ G (Λ.volume n)
              (⟨J, 0, 0⟩ : IsingParams ℝ)) ∧ _)
  exact log_partitionFunctionΛ_high_temp_expansion_h_zero_ratio_sandwich_bundle
    G (Λ.volume n) J β hβJ

end Ambient

end IsingModel

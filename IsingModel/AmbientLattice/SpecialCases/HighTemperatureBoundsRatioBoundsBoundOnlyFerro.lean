import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioBoundsSingletons

/-!
# Upper bounds on the partition-function ratio under `0 ≤ J` and `0 < β`

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

Write `|E|` for the edge count of the stage subgraph. The ratio taken is the partition
function at `⟨J, 0, β⟩` over its value at one of the trivial slices `⟨0, 0, β⟩` and
`⟨J, 0, 0⟩`.

Under `0 ≤ J` and `0 < β`, each of those two ratios is at most `Real.exp (β * J * |E|)`.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Along-ex ferromagnetic Z ratio upper bound at J=0, stage `n`**. -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n /
        partitionFunctionAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n
      ≤ Real.exp (β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card) :=
  (partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_sandwich
    G Λ J β (mul_nonneg hβ.le hJ) n).2

/-- **Along-ex ferromagnetic Z ratio upper bound at β=0, stage `n`**. -/
theorem
partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound_beta_zero_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n /
        partitionFunctionAlongExhaustion G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) n
      ≤ Real.exp (β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card) :=
  (partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_sandwich_beta_zero
    G Λ J β (mul_nonneg hβ.le hJ) n).2

end Ambient

end IsingModel

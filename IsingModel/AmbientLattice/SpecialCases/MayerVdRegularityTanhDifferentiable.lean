import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaMayer

/-!
# `mayerPartialSum` tanh `Differentiable` along-ex wrappers

Narrow child module for the two §18.5--§18.6 along-exhaustion
`mayerPartialSum ∘ tanh ∘ (·)` `Differentiable` wrappers extracted
from `MayerVdRegularityTanh.lean`:

* `mayerPartialSumAlongExhaustion_tanh_differentiable_beta`
* `mayerPartialSumAlongExhaustion_tanh_differentiable_J`

Each wrapper is a thin pass-through to the corresponding
`mayerPartialSum_Λ_tanh_differentiable_*` ambient lemma. Theorem
names are unchanged from the former `MayerVdRegularity` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: mayerPartialSum ∘ tanh ∘ (·*J) differentiable in β**. -/
theorem mayerPartialSumAlongExhaustion_tanh_differentiable_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (J : ℝ) (n : ℕ) :
    Differentiable ℝ (fun β' : ℝ =>
        IsingModel.mayerPartialSum
          (inducedGraph G (Λ.volume n)) N
          (Real.tanh (β' * J))) :=
  mayerPartialSum_Λ_tanh_differentiable_beta G (Λ.volume n) N J

/-- **Along-ex: mayerPartialSum ∘ tanh ∘ (β*·) differentiable in J**. -/
theorem mayerPartialSumAlongExhaustion_tanh_differentiable_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (β : ℝ) (n : ℕ) :
    Differentiable ℝ (fun J' : ℝ =>
        IsingModel.mayerPartialSum
          (inducedGraph G (Λ.volume n)) N
          (Real.tanh (β * J'))) :=
  mayerPartialSum_Λ_tanh_differentiable_J G (Λ.volume n) N β

end Ambient
end IsingModel

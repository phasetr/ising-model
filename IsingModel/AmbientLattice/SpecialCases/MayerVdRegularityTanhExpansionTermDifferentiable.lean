import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaMayer

/-!
# `mayerExpansionTerm` tanh `Differentiable` along-ex wrappers

Narrow child module for the two §18.5--§18.6 along-exhaustion
`mayerExpansionTerm ∘ tanh ∘ (·)` `Differentiable` wrappers
extracted from `MayerVdRegularityTanhExpansionTerm.lean`:

* `mayerExpansionTermAlongExhaustion_tanh_differentiable_beta`
* `mayerExpansionTermAlongExhaustion_tanh_differentiable_J`

Each wrapper is a thin pass-through to the corresponding
`mayerExpansionTerm_Λ_tanh_differentiable_*` ambient lemma. Theorem
names are unchanged from the former `MayerVdRegularity` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: mayerExpansionTerm ∘ tanh ∘ (·*J) differentiable in β**. -/
theorem mayerExpansionTermAlongExhaustion_tanh_differentiable_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (k : ℕ) (J : ℝ) (n : ℕ) :
    Differentiable ℝ (fun β' : ℝ =>
        IsingModel.mayerExpansionTerm
          (inducedGraph G (Λ.volume n)) k
          (Real.tanh (β' * J))) :=
  mayerExpansionTerm_Λ_tanh_differentiable_beta G (Λ.volume n) k J

/-- **Along-ex: mayerExpansionTerm ∘ tanh ∘ (β*·) differentiable in J**. -/
theorem mayerExpansionTermAlongExhaustion_tanh_differentiable_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (k : ℕ) (β : ℝ) (n : ℕ) :
    Differentiable ℝ (fun J' : ℝ =>
        IsingModel.mayerExpansionTerm
          (inducedGraph G (Λ.volume n)) k
          (Real.tanh (β * J'))) :=
  mayerExpansionTerm_Λ_tanh_differentiable_J G (Λ.volume n) k β

end Ambient
end IsingModel

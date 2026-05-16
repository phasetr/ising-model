import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.MayerVdRegularityTanhExpansionTermDifferentiable

/-!
# `mayerExpansionTerm` tanh regularity wrappers along an exhaustion

Narrow child module for the four §18.5 along-exhaustion
`mayerExpansionTerm` tanh-composed continuity / differentiability
wrappers in `β` and `J`. Each wrapper is a thin pass-through to
the corresponding `mayerExpansionTerm_Λ_tanh_*` ambient lemma.
Theorem names are unchanged from the former `MayerVdRegularityTanh`
declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### §18.5 mayerExpansionTerm tanh β/J along-ex wraps -/

/-- **Along-ex: mayerExpansionTerm ∘ tanh ∘ (·*J) continuous in β**. -/
theorem mayerExpansionTermAlongExhaustion_tanh_continuous_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (k : ℕ) (J : ℝ) (n : ℕ) :
    Continuous (fun β' : ℝ =>
        IsingModel.mayerExpansionTerm
          (inducedGraph G (Λ.volume n)) k
          (Real.tanh (β' * J))) :=
  mayerExpansionTerm_Λ_tanh_continuous_beta G (Λ.volume n) k J

/-- **Along-ex: mayerExpansionTerm ∘ tanh ∘ (β*·) continuous in J**. -/
theorem mayerExpansionTermAlongExhaustion_tanh_continuous_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (k : ℕ) (β : ℝ) (n : ℕ) :
    Continuous (fun J' : ℝ =>
        IsingModel.mayerExpansionTerm
          (inducedGraph G (Λ.volume n)) k
          (Real.tanh (β * J'))) :=
  mayerExpansionTerm_Λ_tanh_continuous_J G (Λ.volume n) k β

/-! ## Moved: 2 mayerExpansionTerm tanh Differentiable wrappers

The two `mayerExpansionTermAlongExhaustion_tanh_differentiable_*`
wrappers (`_tanh_differentiable_beta`, `_tanh_differentiable_J`)
now live in
`IsingModel.AmbientLattice.SpecialCases.MayerVdRegularityTanhExpansionTermDifferentiable`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella.
-/

end Ambient
end IsingModel

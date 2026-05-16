import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.MayerVdRegularityTanhExpansionTerm
import IsingModel.AmbientLattice.SpecialCases.MayerVdRegularityTanhDifferentiable

/-!
# `mayerPartialSum` / `mayerExpansionTerm` tanh regularity wrappers along an exhaustion

Narrow child module for the eight §18.5--§18.6 along-exhaustion
`mayerPartialSum` and `mayerExpansionTerm` tanh-composed continuity
and differentiability wrappers in `β` and `J`. Each wrapper is a thin
pass-through to the corresponding `mayerPartialSum_Λ_tanh_*` /
`mayerExpansionTerm_Λ_tanh_*` ambient lemma. Theorem names are
unchanged from the former `MayerVdRegularity` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### §18.6 mayerPartialSum tanh β/J along-ex wraps -/

/-- **Along-ex: mayerPartialSum ∘ tanh ∘ (·*J) continuous in β**. -/
theorem mayerPartialSumAlongExhaustion_tanh_continuous_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (J : ℝ) (n : ℕ) :
    Continuous (fun β' : ℝ =>
        IsingModel.mayerPartialSum
          (inducedGraph G (Λ.volume n)) N
          (Real.tanh (β' * J))) :=
  mayerPartialSum_Λ_tanh_continuous_beta G (Λ.volume n) N J

/-- **Along-ex: mayerPartialSum ∘ tanh ∘ (β*·) continuous in J**. -/
theorem mayerPartialSumAlongExhaustion_tanh_continuous_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (β : ℝ) (n : ℕ) :
    Continuous (fun J' : ℝ =>
        IsingModel.mayerPartialSum
          (inducedGraph G (Λ.volume n)) N
          (Real.tanh (β * J'))) :=
  mayerPartialSum_Λ_tanh_continuous_J G (Λ.volume n) N β

/-! ## Moved: 2 mayerPartialSum tanh Differentiable wrappers

The two `mayerPartialSumAlongExhaustion_tanh_differentiable_*`
wrappers (`_tanh_differentiable_beta`, `_tanh_differentiable_J`)
now live in
`IsingModel.AmbientLattice.SpecialCases.MayerVdRegularityTanhDifferentiable`.
The legacy import path is preserved by re-exporting the new child
from this parent module and from the umbrella.
-/

/-! ## Moved: mayerExpansionTerm tanh β/J along-ex wraps

The four `mayerExpansionTermAlongExhaustion_tanh_*` continuity /
differentiability wrappers (in `β` and `J`) now live in
`IsingModel.AmbientLattice.SpecialCases.MayerVdRegularityTanhExpansionTerm`.
The legacy import path is preserved by re-exporting the new child
from this parent module and from `Legacy.lean`.
-/

end Ambient
end IsingModel

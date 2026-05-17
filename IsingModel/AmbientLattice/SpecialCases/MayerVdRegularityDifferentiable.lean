import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.MayerVdRegularityDifferentiableExpansionTerm

/-!
# Mayer `mayerPartialSum` Differentiable along-ex wrappers

Narrow child module for the two §18.6 along-exhaustion
`mayerPartialSumAlongExhaustion_*` `Differentiable` /
`DifferentiableOn` wrappers. The corresponding
`mayerExpansionTermAlongExhaustion_differentiable` wrapper now
lives in
`IsingModel.AmbientLattice.SpecialCases.MayerVdRegularityDifferentiableExpansionTerm`
and is re-imported through this parent module. Each wrapper is a
thin pass-through to the corresponding
`mayer*_Λ_differentiable*` ambient lemma. Theorem names are
unchanged from the former `MayerVdRegularity` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: `mayerPartialSum` is `Differentiable ℝ`**. -/
theorem mayerPartialSumAlongExhaustion_differentiable
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (n : ℕ) :
    Differentiable ℝ (fun t : ℝ =>
        IsingModel.mayerPartialSum
          (inducedGraph G (Λ.volume n)) N t) :=
  mayerPartialSum_Λ_differentiable G (Λ.volume n) N

/-- **Along-ex: `mayerPartialSum` is `DifferentiableOn ℝ`**. -/
theorem mayerPartialSumAlongExhaustion_differentiableOn
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (n : ℕ) (s : Set ℝ) :
    DifferentiableOn ℝ (fun t : ℝ =>
        IsingModel.mayerPartialSum
          (inducedGraph G (Λ.volume n)) N t) s :=
  mayerPartialSum_Λ_differentiableOn G (Λ.volume n) N s

/-! ## Moved: 1 `mayerExpansionTerm` Differentiable wrapper

The `mayerExpansionTermAlongExhaustion_differentiable` wrapper
now lives in
`IsingModel.AmbientLattice.SpecialCases.MayerVdRegularityDifferentiableExpansionTerm`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

end Ambient
end IsingModel

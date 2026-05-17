import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.MayerVdRegularityDifferentiable
import IsingModel.AmbientLattice.SpecialCases.MayerVdRegularityTanh
import IsingModel.AmbientLattice.SpecialCases.MayerVdRegularityVdPolymer
import IsingModel.AmbientLattice.SpecialCases.MayerVdRegularityExpansionTerm

/-!
# Mayer and polymer-family regularity wrappers along an exhaustion

Narrow child module for along-exhaustion `mayerPartialSum`,
`mayerExpansionTerm`, and `vdPolymerFamilies_sum` regularity and tanh
wrappers. This keeps callers that only need these forwarders out of the
monolithic original special-cases module.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### §18.6 mayerPartialSum regularity along-ex wraps -/

/-- **Along-ex: `mayerPartialSum` is `Continuous`**. -/
theorem mayerPartialSumAlongExhaustion_continuous
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (n : ℕ) :
    Continuous (fun t : ℝ =>
        IsingModel.mayerPartialSum
          (inducedGraph G (Λ.volume n)) N t) :=
  mayerPartialSum_Λ_continuous G (Λ.volume n) N

/-- **Along-ex: `mayerPartialSum` is `ContinuousOn`**. -/
theorem mayerPartialSumAlongExhaustion_continuousOn
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (n : ℕ) (s : Set ℝ) :
    ContinuousOn (fun t : ℝ =>
        IsingModel.mayerPartialSum
          (inducedGraph G (Λ.volume n)) N t) s :=
  mayerPartialSum_Λ_continuousOn G (Λ.volume n) N s

/-! ## Moved: 1 `mayerExpansionTerm` Continuous wrapper

The `mayerExpansionTermAlongExhaustion_continuous` wrapper now
lives in
`IsingModel.AmbientLattice.SpecialCases.MayerVdRegularityExpansionTerm`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

/-! ### Moved: `mayerPartialSum` / `mayerExpansionTerm` Differentiable wraps

The three `mayer*AlongExhaustion_differentiable*` wrappers
(`mayerPartialSum_differentiable`, `_differentiableOn`,
`mayerExpansionTerm_differentiable`) now live in
`IsingModel.AmbientLattice.SpecialCases.MayerVdRegularityDifferentiable`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

/-! ### Moved: `mayerPartialSum` / `mayerExpansionTerm` tanh along-ex wraps

The eight `mayerPartialSumAlongExhaustion_tanh_*` and
`mayerExpansionTermAlongExhaustion_tanh_*` continuity /
differentiability wrappers (in `β` and `J`) now live in
`IsingModel.AmbientLattice.SpecialCases.MayerVdRegularityTanh`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

/-! ### §18.6 vdPolymerFamilies_sum regularity in t along-ex wraps -/

/-! ### Moved: `vdPolymerFamilies_sum` along-ex regularity wraps

The seven `vdPolymerFamilies_sumAlongExhaustion_*` wrappers
(`continuous`, `differentiable`, `hasDerivAt`, and the four
tanh-composed `_continuous_{beta,J}` / `_differentiable_{beta,J}`
variants) now live in
`IsingModel.AmbientLattice.SpecialCases.MayerVdRegularityVdPolymer`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

end Ambient
end IsingModel

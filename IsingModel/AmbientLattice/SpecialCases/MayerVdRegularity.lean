import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.MayerVdRegularityTanh
import IsingModel.AmbientLattice.SpecialCases.MayerVdRegularityVdPolymer

/-!
# Mayer and polymer-family regularity wrappers along an exhaustion

Narrow child module for along-exhaustion `mayerPartialSum`,
`mayerExpansionTerm`, and `vdPolymerFamilies_sum` regularity and tanh
wrappers. This keeps callers that only need these forwarders out of the
monolithic legacy special-cases module.
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

/-- **Along-ex: `mayerPartialSum` is `Differentiable ℝ`**. -/
theorem mayerPartialSumAlongExhaustion_differentiable
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (n : ℕ) :
    Differentiable ℝ (fun t : ℝ =>
        IsingModel.mayerPartialSum
          (inducedGraph G (Λ.volume n)) N t) :=
  mayerPartialSum_Λ_differentiable G (Λ.volume n) N

/-- **Along-ex: `mayerPartialSum` is `ContinuousOn`**. -/
theorem mayerPartialSumAlongExhaustion_continuousOn
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (n : ℕ) (s : Set ℝ) :
    ContinuousOn (fun t : ℝ =>
        IsingModel.mayerPartialSum
          (inducedGraph G (Λ.volume n)) N t) s :=
  mayerPartialSum_Λ_continuousOn G (Λ.volume n) N s

/-- **Along-ex: `mayerPartialSum` is `DifferentiableOn ℝ`**. -/
theorem mayerPartialSumAlongExhaustion_differentiableOn
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (n : ℕ) (s : Set ℝ) :
    DifferentiableOn ℝ (fun t : ℝ =>
        IsingModel.mayerPartialSum
          (inducedGraph G (Λ.volume n)) N t) s :=
  mayerPartialSum_Λ_differentiableOn G (Λ.volume n) N s

/-! ### §18.6 mayerExpansionTerm regularity along-ex wraps -/

/-- **Along-ex: `mayerExpansionTerm` is `Continuous`**. -/
theorem mayerExpansionTermAlongExhaustion_continuous
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (k : ℕ) (n : ℕ) :
    Continuous (fun t : ℝ =>
        IsingModel.mayerExpansionTerm
          (inducedGraph G (Λ.volume n)) k t) :=
  mayerExpansionTerm_Λ_continuous G (Λ.volume n) k

/-- **Along-ex: `mayerExpansionTerm` is `Differentiable ℝ`**. -/
theorem mayerExpansionTermAlongExhaustion_differentiable
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (k : ℕ) (n : ℕ) :
    Differentiable ℝ (fun t : ℝ =>
        IsingModel.mayerExpansionTerm
          (inducedGraph G (Λ.volume n)) k t) :=
  mayerExpansionTerm_Λ_differentiable G (Λ.volume n) k

/-! ### Moved: `mayerPartialSum` / `mayerExpansionTerm` tanh along-ex wraps

The eight `mayerPartialSumAlongExhaustion_tanh_*` and
`mayerExpansionTermAlongExhaustion_tanh_*` continuity /
differentiability wrappers (in `β` and `J`) now live in
`IsingModel.AmbientLattice.SpecialCases.MayerVdRegularityTanh`.
The legacy import path is preserved by re-exporting the new child
from this parent module and from `Legacy.lean`.
-/

/-! ### §18.6 vdPolymerFamilies_sum regularity in t along-ex wraps -/

/-! ### Moved: `vdPolymerFamilies_sum` along-ex regularity wraps

The seven `vdPolymerFamilies_sumAlongExhaustion_*` wrappers
(`continuous`, `differentiable`, `hasDerivAt`, and the four
tanh-composed `_continuous_{beta,J}` / `_differentiable_{beta,J}`
variants) now live in
`IsingModel.AmbientLattice.SpecialCases.MayerVdRegularityVdPolymer`.
The legacy import path is preserved by re-exporting the new child
from this parent module and from `Legacy.lean`.
-/

end Ambient
end IsingModel

import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.MayerAnalyticityExpansionTerm
import IsingModel.AmbientLattice.SpecialCases.MayerAnalyticityTanh

/-!
# Mayer analyticity wrappers along an exhaustion

Narrow child module for along-exhaustion `mayerPartialSum` and
`mayerExpansionTerm` analytic wrappers. This keeps callers that only need
these analytic forwarders out of the monolithic legacy special-cases module.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### `mayerPartialSum` analyticity along an exhaustion -/

/-- **Along-ex: `mayerPartialSum` is `AnalyticAt ℝ`**. -/
theorem mayerPartialSumAlongExhaustion_analyticAt
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (n : ℕ) (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ =>
        IsingModel.mayerPartialSum
          (inducedGraph G (Λ.volume n)) N s) t :=
  mayerPartialSum_Λ_analyticAt G (Λ.volume n) N t

/-- **Along-ex: mayerPartialSum `AnalyticOnNhd ℝ _ Set.univ`**. -/
theorem mayerPartialSumAlongExhaustion_analyticOnNhd
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (n : ℕ) :
    AnalyticOnNhd ℝ
      (fun s : ℝ => IsingModel.mayerPartialSum
          (inducedGraph G (Λ.volume n)) N s) Set.univ :=
  mayerPartialSum_Λ_analyticOnNhd G (Λ.volume n) N

/-! ## Moved: mayerExpansionTermAlongExhaustion analyticity wrappers

The two `mayerExpansionTermAlongExhaustion_analytic{At,OnNhd}` wrappers
now live in `MayerAnalyticityExpansionTerm.lean`. They are re-imported
here so downstream consumers continue to see the symbols. -/


/-! ## Moved: mayerPartialSumAlongExhaustion tanh analyticity wrappers

The four `mayerPartialSumAlongExhaustion_tanh_analytic*` wrappers
(`_analyticAt_beta`, `_analyticAt_J`, `_analyticOnNhd_beta`,
`_analyticOnNhd_J`) now live in
`IsingModel.AmbientLattice.SpecialCases.MayerAnalyticityTanh`.
The legacy import path is preserved by re-exporting the new child
from this parent module and from `Legacy.lean`.
-/

/-! ## Moved: mayerExpansionTermAlongExhaustion tanh analyticity wrappers

The two `mayerExpansionTermAlongExhaustion_tanh_analyticAt_{beta,J}`
wrappers now live in `MayerAnalyticityExpansionTerm.lean`. -/


end Ambient
end IsingModel

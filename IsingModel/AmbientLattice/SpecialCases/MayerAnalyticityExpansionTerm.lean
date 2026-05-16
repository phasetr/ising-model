import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.MayerAnalyticityExpansionTermTanh

/-!
# Ambient mayerExpansionTermAlongExhaustion analyticity wrappers

Narrow child module for 4 ambient `mayerExpansionTermAlongExhaustion_*`
analyticity wrappers extracted from `MayerAnalyticity.lean`:

* `mayerExpansionTermAlongExhaustion_analyticAt`,
* `mayerExpansionTermAlongExhaustion_analyticOnNhd`,
* `mayerExpansionTermAlongExhaustion_tanh_analyticAt_beta`,
* `mayerExpansionTermAlongExhaustion_tanh_analyticAt_J`.

Each result is a thin pass-through of the corresponding Λ-level
`mayerExpansionTerm_Λ_*` analyticity lemma. The theorem names are
unchanged from the former `MayerAnalyticity` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]


/-! ### `mayerExpansionTerm` analyticity along an exhaustion -/

/-- **Along-ex: `mayerExpansionTerm` is `AnalyticAt ℝ`**. -/
theorem mayerExpansionTermAlongExhaustion_analyticAt
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (k : ℕ) (n : ℕ) (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ =>
        IsingModel.mayerExpansionTerm
          (inducedGraph G (Λ.volume n)) k s) t :=
  mayerExpansionTerm_Λ_analyticAt G (Λ.volume n) k t

/-- **Along-ex: `mayerExpansionTerm` is
`AnalyticOnNhd ℝ _ Set.univ`**. -/
theorem mayerExpansionTermAlongExhaustion_analyticOnNhd
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (k : ℕ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun s : ℝ =>
        IsingModel.mayerExpansionTerm
          (inducedGraph G (Λ.volume n)) k s) Set.univ :=
  mayerExpansionTerm_Λ_analyticOnNhd G (Λ.volume n) k

/-! ## Moved: 2 mayerExpansionTerm tanh AnalyticAt wrappers

The two `mayerExpansionTermAlongExhaustion_tanh_analyticAt_*`
wrappers (`_tanh_analyticAt_beta`, `_tanh_analyticAt_J`) now live
in
`IsingModel.AmbientLattice.SpecialCases.MayerAnalyticityExpansionTermTanh`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella.
-/

end Ambient
end IsingModel

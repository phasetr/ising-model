import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.BetaDerivative
import IsingModel.BetaDerivative
import IsingModel.FieldDerivative

/-!
# magnetizationAlongExhaustion `HasDerivAt` wrappers (Step 213, GJ §17.5)

Narrow child module for the two `magnetizationAlongExhaustion`
existence-form β-derivative wrappers
`magnetizationAlongExhaustion_hasDerivAt_beta` (at `h = 0`) and
`magnetizationAlongExhaustion_hasDerivAt_beta_general_h_gen` (at general
`h`). Each is a thin pass-through to the corresponding
`correlationAlongExhaustion_hasDerivAt_*` lemma at `A = {i}`. Extracted
from `BetaDerivative.lean` in PR #2063; the theorem names are unchanged
from the former `BetaDerivative` declarations.

The `Continuous` / `Differentiable` regularity of
`magnetizationAlongExhaustion` in the β / h / J directions lives in
`AmbientLattice/SpecialCases/Magnetization.lean`; the six `_gen`-suffixed
duplicates that used to sit here were retired in PR #4839 because each
stated exactly the same proposition as its `SpecialCases` counterpart
(same binders in the same order, and the β pair was already at general
`h`). Their `h = 0` corollaries
`magnetizationAlongExhaustion_{continuous, differentiable}_beta_gen`
keep their names and moved to the same `SpecialCases` module.
-/

namespace IsingModel.Ambient

variable {V : Type*} [DecidableEq V]

/-! ## Step 213: magnetizationAlongExhaustion β-direction `HasDerivAt` -/

/-- **β-derivative of `magnetizationAlongExhaustion` at `h = 0`** (GJ §17.5):
The function `fun β' => magnetizationAlongExhaustion G Λ ⟨J, 0, β'⟩ i n`
has a derivative at `β`.

Direct specialization of `correlationAlongExhaustion_hasDerivAt_beta` at
`A = {i}`. -/
theorem magnetizationAlongExhaustion_hasDerivAt_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (i : V) (n : ℕ) :
    ∃ d : ℝ, HasDerivAt
      (fun β' => magnetizationAlongExhaustion G Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) i n) d β := by
  unfold magnetizationAlongExhaustion
  exact correlationAlongExhaustion_hasDerivAt_beta G Λ J β {i} n

/-- **β-derivative of `magnetizationAlongExhaustion` at general `h`** (GJ §17.5):
The function `fun β' => magnetizationAlongExhaustion G Λ ⟨J, h, β'⟩ i n`
has a derivative at `β`, at any `h`.

Direct specialization of `correlationAlongExhaustion_hasDerivAt_beta_general_h_gen`
at `A = {i}`. -/
theorem magnetizationAlongExhaustion_hasDerivAt_beta_general_h_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    ∃ d : ℝ, HasDerivAt
      (fun β' => magnetizationAlongExhaustion G Λ
          (⟨J, h, β'⟩ : IsingParams ℝ) i n) d β := by
  unfold magnetizationAlongExhaustion
  exact correlationAlongExhaustion_hasDerivAt_beta_general_h_gen G Λ J h β {i} n

end IsingModel.Ambient

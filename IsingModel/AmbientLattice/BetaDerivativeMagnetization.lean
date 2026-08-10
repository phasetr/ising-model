import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.BetaDerivative
import IsingModel.BetaDerivative
import IsingModel.FieldDerivative

/-!
# Existence of the inverse-temperature derivative of the stage magnetization

Statements for an ambient graph `G : SimpleGraph V`, an exhaustion `Λ` of `V`, an ambient site
`i : V` and a stage index `n`. The stage magnetization
`magnetizationAlongExhaustion G Λ p i n` is the stage correlation at the singleton test set
`{i}`.

Each declaration takes exactly two instance binders, `DecidableEq V` and the stagewise
`Fintype` instance on the edge set of the induced subgraph of `Λ.volume n`, and neither
carries a Prop-valued hypothesis.

Fixing the coupling and the field and varying the inverse temperature, the map
`β' ↦ magnetizationAlongExhaustion G Λ ⟨J, h, β'⟩ i n` has a derivative at every point, stated
in the existence form `∃ d, HasDerivAt … d β`. The zero field and an arbitrary field are
treated separately, each by unfolding the stage magnetization to the stage correlation at
`{i}` and applying the corresponding statement about the stage correlation.
-/

namespace IsingModel.Ambient

variable {V : Type*} [DecidableEq V]

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

import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.MagnetizationAlongExhaustion
import IsingModel.JDerivative

/-!
# J-derivative of correlationAlongExhaustion / magnetizationAlongExhaustion (GJ §17.5)

Shows that for any graph G whose exhaustion stages have finite edge sets,
the functions
`fun J' => correlationAlongExhaustion G Λ ⟨J', h, β⟩ A n` and
`fun J' => magnetizationAlongExhaustion G Λ ⟨J', h, β⟩ i n`
have a derivative at J.

Subset / membership case: lift to the finite-volume `hasDerivAt_correlation_J`.
Non-subset / non-member case: constant zero.

Companion to `IsingModel.AmbientLattice.BetaDerivative` (β-direction).
The corresponding `Continuous*` / `Differentiable*` wrappers already
exist in `BetaDerivative.lean` under the `_gen` suffix.

Reference: Glimm–Jaffe §17.5–§17.6 (covariance-form thermodynamic
derivative identities). -/

namespace IsingModel.Ambient

variable {V : Type*} [DecidableEq V]

/-- **J-derivative of `correlationAlongExhaustion`** (GJ §17.5):
The function `fun J' => correlationAlongExhaustion G Λ ⟨J', h, β⟩ A n`
has a derivative at `J`.

Proof: split on `A ⊆ Λ.volume n`. In the subset case, unfold to the
finite-volume correlation on the induced graph and apply
`hasDerivAt_correlation_J`. In the non-subset case, the function is
constant zero, with derivative 0. -/
theorem correlationAlongExhaustion_hasDerivAt_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (A : Finset V) (n : ℕ) :
    ∃ d : ℝ, HasDerivAt
      (fun J' => correlationAlongExhaustion G Λ
          (⟨J', h, β⟩ : IsingParams ℝ) A n) d J := by
  by_cases h_sub : A ⊆ Λ.volume n
  · have heq :
        (fun J' => correlationAlongExhaustion G Λ
              (⟨J', h, β⟩ : IsingParams ℝ) A n) =
        (fun J' => IsingModel.correlation (inducedGraph G (Λ.volume n))
              (⟨J', h, β⟩ : IsingParams ℝ) (liftFinset A h_sub)) := by
      funext J'
      rw [correlationAlongExhaustion_of_subset G Λ _ h_sub, correlationΛ_apply]
    rw [heq]
    exact ⟨_, IsingModel.hasDerivAt_correlation_J _ J h β _⟩
  · have heq :
        (fun J' => correlationAlongExhaustion G Λ
              (⟨J', h, β⟩ : IsingParams ℝ) A n) = fun _ => 0 := by
      funext J'
      exact correlationAlongExhaustion_of_not_subset G Λ _ h_sub
    rw [heq]
    exact ⟨0, hasDerivAt_const J 0⟩

/-- **J-derivative of `magnetizationAlongExhaustion`** (GJ §17.5):
The function `fun J' => magnetizationAlongExhaustion G Λ ⟨J', h, β⟩ i n`
has a derivative at `J`.

Direct specialization of `correlationAlongExhaustion_hasDerivAt_J` at
`A = {i}`, since `magnetizationAlongExhaustion = correlationAlongExhaustion`
at `A = {i}` by definition. -/
theorem magnetizationAlongExhaustion_hasDerivAt_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    ∃ d : ℝ, HasDerivAt
      (fun J' => magnetizationAlongExhaustion G Λ
          (⟨J', h, β⟩ : IsingParams ℝ) i n) d J := by
  unfold magnetizationAlongExhaustion
  exact correlationAlongExhaustion_hasDerivAt_J G Λ J h β {i} n

end IsingModel.Ambient

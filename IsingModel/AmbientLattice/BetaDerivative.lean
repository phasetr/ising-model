import IsingModel.AmbientLattice.Exhaustion
import IsingModel.BetaDerivative

/-!
# β-derivative of correlationAlongExhaustion (GJ §17.5)

Shows that for any graph G whose exhaustion stages have finite edge sets,
the function `fun β' => correlationAlongExhaustion G Λ ⟨J, 0, β'⟩ A n` has a derivative at β.

When `A ⊆ Λ.volume n` the function reduces to the finite-volume correlation
(differentiable by `hasDerivAt_correlation_beta`); otherwise it is constant zero.

Step 156, GJ §17.5 (first step toward ∞-vol β-derivative). -/

namespace IsingModel.Ambient

variable {V : Type*} [DecidableEq V]

/-- **β-derivative of correlationAlongExhaustion** (Step 156, GJ §17.5):
The function `fun β' => correlationAlongExhaustion G Λ ⟨J, 0, β'⟩ A n` has a derivative at β.

Proof: split on `A ⊆ Λ.volume n`. In the subset case, unfold to the finite-volume correlation
on the induced graph and apply `hasDerivAt_correlation_beta`. In the non-subset case,
the function is constant zero, with derivative 0.

Reference: Glimm–Jaffe §17.5. -/
theorem correlationAlongExhaustion_hasDerivAt_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (A : Finset V) (n : ℕ) :
    ∃ d : ℝ, HasDerivAt
      (fun β' => correlationAlongExhaustion G Λ (⟨J, 0, β'⟩ : IsingParams ℝ) A n) d β := by
  by_cases h : A ⊆ Λ.volume n
  · -- Rewrite to the induced-graph correlation
    have heq : (fun β' => correlationAlongExhaustion G Λ (⟨J, 0, β'⟩ : IsingParams ℝ) A n) =
               (fun β' => IsingModel.correlation (inducedGraph G (Λ.volume n))
                    (⟨J, 0, β'⟩ : IsingParams ℝ) (liftFinset A h)) := by
      funext β'
      rw [correlationAlongExhaustion_of_subset G Λ _ h, correlationΛ_apply]
    rw [heq]
    exact ⟨_, hasDerivAt_correlation_beta _ J β _⟩
  · -- Function is constant zero
    have heq : (fun β' => correlationAlongExhaustion G Λ (⟨J, 0, β'⟩ : IsingParams ℝ) A n) =
               fun _ => 0 := by
      funext β'
      exact correlationAlongExhaustion_of_not_subset G Λ _ h
    rw [heq]
    exact ⟨0, hasDerivAt_const β 0⟩

end IsingModel.Ambient

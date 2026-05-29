import IsingModel.AmbientLattice.Exhaustion

/-!
# Covered-stage correlationAlongExhaustion derivative identity (Issue #3026)

On a covered exhaustion stage (`A ⊆ Λ.volume n`), the exhaustion correlation
`correlationAlongExhaustion G Λ p A n` is, by definition, the induced-graph correlation
`correlation (inducedGraph G (Λ.volume n)) p (liftFinset A …)`. Since the coverage
condition does not depend on the inverse temperature `β`, the same identity holds for the
`β`-dependent family, hence for its `β`-derivative.

This rewrites the GJ §17.5 Lemma 17.5.2 capstone `hincr` — phrased with
`deriv (correlationAlongExhaustion …)` — into the bare induced-graph correlation
derivatives on the cubic boxes, the form on which the Cauchy-estimate derivative-increment
bridge (`dist_deriv_correlation_le_of_complex_circle_bound`, Issue #3026) operates.

References:

* Glimm–Jaffe, *Quantum Physics* (2nd ed.), §17.5, Lemma 17.5.2, pp. 311–312.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Covered-stage exhaustion correlation is the induced-graph correlation** (Issue
#3026). For `A ⊆ Λ.volume n`, `correlationAlongExhaustion G Λ p A n` equals
`correlation (inducedGraph G (Λ.volume n)) p (liftFinset A …)`. Unfolds the
`A ⊆ Λ.volume n` branch (`dif_pos`) of `correlationAlongExhaustion`, with `correlationΛ`
definitionally the induced-graph correlation. -/
theorem correlationAlongExhaustion_eq_correlation_inducedGraph (G : SimpleGraph V)
    (Λ : Exhaustion V) [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (A : Finset V) (n : ℕ) (hcov : A ⊆ Λ.volume n) :
    correlationAlongExhaustion G Λ p A n
      = correlation (inducedGraph G (Λ.volume n)) p (liftFinset A hcov) := by
  unfold correlationAlongExhaustion
  rw [dif_pos hcov]
  rfl

/-- **Covered-stage exhaustion correlation derivative is the induced-graph correlation
derivative** (Issue #3026). Since the coverage condition `A ⊆ Λ.volume n` is independent
of `β`, the `β`-family `fun β' => correlationAlongExhaustion G Λ ⟨J,h,β'⟩ A n` agrees with
`fun β' => correlation (inducedGraph G (Λ.volume n)) ⟨J,h,β'⟩ (liftFinset A …)`
everywhere, hence so do their `β`-derivatives. -/
theorem deriv_correlationAlongExhaustion_eq_inducedGraph (G : SimpleGraph V)
    (Λ : Exhaustion V) [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (A : Finset V) (n : ℕ) (hcov : A ⊆ Λ.volume n) (β : ℝ) :
    deriv (fun β' => correlationAlongExhaustion G Λ (⟨J, h, β'⟩ : IsingParams ℝ) A n) β
      = deriv (fun β' => correlation (inducedGraph G (Λ.volume n))
          (⟨J, h, β'⟩ : IsingParams ℝ) (liftFinset A hcov)) β := by
  have hfun : (fun β' => correlationAlongExhaustion G Λ (⟨J, h, β'⟩ : IsingParams ℝ) A n)
      = (fun β' => correlation (inducedGraph G (Λ.volume n))
          (⟨J, h, β'⟩ : IsingParams ℝ) (liftFinset A hcov)) :=
    funext fun β' =>
      correlationAlongExhaustion_eq_correlation_inducedGraph G Λ _ A n hcov
  rw [hfun]

/-- **`HasDerivAt` for the covered-stage exhaustion correlation in `β`** (Issue
#3026). Companion to `deriv_correlationAlongExhaustion_eq_inducedGraph`: if the
β-family of the induced-graph correlation has a derivative at `β`, then the
β-family of `correlationAlongExhaustion` has the *same* derivative there. -/
theorem hasDerivAt_correlationAlongExhaustion_of_hasDerivAt_inducedGraph
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (A : Finset V) (n : ℕ) (hcov : A ⊆ Λ.volume n)
    {β dval : ℝ}
    (h_ind : HasDerivAt
        (fun β' => correlation (inducedGraph G (Λ.volume n))
          (⟨J, h, β'⟩ : IsingParams ℝ) (liftFinset A hcov)) dval β) :
    HasDerivAt
      (fun β' => correlationAlongExhaustion G Λ (⟨J, h, β'⟩ : IsingParams ℝ) A n) dval β := by
  have hfun : (fun β' => correlationAlongExhaustion G Λ (⟨J, h, β'⟩ : IsingParams ℝ) A n)
      = (fun β' => correlation (inducedGraph G (Λ.volume n))
          (⟨J, h, β'⟩ : IsingParams ℝ) (liftFinset A hcov)) :=
    funext fun β' =>
      correlationAlongExhaustion_eq_correlation_inducedGraph G Λ _ A n hcov
  rw [hfun]; exact h_ind

/-- **`HasDerivAt` for the covered-stage exhaustion correlation in `J`** (Issue
#3026, J-direction parallel). Companion to
`hasDerivAt_correlationAlongExhaustion_of_hasDerivAt_inducedGraph`: if the
J-family of the induced-graph correlation has a derivative at `J`, then the
J-family of `correlationAlongExhaustion` has the *same* derivative there. The
coverage condition is independent of `J`, so the function-level identity
passes through `HasDerivAt`. -/
theorem hasDerivAt_correlationAlongExhaustion_J_of_hasDerivAt_inducedGraph
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ) (A : Finset V) (n : ℕ) (hcov : A ⊆ Λ.volume n)
    {J dval : ℝ}
    (h_ind : HasDerivAt
        (fun J' => correlation (inducedGraph G (Λ.volume n))
          (⟨J', h, β⟩ : IsingParams ℝ) (liftFinset A hcov)) dval J) :
    HasDerivAt
      (fun J' => correlationAlongExhaustion G Λ (⟨J', h, β⟩ : IsingParams ℝ) A n) dval J := by
  have hfun : (fun J' => correlationAlongExhaustion G Λ (⟨J', h, β⟩ : IsingParams ℝ) A n)
      = (fun J' => correlation (inducedGraph G (Λ.volume n))
          (⟨J', h, β⟩ : IsingParams ℝ) (liftFinset A hcov)) :=
    funext fun J' =>
      correlationAlongExhaustion_eq_correlation_inducedGraph G Λ _ A n hcov
  rw [hfun]; exact h_ind

end Ambient
end IsingModel

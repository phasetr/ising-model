import IsingModel.BallBoundarySimonLieb.ScaledGKS

/-!
# Ball-boundary Simon-Lieb scaled monotonicity wrappers

Monotonicity layer for the ball-boundary Simon-Lieb inequality.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Monotonicity in s -/

/-- The derivative of `scaledCorrelation G E₀ p s A` in `s` is non-negative for
ferromagnetic params, `s ≥ 0`, `E₀ ⊆ G.edgeFinset`, and non-diagonal `E₀`. -/
theorem scaledCorrelation_deriv_nonneg' (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (hE₀_nd : ∀ e ∈ E₀, ¬e.IsDiag)
    (hE₀_sub : E₀ ⊆ G.edgeFinset)
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (s : ℝ) (hs : 0 ≤ s) (A : Finset ι) :
    0 ≤ p.β * p.J * ∑ e ∈ E₀,
      Sym2.lift ⟨fun u v =>
        scaledCorrelation G E₀ p s (symmDiff A {u, v}) -
        scaledCorrelation G E₀ p s A * scaledCorrelation G E₀ p s {u, v},
      fun u v => by simp [Finset.pair_comm v u]⟩ e := by
  apply mul_nonneg (mul_nonneg hf.hβ.le hf.hJ)
  apply Finset.sum_nonneg; intro e he
  obtain ⟨⟨u, v⟩, rfl⟩ := Quot.exists_rep e
  simp only [Sym2.lift_mk]
  have huv : u ≠ v := by
    intro h; subst h; exact hE₀_nd _ he (Sym2.mk_isDiag_iff.mpr rfl)
  linarith [scaledCorrelation_gks_second G E₀ hE₀_sub p hf s hs A {u, v}]

/-- **Monotonicity of scaled correlation in `s`**: for ferromagnetic params and `0 ≤ s₁ ≤ s₂`,
`⟨σ^A⟩_{s₁} ≤ ⟨σ^A⟩_{s₂}`. -/
theorem scaledCorrelation_monotoneOn (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (hE₀_nd : ∀ e ∈ E₀, ¬e.IsDiag)
    (hE₀_sub : E₀ ⊆ G.edgeFinset)
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset ι) :
    MonotoneOn (fun s => scaledCorrelation G E₀ p s A) (Set.Ici 0) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
  · intro s _
    exact (hasDerivAt_scaledCorrelation G E₀ hE₀_nd p s A).continuousAt.continuousWithinAt
  · intro s hs
    rw [interior_Ici] at hs ⊢
    exact (hasDerivAt_scaledCorrelation G E₀ hE₀_nd p s A).hasDerivWithinAt
  · intro s hs
    rw [interior_Ici] at hs
    exact scaledCorrelation_deriv_nonneg' G E₀ hE₀_nd hE₀_sub p hf s hs.le A


end IsingModel

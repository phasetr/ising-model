import IsingModel.BetaDerivative.FreeEnergy

/-!
# Monotonicity in beta

This module contains the GKS-II beta-monotonicity wrappers split from
`IsingModel.BetaDerivative`.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Monotonicity in β (Step 122): GKS-II-based bound -/

/-- The β-derivative of two-point correlations is nonneg (infinitesimal form of β-monotonicity).

`d/dβ ⟨σ^A⟩_β = J · Σ_e (⟨σ^{AΔe}⟩ − ⟨σ^A⟩·⟨σ^e⟩) ≥ 0`

by GKS-II: each term `⟨σ^{AΔe}⟩ − ⟨σ^A⟩·⟨σ^e⟩ ≥ 0` for ferromagnetic `h = 0`.
This is the infinitesimal form underlying the monotonicity of correlations in β.

Reference: Friedli–Velenik §3.7, Lemma 3.31 part 2 (p. 107) — adapted to general `σ^A`;
Glimm–Jaffe §17.5 pp. 345–347. -/
theorem correlation_beta_deriv_nonneg
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (A : Finset ι)
    (hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ)) :
    0 ≤ J * ∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun r s =>
          correlation G (⟨J, 0, β⟩ : IsingParams ℝ) (symmDiff A {r, s}) -
          correlation G (⟨J, 0, β⟩ : IsingParams ℝ) A *
          correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {r, s},
          fun r s => by simp [Finset.pair_comm s r]⟩ e := by
  apply mul_nonneg hf.hJ
  apply Finset.sum_nonneg
  intro e _
  obtain ⟨⟨r, s⟩, rfl⟩ := Quot.exists_rep e
  simp only [Sym2.lift_mk]
  linarith [gks_second G (⟨J, 0, β⟩ : IsingParams ℝ) hf A {r, s}]

/-- **Correlations are monotone in β** (on `{β ≥ 0}`):
`β₁ ≤ β₂ → correlation G (⟨J, 0, β₁⟩) A ≤ correlation G (⟨J, 0, β₂⟩) A`

for ferromagnetic coupling `J ≥ 0`.

Proof: mean value theorem applied to `β ↦ correlation` whose derivative
is nonneg by GKS-II (`correlation_beta_deriv_nonneg`).

Reference: Friedli–Velenik §3.7, Lemma 3.31 part 2 (p. 107);
Glimm–Jaffe §17.5 pp. 345–347. -/
theorem correlation_monotoneOn_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (A : Finset ι) :
    MonotoneOn (fun β => correlation G (⟨J, 0, β⟩ : IsingParams ℝ) A) (Set.Ici 0) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
  · -- ContinuousOn: from HasDerivAt ⇒ ContinuousAt ⇒ ContinuousWithinAt
    intro β _
    exact (hasDerivAt_correlation_beta G J β A).continuousAt.continuousWithinAt
  · -- HasDerivWithinAt on interior (Ici 0) = Ioi 0
    intro β hβ
    rw [interior_Ici] at hβ ⊢
    exact (hasDerivAt_correlation_beta G J β A).hasDerivWithinAt
  · -- derivative ≥ 0 on interior
    intro β hβ
    rw [interior_Ici] at hβ
    exact correlation_beta_deriv_nonneg G J β A ⟨hJ, le_refl 0, hβ⟩


end IsingModel

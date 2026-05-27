import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.DerivativeLimitProviderFiniteProfile

/-!
# Explicit β-derivative increment formula on covered stages (Issue #2965, Phase C)

On two consecutive exhaustion stages `k ⊆ k+1` that both contain the target pair
`{x,z}`, the β-derivative increment `F_{k+1}(β) − F_k(β)` of the finite-volume
two-point profiles is the difference of the two finite Lebowitz/Ursell edge sums
(`lemma_17_5_2_finite_derivative_profile_eq_beta_edge_sum` applied at `k` and
`k+1`).

Stated for an arbitrary exhaustion `Λ` (RHS over `Λ.volume k`, `Λ.volume (k+1)`).
This is the explicit starting point for the per-stage β-derivative increment bound
required by the GJ §17.5 Lemma 17.5.2 capstone: the difference splits algebraically
into the edges new to stage `k+1` and the edges shared with stage `k`. For the
cubic exhaustion specifically, the new edges form a shell far from `{x,z}` (so their
Ursell terms decay) and the shared interior edges' Ursell terms differ only by the
inter-stage correlation differences — but that geometric interpretation is the
intended later specialization, not part of this general formula.

## Main declaration

* `IsingModel.Ambient.lemma_17_5_2_finite_derivative_increment_eq`.
-/

namespace IsingModel
namespace Ambient

open scoped symmDiff

/-- **Explicit β-derivative increment on covered stages** (Issue #2965, Phase C):
for consecutive stages `k ⊆ k+1` both containing `{x,z}`, the β-derivative
increment of the finite-volume two-point profiles equals the difference of the
stage-`k+1` and stage-`k` finite Ursell edge sums. Immediate from the
finite-derivative-profile formula `lemma_17_5_2_finite_derivative_profile_eq_beta_edge_sum`
at both stages. -/
theorem lemma_17_5_2_finite_derivative_increment_eq
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) {k : ℕ}
    (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k)
    (hk1 : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume (k + 1)) (β : ℝ) :
    deriv (fun β' =>
        Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} (k + 1)) β
      - deriv (fun β' =>
          Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} k) β
      = (J * ∑ e ∈ (inducedGraph (IsingModel.latticeGraph d) (Λ.volume (k + 1))).edgeFinset,
            Sym2.lift ⟨fun u v =>
              IsingModel.correlation (inducedGraph (IsingModel.latticeGraph d) (Λ.volume (k + 1)))
                  (⟨J, 0, β⟩ : IsingParams ℝ)
                  (symmDiff (liftFinset ({x, z} : Finset _) hk1) {u, v}) -
                IsingModel.correlation (inducedGraph (IsingModel.latticeGraph d) (Λ.volume (k + 1)))
                  (⟨J, 0, β⟩ : IsingParams ℝ) (liftFinset ({x, z} : Finset _) hk1) *
                IsingModel.correlation (inducedGraph (IsingModel.latticeGraph d) (Λ.volume (k + 1)))
                  (⟨J, 0, β⟩ : IsingParams ℝ) {u, v},
              fun u v => by simp [Finset.pair_comm v u]⟩ e)
        - (J * ∑ e ∈ (inducedGraph (IsingModel.latticeGraph d) (Λ.volume k)).edgeFinset,
            Sym2.lift ⟨fun u v =>
              IsingModel.correlation (inducedGraph (IsingModel.latticeGraph d) (Λ.volume k))
                  (⟨J, 0, β⟩ : IsingParams ℝ)
                  (symmDiff (liftFinset ({x, z} : Finset _) hk) {u, v}) -
                IsingModel.correlation (inducedGraph (IsingModel.latticeGraph d) (Λ.volume k))
                  (⟨J, 0, β⟩ : IsingParams ℝ) (liftFinset ({x, z} : Finset _) hk) *
                IsingModel.correlation (inducedGraph (IsingModel.latticeGraph d) (Λ.volume k))
                  (⟨J, 0, β⟩ : IsingParams ℝ) {u, v},
              fun u v => by simp [Finset.pair_comm v u]⟩ e) := by
  rw [lemma_17_5_2_finite_derivative_profile_eq_beta_edge_sum Λ J x z hk1 β,
    lemma_17_5_2_finite_derivative_profile_eq_beta_edge_sum Λ J x z hk β]

end Ambient
end IsingModel

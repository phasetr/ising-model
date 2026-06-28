import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.CubicIncidentInfiniteBridge

/-!
# GJ §17.5 Theorem 17.5.1 — PR-1i: finite ≤ infinite cross-sum bridge (p.312)

The finite-volume c-cancelling Lebowitz cross-sum (from #4340
`derivative_profile_cubic_le_lebowitz_cancelling`, with **finite** induced-graph factors) is bounded
termwise by the **infinite-volume** cross-sum (#4347's input form).  Each finite cross product is
dominated by its infinite-volume value (`correlation_inducedGraph_cubic_le_correlationInfinite`);
products monotone since correlations are non-negative.

This bridge lets the `hcomp` combine use the **finite** deriv bound #4340 (whose incident term is
the tight finite reduced correlation handled by #4344) while routing its cross-sum through the
**infinite** convolution machinery (#4347 + #4350).

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, p.~312.
-/

namespace IsingModel
namespace Ambient

open Finset

/-- **Finite ≤ infinite cross-sum bridge** (GJ p.312): the finite-volume Lebowitz cross-sum (with
induced-graph correlation factors `⟨φ_{⟨x⟩} φ_u⟩_{box}`) is bounded termwise by the infinite-volume
cross-sum (`⟨φ_x φ_{u.val}⟩^∞`).  Per edge, each factor is dominated by its infinite-volume value
(`correlation_inducedGraph_cubic_le_correlationInfinite`) and the products are monotone
(`mul_le_mul`, correlations non-negative). -/
theorem cross_sum_finite_le_infinite (d : ℕ) (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {n : ℕ} {x z : Fin d → ℤ} (hx : x ∈ (cubicExhaustion d).volume n)
    (hz : z ∈ (cubicExhaustion d).volume n) :
    ∑ e ∈ (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n)).edgeFinset,
        Sym2.lift ⟨fun u v =>
            correlation (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n))
                (⟨J, 0, β⟩ : IsingParams ℝ)
                {⟨x, hx⟩, u} *
              correlation (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n))
                (⟨J, 0, β⟩ : IsingParams ℝ) {⟨z, hz⟩, v} +
            correlation (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n))
                (⟨J, 0, β⟩ : IsingParams ℝ) {⟨x, hx⟩, v} *
              correlation (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n))
                (⟨J, 0, β⟩ : IsingParams ℝ) {⟨z, hz⟩, u},
          fun u v => by ring⟩ e
      ≤ ∑ e ∈ (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n)).edgeFinset,
          Sym2.lift ⟨fun u v =>
              Ambient.correlationInfinite (latticeGraph d) (cubicExhaustion d)
                  (⟨J, 0, β⟩ : IsingParams ℝ) {x, u.val} *
                Ambient.correlationInfinite (latticeGraph d) (cubicExhaustion d)
                  (⟨J, 0, β⟩ : IsingParams ℝ) {z, v.val} +
              Ambient.correlationInfinite (latticeGraph d) (cubicExhaustion d)
                  (⟨J, 0, β⟩ : IsingParams ℝ) {x, v.val} *
                Ambient.correlationInfinite (latticeGraph d) (cubicExhaustion d)
                  (⟨J, 0, β⟩ : IsingParams ℝ) {z, u.val},
            fun u v => by ring⟩ e := by
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ, le_refl 0, hβ⟩
  apply Finset.sum_le_sum
  intro e _he
  obtain ⟨⟨u, v⟩, rfl⟩ := Quot.exists_rep e
  simp only [Sym2.lift_mk]
  have bxu := correlation_inducedGraph_cubic_le_correlationInfinite d
    (⟨J, 0, β⟩ : IsingParams ℝ) n ⟨x, hx⟩ u
  have bzv := correlation_inducedGraph_cubic_le_correlationInfinite d
    (⟨J, 0, β⟩ : IsingParams ℝ) n ⟨z, hz⟩ v
  have bxv := correlation_inducedGraph_cubic_le_correlationInfinite d
    (⟨J, 0, β⟩ : IsingParams ℝ) n ⟨x, hx⟩ v
  have bzu := correlation_inducedGraph_cubic_le_correlationInfinite d
    (⟨J, 0, β⟩ : IsingParams ℝ) n ⟨z, hz⟩ u
  exact add_le_add
    (mul_le_mul bxu bzv (gks_first _ _ hf _) (correlationInfinite_nonneg _ _ _ hf _))
    (mul_le_mul bxv bzu (gks_first _ _ hf _) (correlationInfinite_nonneg _ _ _ hf _))

end Ambient
end IsingModel

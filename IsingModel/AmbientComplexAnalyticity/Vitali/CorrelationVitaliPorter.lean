import IsingModel.AmbientComplexAnalyticity.Vitali.CorrelationPerStageHolomorphic
import IsingModel.ComplexAnalyticity.FunctionTheoryAxioms

/-!
# Applying Vitali–Porter to the complex along-exhaustion correlation (GJ §18.6/§18.7)

Third step of the infinite-volume two-point correlation-analyticity programme (Issue #4230, item D
of #4214).  Consumes the isolated **Vitali–Porter** function-theory axiom
(`IsingModel/ComplexAnalyticity/FunctionTheoryAxioms.lean`) to turn the **Ising-side** inputs into
the locally-uniform convergence of the per-stage complex correlations.

The per-stage complex correlations are holomorphic on a high-temperature open set `U` once the
complex partition function is nonvanishing there
(`correlationComplexAlongExhaustion_differentiableOn_of_ne_zero`, PR #4232).  Given, in addition, a
**volume-uniform bound** on those correlations on `U` (the Ising-side cluster-expansion input, to be
proven separately) and their **pointwise convergence** on a
subset `S ⊆ U` with an accumulation point in `U` (supplied on the real axis by
`correlationComplexAlongExhaustion_tendsto_at_real`), the Vitali–Porter axiom yields a holomorphic
limit `f` on `U` with locally uniform convergence — exactly the `hconv` consumed by
`correlationComplexAlongExhaustion_vitali_identified_at_real_of_ne_zero`.

## Main result
* `correlationComplexAlongExhaustion_analytic_limit_of_volume_uniform` — from per-stage
  non-vanishing + a volume-uniform bound + pointwise convergence on `S` (accumulation point in `U`),
  there is a holomorphic limit `f` with `TendstoLocallyUniformlyOn … f`, agreeing with the pointwise
  limit on `S`.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §18.6–18.7.
-/

namespace IsingModel

namespace Ambient

open Filter Topology

variable {V : Type*} [DecidableEq V]

/-- **Vitali–Porter applied to the along-exhaustion complex correlation**: from
* the volume-uniform partition non-vanishing on an open preconnected `U` (giving per-stage
  holomorphicity, `correlationComplexAlongExhaustion_differentiableOn_of_ne_zero`),
* a volume-uniform bound on the per-stage complex correlations on `U` (the Ising-side
  cluster-expansion input), and
* pointwise convergence of the per-stage correlations on a subset `S ⊆ U` with an accumulation point
  `z₀ ∈ U`,

the isolated **Vitali–Porter** function-theory axiom yields a holomorphic limit `f` on `U` with
locally uniform convergence and `f = g` on `S`.  The locally-uniform convergence is exactly the
`hconv` consumed by `correlationComplexAlongExhaustion_vitali_identified_at_real_of_ne_zero`. -/
theorem correlationComplexAlongExhaustion_analytic_limit_of_volume_uniform
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (A : Finset V) (J h : ℂ) {U : Set ℂ} (hU : IsOpen U) (hUconn : IsPreconnected U)
    (hZ : ∀ n, ∀ β ∈ U,
      partitionFunctionComplexAlongExhaustion G Λ J h β n ≠ 0)
    (hbdd : ∀ z ∈ U, ∃ r M : ℝ, 0 < r ∧ Metric.ball z r ⊆ U ∧
      ∀ n, ∀ w ∈ Metric.ball z r,
        ‖correlationComplexAlongExhaustion G Λ A J h w n‖ ≤ M)
    {S : Set ℂ} (hSU : S ⊆ U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hacc : AccPt z₀ (Filter.principal S))
    {g : ℂ → ℂ}
    (hpt : ∀ z ∈ S, Filter.Tendsto
      (fun n => correlationComplexAlongExhaustion G Λ A J h z n) Filter.atTop (nhds (g z))) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧
      TendstoLocallyUniformlyOn
        (fun n β => correlationComplexAlongExhaustion G Λ A J h β n) f Filter.atTop U ∧
      Set.EqOn f g S :=
  FunctionTheory.vitaliPorter_tendstoLocallyUniformlyOn hU hUconn
    (fun n => correlationComplexAlongExhaustion_differentiableOn_of_ne_zero G Λ A J h hZ n)
    hbdd hSU hz₀ hacc hpt

end Ambient

end IsingModel

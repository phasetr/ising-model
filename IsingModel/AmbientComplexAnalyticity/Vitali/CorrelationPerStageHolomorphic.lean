import IsingModel.AmbientComplexAnalyticity.Vitali.CorrelationBridge

/-!
# Per-stage holomorphicity of the complex along-exhaustion correlation (GJ §18.6/§18.7)

Discharges the per-stage differentiability hypothesis `hF` of the conditional correlation Vitali
bridge (`AmbientComplexAnalyticity/Vitali/CorrelationBridge.lean`, Issue #4230 PR 1) from a
**volume-uniform non-vanishing** of the complex partition function — the second PR of the
infinite-volume correlation-analyticity programme (Issue #4230, item D of #4214).

The finite-volume complex correlation `correlationComplex` is analytic in `β` wherever the complex
partition function is nonzero (`correlationComplex_analyticAt_beta`).  Hence, on any open set `U`
where the along-exhaustion complex partition function is nonvanishing for every stage `n`, the
per-stage complex along-exhaustion correlation is holomorphic — exactly the `hF` input of the Vitali
bridge.  The (volume-uniform) partition-function non-vanishing on a high-temperature disc is
available from `AmbientComplexAnalyticity/VolumeUniformHZ.lean`
(`volume_uniform_Z_ne_zero_of_HT_bound_and_identity` etc.) under the cluster-expansion bound
hypotheses.

## Main results
* `correlationComplexAlongExhaustion_differentiableOn_of_ne_zero` — per-stage holomorphicity on an
  open `U` from the along-exhaustion partition non-vanishing on `U`.
* `correlationComplexAlongExhaustion_vitali_identified_at_real_of_ne_zero` — the conditional Vitali
  assembly with the `hF` hypothesis discharged: only the locally uniform convergence `hconv` (the
  Montel input) and the partition non-vanishing remain.

The remaining input — locally uniform convergence of the per-stage complex correlations on the disc,
from a volume-uniform (Montel) bound — is the genuine research-level core, deferred to follow-up PRs
(Issue #4230).

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §18.6–18.7.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Per-stage holomorphicity of the complex along-exhaustion correlation**: on an open set `U`
where the along-exhaustion complex partition function is nonvanishing at every stage `n`, the
per-stage complex correlation `β ↦ correlationComplexAlongExhaustion G Λ A J h β n` is holomorphic
on `U`.  This discharges the per-stage differentiability hypothesis `hF` of
`correlationComplexAlongExhaustion_vitali_bridge`.

Stage `n` is either the finite-volume complex correlation `correlationComplex` on the induced
subgraph — analytic in `β` where the partition function is nonzero
(`correlationComplex_analyticAt_beta`) — once `A ⊆ Λ.volume n`, or the constant `0` before. -/
theorem correlationComplexAlongExhaustion_differentiableOn_of_ne_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (A : Finset V) (J h : ℂ) {U : Set ℂ}
    (hZ : ∀ n, ∀ β ∈ U,
      partitionFunctionComplexAlongExhaustion G Λ J h β n ≠ 0)
    (n : ℕ) :
    DifferentiableOn ℂ
      (fun β => correlationComplexAlongExhaustion G Λ A J h β n) U := by
  by_cases hsub : A ⊆ Λ.volume n
  · have hfun : (fun β => correlationComplexAlongExhaustion G Λ A J h β n)
        = fun β => correlationComplex (inducedGraph G (Λ.volume n)) (liftFinset A hsub) J h β := by
      funext β
      unfold correlationComplexAlongExhaustion
      simp only [hsub, dif_pos]
    rw [hfun]
    intro β hβ
    have hZn : partitionFunctionComplex (inducedGraph G (Λ.volume n)) J h β ≠ 0 := by
      have hZn' := hZ n β hβ
      rwa [partitionFunctionComplexAlongExhaustion_apply] at hZn'
    exact ((correlationComplex_analyticAt_beta (inducedGraph G (Λ.volume n))
      (liftFinset A hsub) J h β hZn).differentiableAt).differentiableWithinAt
  · have hfun : (fun β => correlationComplexAlongExhaustion G Λ A J h β n)
        = fun _ => (0 : ℂ) := by
      funext β
      unfold correlationComplexAlongExhaustion
      simp only [hsub, dif_neg, not_false_iff]
    rw [hfun]
    exact differentiableOn_const 0

/-- **Conditional Vitali assembly with the per-stage differentiability discharged**
(GJ §18.6/§18.7): if the along-exhaustion complex partition function is nonvanishing on an open `U`
at every stage
and the per-stage complex correlations converge locally uniformly to `f` on `U`, then `f` is
holomorphic on `U` and, on the real axis, equals the real infinite-volume correlation
`correlationInfinite`.  Strengthens `correlationComplexAlongExhaustion_vitali_identified_at_real` by
deriving its `hF` hypothesis from the partition non-vanishing
(`correlationComplexAlongExhaustion_differentiableOn_of_ne_zero`).

Only the locally uniform convergence `hconv` (the Montel / volume-uniform input, deferred to
follow-up PRs of Issue #4230) and the partition non-vanishing remain as hypotheses. -/
theorem correlationComplexAlongExhaustion_vitali_identified_at_real_of_ne_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset V)
    {U : Set ℂ} (hU : IsOpen U)
    (hZ : ∀ n, ∀ β ∈ U,
      partitionFunctionComplexAlongExhaustion G Λ (p.J : ℂ) (p.h : ℂ) β n ≠ 0)
    (hβ : (p.β : ℂ) ∈ U) {f : ℂ → ℂ}
    (hconv : TendstoLocallyUniformlyOn
      (fun n β => correlationComplexAlongExhaustion G Λ A (p.J : ℂ) (p.h : ℂ) β n)
      f Filter.atTop U) :
    DifferentiableOn ℂ f U ∧ f (p.β : ℂ) = ((correlationInfinite G Λ p A : ℝ) : ℂ) :=
  correlationComplexAlongExhaustion_vitali_identified_at_real G Λ p hf A hU hβ
    (fun n => correlationComplexAlongExhaustion_differentiableOn_of_ne_zero
      G Λ A (p.J : ℂ) (p.h : ℂ) hZ n)
    hconv

end Ambient

end IsingModel

import IsingModel.AmbientComplexAnalyticity.Vitali.Bridge
import IsingModel.ComplexAnalyticity.Correlation

/-!
# Conditional Vitali assembly for the infinite-volume two-point correlation (GJ §18.6/§18.7)

The along-exhaustion analogue of the free-energy Vitali bridges
(`AmbientComplexAnalyticity/Vitali/Bridge.lean`), for the **two-point correlation**.  First PR of
the infinite-volume correlation-analyticity programme (Issue #4230, item D of #4214).

The finite-volume complex correlation `correlationComplex` is analytic in the inverse temperature
`β` wherever the complex partition function is nonzero (`correlationComplex_analyticAt_beta`), and
on the real axis it reduces to the real correlation (`correlation_ofReal_eq_correlationComplex`).
Bundling
these along an exhaustion `Λ ↑ V`, this module records the **conditional Vitali assembly**: given a
locally uniform limit `f` of the per-stage complex correlations on an open set `U` (the genuine hard
input — a volume-uniform/Montel bound, deferred to a follow-up PR), `f` is holomorphic on `U` and,
on the real axis, equals the real infinite-volume correlation `correlationInfinite`.

## Main results
* `correlationComplexAlongExhaustion` — the per-stage complex two-point correlation along the
  exhaustion (`= 0` before the observable's support is engulfed, mirroring
  `correlationAlongExhaustion`).
* `correlationComplexAlongExhaustion_at_real_eq_ofReal` — at real parameters it is the `ofReal` of
  the real `correlationAlongExhaustion`.
* `correlationComplexAlongExhaustion_tendsto_at_real` — pointwise convergence to
  `(correlationInfinite : ℂ)` at real parameters (ferromagnetic).
* `correlationComplexAlongExhaustion_vitali_bridge` — Vitali: a locally uniform limit of the
  per-stage-holomorphic correlations is holomorphic on `U`.
* `correlationComplexAlongExhaustion_limit_eq_correlationInfinite_at_real` — the limit agrees with
  `(correlationInfinite : ℂ)` at the real parameter point.
* `correlationComplexAlongExhaustion_vitali_identified_at_real` — the combined statement.

The remaining input — locally uniform convergence of the per-stage complex correlations on a
high-temperature disc, from a volume-uniform cluster-expansion bound (Montel) — is the genuine
research-level core, deferred to follow-up PRs (Issue #4230).

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §18.6–18.7.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Complex two-point correlation along an exhaustion**: the finite-volume complex correlation
`correlationComplex` on the induced subgraph of the stage-`n` volume, evaluated on the lifted
observable `liftFinset A` once `A ⊆ Λ.volume n` (and `0` before).  The complex-parameter analogue of
`correlationAlongExhaustion`. -/
noncomputable def correlationComplexAlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (A : Finset V) (J h β : ℂ) : ℕ → ℂ :=
  fun n =>
    if hsub : A ⊆ Λ.volume n then
      correlationComplex (inducedGraph G (Λ.volume n)) (liftFinset A hsub) J h β
    else 0

/-- **Real-axis reduction**: at real parameters the complex along-exhaustion correlation is the
`ofReal` of the real `correlationAlongExhaustion`, stage by stage (mirrors
`freeEnergyComplexAlongExhaustion_at_real_eq_ofReal`). -/
theorem correlationComplexAlongExhaustion_at_real_eq_ofReal
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (A : Finset V) (n : ℕ) :
    correlationComplexAlongExhaustion G Λ A (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) n
      = ((correlationAlongExhaustion G Λ p A n : ℝ) : ℂ) := by
  unfold correlationComplexAlongExhaustion correlationAlongExhaustion
  by_cases hsub : A ⊆ Λ.volume n
  · simp only [hsub, dif_pos]
    rw [correlationΛ_apply,
      ← correlation_ofReal_eq_correlationComplex (inducedGraph G (Λ.volume n)) p
        (liftFinset A hsub)]
  · simp only [hsub, dif_neg, not_false_iff, Complex.ofReal_zero]

/-- **Pointwise real-axis convergence** of the complex along-exhaustion correlation to the real
infinite-volume correlation `correlationInfinite` (ferromagnetic parameters): the analogue of
`freeEnergyComplexAlongExhaustion_tendsto_at_real_of_disjointTowerHypotheses`. -/
theorem correlationComplexAlongExhaustion_tendsto_at_real
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset V) :
    Filter.Tendsto
      (fun n => correlationComplexAlongExhaustion G Λ A
        (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) n)
      Filter.atTop
      (nhds ((correlationInfinite G Λ p A : ℝ) : ℂ)) := by
  have h_eq : (fun n => correlationComplexAlongExhaustion G Λ A
        (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) n)
      = fun n => ((correlationAlongExhaustion G Λ p A n : ℝ) : ℂ) := by
    funext n
    exact correlationComplexAlongExhaustion_at_real_eq_ofReal G Λ p A n
  rw [h_eq]
  exact (Complex.continuous_ofReal.tendsto _).comp
    (tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf A)

/-- **Conditional Vitali bridge** for the complex along-exhaustion correlation: a locally uniform
limit on an open set `U` of the per-stage-holomorphic correlations is holomorphic on `U`.  Direct
specialization of `vitali_bridge`; the per-stage differentiability `hF` (where the complex partition
function is nonvanishing, via `correlationComplex_analyticAt_beta`) and the locally uniform
convergence `hconv` are supplied by the caller. -/
theorem correlationComplexAlongExhaustion_vitali_bridge
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (A : Finset V) (J h : ℂ) {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ
      (fun β => correlationComplexAlongExhaustion G Λ A J h β n) U)
    (hconv : TendstoLocallyUniformlyOn
      (fun n β => correlationComplexAlongExhaustion G Λ A J h β n) f Filter.atTop U) :
    DifferentiableOn ℂ f U :=
  vitali_bridge hU hF hconv

/-- **Real-axis identification** of the Vitali limit: if the complex along-exhaustion correlation
(at real `J, h`, varying `β`) converges locally uniformly to `f` on an open set `U` containing the
real parameter `p.β`, then `f (p.β) = (correlationInfinite … : ℂ)`.  Mirrors
`freeEnergyComplexAlongExhaustion_limit_eq_freeEnergyInfinite_at_real`. -/
theorem correlationComplexAlongExhaustion_limit_eq_correlationInfinite_at_real
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset V)
    {U : Set ℂ} {f : ℂ → ℂ} (hβ : (p.β : ℂ) ∈ U)
    (hconv : TendstoLocallyUniformlyOn
      (fun n β => correlationComplexAlongExhaustion G Λ A (p.J : ℂ) (p.h : ℂ) β n)
      f Filter.atTop U) :
    f (p.β : ℂ) = ((correlationInfinite G Λ p A : ℝ) : ℂ) :=
  tendsto_nhds_unique (hconv.tendsto_at hβ)
    (correlationComplexAlongExhaustion_tendsto_at_real G Λ p hf A)

/-- **Conditional Vitali assembly with real-axis identification**: combines holomorphicity of the
locally uniform limit with its identification, on the real axis, by the real infinite-volume
correlation `correlationInfinite`.  The along-exhaustion correlation analogue of
`freeEnergyComplexAlongExhaustion_vitali_bridge_leeYangDomain_identified_at_real`. -/
theorem correlationComplexAlongExhaustion_vitali_identified_at_real
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset V)
    {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ} (hβ : (p.β : ℂ) ∈ U)
    (hF : ∀ n, DifferentiableOn ℂ
      (fun β => correlationComplexAlongExhaustion G Λ A (p.J : ℂ) (p.h : ℂ) β n) U)
    (hconv : TendstoLocallyUniformlyOn
      (fun n β => correlationComplexAlongExhaustion G Λ A (p.J : ℂ) (p.h : ℂ) β n)
      f Filter.atTop U) :
    DifferentiableOn ℂ f U ∧ f (p.β : ℂ) = ((correlationInfinite G Λ p A : ℝ) : ℂ) :=
  ⟨correlationComplexAlongExhaustion_vitali_bridge G Λ A (p.J : ℂ) (p.h : ℂ) hU hF hconv,
    correlationComplexAlongExhaustion_limit_eq_correlationInfinite_at_real G Λ p hf A hβ hconv⟩

end Ambient

end IsingModel

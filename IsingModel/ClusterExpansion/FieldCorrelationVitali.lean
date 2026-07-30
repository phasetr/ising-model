import IsingModel.ClusterExpansion.FieldCorrelationAlongExhaustion
import IsingModel.ComplexAnalyticity.VitaliPorter.Theorem
import IsingModel.Conditioning.CorrelationClosed.GeneralFieldClosedComplex
import IsingModel.AmbientLattice.CorrelationInfinite.Basic

/-!
# Field Vitali plumbing for the infinite-volume two-point correlation (GJ §17.6.1, brick F6a)

This file assembles the **conditional field Vitali/Montel local-limit plumbing** for
the infinite-volume two-point correlation, brick F6a.  It is the field
analogue of the `β`-route real-axis Vitali application
(`AmbientComplexAnalyticity/Vitali/CorrelationRealAxisVitali.lean`), obtained by
consuming the *family-agnostic* Vitali–Porter provider
`FunctionTheory.vitaliPorter_tendstoLocallyUniformlyOn`
(`ComplexAnalyticity/VitaliPorter/Theorem.lean`, proved, axiom-free, #4280) directly on
the field family `fun n b => fieldCorrelationℂAlongExhaustion G Λ A a b n`.  The `β`
Vitali stack is **not** modified — this is a new, field-specific thin glue, not an
abstraction refactor of the merged `β` bridges.

The varying complex parameter is the field `b` (`= β·h`); the coupling `a` (`= β·J`) is
held fixed.  On the real axis the complex field correlation reduces to the physical
correlation (F4b, `fieldCorrelationℂ_ofReal_eq_correlation`), so the pointwise limit is
supplied by the **existing** `correlationInfinite` mechanism — no new infinite-volume
object is introduced (F6 is plumbing, not a research core).

## Main results
* `fieldCorrelationℂAlongExhaustion_at_real_eq_ofReal` — at a real field `b`, the complex
  along-exhaustion field correlation is the `ofReal` of the real `correlationAlongExhaustion`
  at parameters `⟨a, b, 1⟩` (`β = 1`, `J = a`, `h = b`), stage by stage.
* `fieldCorrelationℂAlongExhaustion_tendsto_at_real` — at a nonnegative real field `b` with
  `0 ≤ a` (ferromagnetic), the per-stage complex field correlations converge to
  `↑(correlationInfinite G Λ ⟨a, b, 1⟩ A)`.
* `fieldCorrelationℂAlongExhaustion_analytic_of_volume_uniform_bound` — the gated capstone:
  on the ball `Metric.ball 0 r` (`r ≤ π/2`), given a per-stage non-vanishing complex field
  polymer partition function (`hden`, gated) and a volume-uniform local bound (`hbdd`,
  gated), the per-stage complex field correlations converge locally uniformly to a
  holomorphic `f`, with `f (b₀) = ↑(correlationInfinite G Λ ⟨a, b₀, 1⟩ A)` at the real
  accumulation field `b₀ ≥ 0`.  Proof: feed the field family into the generic Vitali–Porter
  provider.

## Scope
F6a proves the conditional Vitali/local-limit body under `hden` (per-stage
non-vanishing) and `hbdd` (volume-uniform bound), exactly as the `β` route
`correlationComplexAlongExhaustion_analytic_of_volume_uniform_bound`.  F6b supplies
the volume-uniform `hden`, and F6c discharges the small-coupling window to obtain a
holomorphic local limit with equality to the real infinite-volume correlation at
one field value `b₀`.  Neither result exports an unconditional full GJ Theorem
17.6.1 field derivative; real infinite-volume `HasDerivAt` remains unresolved
under #4790.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §17.6,
Theorem 17.6.1, eq. (17.6.1), p. 313.
-/

namespace IsingModel

namespace Ambient

open Filter Topology

variable {V : Type*} [DecidableEq V]

/-- **Real-axis reduction of the along-exhaustion complex field correlation** (GJ §17.6.1,
brick F6a): at a real field `b`, `fieldCorrelationℂAlongExhaustion G Λ A a (b : ℂ) n` is the
`ofReal` of the real `correlationAlongExhaustion G Λ ⟨a, b, 1⟩ A n` (`β = 1`, so `β·J = a`,
`β·h = b`), stage by stage.  On the engulfed branch this is the F4b real-axis identity
`fieldCorrelationℂ_ofReal_eq_correlation`; on the pre-engulfment branch both sides are `0`.
The field (`b`-varying) transcription of `correlationComplexAlongExhaustion_at_real_eq_ofReal`. -/
theorem fieldCorrelationℂAlongExhaustion_at_real_eq_ofReal
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (A : Finset V) (a b : ℝ) (n : ℕ) :
    fieldCorrelationℂAlongExhaustion G Λ A a (b : ℂ) n
      = ((correlationAlongExhaustion G Λ (⟨a, b, 1⟩ : IsingParams ℝ) A n : ℝ) : ℂ) := by
  unfold fieldCorrelationℂAlongExhaustion correlationAlongExhaustion
  by_cases hsub : A ⊆ Λ.volume n
  · simp only [dif_pos hsub]
    rw [correlationΛ_apply]
    have h := fieldCorrelationℂ_ofReal_eq_correlation
      (inducedGraph G (Λ.volume n)) (⟨a, b, 1⟩ : IsingParams ℝ) (liftFinset A hsub)
    simp only [one_mul] at h
    exact h
  · simp only [dif_neg hsub, Complex.ofReal_zero]

/-- **Pointwise real-axis convergence** of the along-exhaustion complex field correlation
(GJ §17.6.1, brick F6a): at a nonnegative real field `b` with `0 ≤ a`, the per-stage complex
field correlations converge to `↑(correlationInfinite G Λ ⟨a, b, 1⟩ A)`.  Casts the bridge
`fieldCorrelationℂAlongExhaustion_at_real_eq_ofReal` through
`tendsto_correlationAlongExhaustion_correlationInfinite` (ferromagnetic `⟨a, b, 1⟩`, i.e.
`0 ≤ a`, `0 ≤ b`, `0 < 1`), reusing the existing infinite-volume mechanism.  The field
transcription of `correlationComplexAlongExhaustion_tendsto_at_real`. -/
theorem fieldCorrelationℂAlongExhaustion_tendsto_at_real
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (A : Finset V) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Filter.Tendsto
      (fun n => fieldCorrelationℂAlongExhaustion G Λ A a (b : ℂ) n)
      Filter.atTop
      (nhds ((correlationInfinite G Λ (⟨a, b, 1⟩ : IsingParams ℝ) A : ℝ) : ℂ)) := by
  have h_eq : (fun n => fieldCorrelationℂAlongExhaustion G Λ A a (b : ℂ) n)
      = fun n => ((correlationAlongExhaustion G Λ (⟨a, b, 1⟩ : IsingParams ℝ) A n : ℝ) : ℂ) := by
    funext n
    exact fieldCorrelationℂAlongExhaustion_at_real_eq_ofReal G Λ A a b n
  rw [h_eq]
  exact (Complex.continuous_ofReal.tendsto _).comp
    (tendsto_correlationAlongExhaustion_correlationInfinite G Λ
      (⟨a, b, 1⟩ : IsingParams ℝ) ⟨ha, hb, one_pos⟩ A)

/-- **Infinite-volume field correlation analyticity from a volume-uniform bound** (GJ §17.6.1,
brick F6a capstone): fix a coupling `a ≥ 0` and a radius `0 < r ≤ π/2`.  On the ball
`Metric.ball 0 r`, given that the per-stage complex field polymer partition function is
non-vanishing (`hden`, gated — discharged in F6b) and that the per-stage complex field
correlations are volume-uniformly locally bounded (`hbdd`, gated), the per-stage complex
field correlations converge **locally uniformly** on the ball to a holomorphic `f`, with
`f (b₀) = ↑(correlationInfinite G Λ ⟨a, b₀, 1⟩ A)` at the real accumulation field `b₀ ≥ 0`.

The per-stage holomorphy is supplied by F5b `fieldCorrelationℂAlongExhaustion_analyticOnNhd`
(via `hden`).  The pointwise input to Vitali–Porter is furnished on the one-sided real
segment `(b₀, b₀ + δ)` (each interior field `t > 0` is ferromagnetic together with `a ≥ 0`,
`fieldCorrelationℂAlongExhaustion_tendsto_at_real`), with `(b₀ : ℂ)` an accumulation point;
the value at `b₀` is identified via pointwise uniqueness at the real point.  The proof body
consumes the family-agnostic provider `FunctionTheory.vitaliPorter_tendstoLocallyUniformlyOn`
directly (a thin field-specific glue; the `β` Vitali stack is not modified).  Here `b = β·h`
with `β = 1` and `J = a` fixed, so holomorphy in `b` is the `∂/∂h` analyticity of the
infinite-volume two-point correlation. -/
theorem fieldCorrelationℂAlongExhaustion_analytic_of_volume_uniform_bound
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (A : Finset V) (a : ℝ) (ha0 : 0 ≤ a) {r : ℝ} (hrpi : r ≤ Real.pi / 2)
    (hden : ∀ n : ℕ, ∀ w ∈ Metric.ball (0 : ℂ) r,
        fieldPolymerZℂ (inducedGraph G (Λ.volume n)) a w ≠ 0)
    (hbdd : ∀ z ∈ Metric.ball (0 : ℂ) r, ∃ ρ M : ℝ, 0 < ρ ∧
        Metric.ball z ρ ⊆ Metric.ball 0 r ∧
        ∀ n, ∀ w ∈ Metric.ball z ρ,
          ‖fieldCorrelationℂAlongExhaustion G Λ A a w n‖ ≤ M)
    {b₀ : ℝ} (hb₀0 : 0 ≤ b₀) (hb₀U : (b₀ : ℂ) ∈ Metric.ball (0 : ℂ) r) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f (Metric.ball 0 r) ∧
      TendstoLocallyUniformlyOn
        (fun n b => fieldCorrelationℂAlongExhaustion G Λ A a b n) f Filter.atTop
        (Metric.ball 0 r) ∧
      f (b₀ : ℂ) = ((correlationInfinite G Λ (⟨a, b₀, 1⟩ : IsingParams ℝ) A : ℝ) : ℂ) := by
  have hU : IsOpen (Metric.ball (0 : ℂ) r) := Metric.isOpen_ball
  have hUconn : IsPreconnected (Metric.ball (0 : ℂ) r) :=
    (convex_ball (0 : ℂ) r).isPreconnected
  -- `b₀ < r` from the ball membership (`b₀ ≥ 0`).
  have hb₀r : b₀ < r := by
    have h := hb₀U
    rwa [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hb₀0] at h
  -- one-sided real segment half-width: positive, keeps the segment `⊆ (0, r)`.
  set δ : ℝ := (r - b₀) / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  -- the real segment `(b₀, b₀ + δ)`, embedded in `ℂ`.
  set S : Set ℂ := (fun t : ℝ => (t : ℂ)) '' Set.Ioo b₀ (b₀ + δ) with hS
  have hSU : S ⊆ Metric.ball 0 r := by
    rintro z ⟨t, ht, rfl⟩
    have ht0 : 0 < t := lt_of_le_of_lt hb₀0 ht.1
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht0]
    have := ht.2
    rw [hδ] at this
    linarith
  -- pointwise limit on the segment: the real infinite-volume correlation at the real field.
  set g : ℂ → ℂ :=
    fun z => ((correlationInfinite G Λ (⟨a, z.re, 1⟩ : IsingParams ℝ) A : ℝ) : ℂ) with hg
  have hpt : ∀ z ∈ S, Filter.Tendsto
      (fun n => fieldCorrelationℂAlongExhaustion G Λ A a z n)
      Filter.atTop (nhds (g z)) := by
    rintro z ⟨t, ht, rfl⟩
    have ht0 : 0 ≤ t := le_of_lt (lt_of_le_of_lt hb₀0 ht.1)
    have key := fieldCorrelationℂAlongExhaustion_tendsto_at_real G Λ A a t ha0 ht0
    simpa [hg, Complex.ofReal_re] using key
  -- `(b₀ : ℂ)` is an accumulation point of the (one-sided) segment.
  have hacc : AccPt (b₀ : ℂ) (Filter.principal S) := by
    rw [accPt_iff_nhds]
    intro W hW
    obtain ⟨ρ, hρ, hρW⟩ := Metric.mem_nhds_iff.mp hW
    set η : ℝ := min ρ δ with hη
    have hηpos : 0 < η := lt_min hρ hδpos
    set t : ℝ := b₀ + η / 2 with ht_def
    have htβ : b₀ < t := by rw [ht_def]; linarith
    have htIoo : t ∈ Set.Ioo b₀ (b₀ + δ) := by
      refine ⟨htβ, ?_⟩
      have hηδ : η ≤ δ := min_le_right ρ δ
      rw [ht_def]; linarith
    refine ⟨(t : ℂ), ⟨?_, ?_⟩, ?_⟩
    · -- `(t : ℂ) ∈ W`
      apply hρW
      rw [Metric.mem_ball, Complex.isometry_ofReal.dist_eq, Real.dist_eq]
      have habs : |t - b₀| = η / 2 := by
        rw [show t - b₀ = η / 2 by rw [ht_def]; ring, abs_of_pos (by linarith)]
      have hηρ : η ≤ ρ := min_le_left ρ δ
      rw [habs]; linarith
    · -- `(t : ℂ) ∈ S`
      exact ⟨t, htIoo, rfl⟩
    · -- `(t : ℂ) ≠ (b₀ : ℂ)`
      exact fun h => (ne_of_gt htβ) (Complex.ofReal_inj.mp h)
  -- feed the field family into the generic Vitali–Porter provider.
  obtain ⟨f, hfdiff, hconv, _hEqOn⟩ :=
    FunctionTheory.vitaliPorter_tendstoLocallyUniformlyOn hU hUconn
      (fun n =>
        (fieldCorrelationℂAlongExhaustion_analyticOnNhd G Λ A a hrpi hden n).differentiableOn)
      hbdd hSU hb₀U hacc hpt
  refine ⟨f, hfdiff, hconv, ?_⟩
  -- identify `f (b₀)` at the real point by pointwise uniqueness.
  have hlim := hconv.tendsto_at hb₀U
  have hpt0 := fieldCorrelationℂAlongExhaustion_tendsto_at_real G Λ A a b₀ ha0 hb₀0
  exact tendsto_nhds_unique hlim hpt0

end Ambient

end IsingModel

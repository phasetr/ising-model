import IsingModel.AmbientComplexAnalyticity.Vitali.CorrelationVitaliPorter

/-!
# Real-axis Vitali application: infinite-volume correlation analyticity from a volume-uniform bound
(GJ §18.6/§18.7)

Fourth step of the infinite-volume two-point correlation-analyticity programme (Issue #4230, item D
of #4214).  This is **Ising-side content and is proven**: it builds the real-axis inputs to the
isolated Vitali–Porter axiom (via its consumer
`correlationComplexAlongExhaustion_analytic_limit_of_volume_uniform`), reducing the infinite-volume
correlation analyticity to a *single* remaining Ising hypothesis — the **volume-uniform bound** on
the per-stage complex correlations on the high-temperature open set `U`.

Given an open preconnected `U ∋ (p.β : ℂ)` on which the complex partition function is nonvanishing
(per-stage holomorphicity, #4232) and a volume-uniform bound on the per-stage correlations, we
construct a positive real segment `S = ofReal '' (a, b) ⊆ U` around `p.β` on which the correlations
converge pointwise to `correlationInfinite` (each interior point is a ferromagnetic real parameter,
`correlationComplexAlongExhaustion_tendsto_at_real`), with `(p.β : ℂ)` an accumulation point.  The
Vitali–Porter consumer then yields a holomorphic limit `f` on `U` with locally uniform convergence,
identified at `p.β` with `correlationInfinite` via #4232.

## Main result
* `correlationComplexAlongExhaustion_analytic_of_volume_uniform_bound` — `∃ f` holomorphic on `U`,
  the locally-uniform limit of the per-stage complex correlations, with
  `f (p.β) = ↑(correlationInfinite …)`.

The only remaining Ising hypothesis is the volume-uniform bound (cluster expansion), proven in a
follow-up PR; the function-theory input is the isolated Vitali–Porter axiom.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §18.6–18.7.
-/

namespace IsingModel

namespace Ambient

open Filter Topology

variable {V : Type*} [DecidableEq V]

/-- **Infinite-volume correlation analyticity from a volume-uniform bound** (GJ §18.6/§18.7): for a
ferromagnetic `p`, on an open preconnected `U ∋ (p.β : ℂ)` where the along-exhaustion complex
partition function is nonvanishing and the per-stage complex correlations are **volume-uniformly
bounded**, the per-stage complex correlations converge locally uniformly on `U` to a holomorphic
function `f`, with `f (p.β) = ↑(correlationInfinite G Λ p A)`.

The pointwise input to Vitali–Porter is supplied on a positive real segment around `p.β` (interior
points are ferromagnetic, `correlationComplexAlongExhaustion_tendsto_at_real`), with `(p.β : ℂ)` an
accumulation point; the only remaining Ising hypothesis is the volume-uniform bound `hbdd`. -/
theorem correlationComplexAlongExhaustion_analytic_of_volume_uniform_bound
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset V)
    {U : Set ℂ} (hU : IsOpen U) (hUconn : IsPreconnected U) (hβU : (p.β : ℂ) ∈ U)
    (hZ : ∀ n, ∀ β ∈ U,
      partitionFunctionComplexAlongExhaustion G Λ (p.J : ℂ) (p.h : ℂ) β n ≠ 0)
    (hbdd : ∀ z ∈ U, ∃ r M : ℝ, 0 < r ∧ Metric.ball z r ⊆ U ∧
      ∀ n, ∀ w ∈ Metric.ball z r,
        ‖correlationComplexAlongExhaustion G Λ A (p.J : ℂ) (p.h : ℂ) w n‖ ≤ M) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧
      TendstoLocallyUniformlyOn
        (fun n β => correlationComplexAlongExhaustion G Λ A (p.J : ℂ) (p.h : ℂ) β n)
        f Filter.atTop U ∧
      f (p.β : ℂ) = ((correlationInfinite G Λ p A : ℝ) : ℂ) := by
  -- a ball around `(p.β : ℂ)` inside `U`
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU (p.β : ℂ) hβU
  -- segment half-width: positive, `< ε`, and `≤ p.β`
  set δ : ℝ := min ε p.β / 2 with hδ
  have hmin_pos : 0 < min ε p.β := lt_min hε hf.hβ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hδ_lt_eps : δ < ε := by
    have := min_le_left ε p.β; rw [hδ]; linarith
  have hδ_le_beta : δ ≤ p.β := by
    have := min_le_right ε p.β; rw [hδ]; linarith [hf.hβ]
  -- the real segment, embedded in `ℂ`
  set S : Set ℂ := (fun t : ℝ => (t : ℂ)) '' Set.Ioo (p.β - δ) (p.β + δ) with hS
  have hSU : S ⊆ U := by
    rintro z ⟨t, ht, rfl⟩
    apply hεU
    rw [Metric.mem_ball, Complex.isometry_ofReal.dist_eq, Real.dist_eq]
    have : |t - p.β| < δ := by rw [abs_lt]; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    linarith
  -- pointwise limit on the segment: the real infinite-volume correlation at the real `β`-slice
  set g : ℂ → ℂ := fun z => ((correlationInfinite G Λ (⟨p.J, p.h, z.re⟩ : IsingParams ℝ) A : ℝ) : ℂ)
    with hg
  have hpt : ∀ z ∈ S, Filter.Tendsto
      (fun n => correlationComplexAlongExhaustion G Λ A (p.J : ℂ) (p.h : ℂ) z n)
      Filter.atTop (nhds (g z)) := by
    rintro z ⟨t, ht, rfl⟩
    have ht0 : 0 < t := lt_of_le_of_lt (by linarith [hδ_le_beta] : (0 : ℝ) ≤ p.β - δ) ht.1
    have hq : Ferromagnetic (⟨p.J, p.h, t⟩ : IsingParams ℝ) := ⟨hf.hJ, hf.hh, ht0⟩
    have key := correlationComplexAlongExhaustion_tendsto_at_real G Λ
      (⟨p.J, p.h, t⟩ : IsingParams ℝ) hq A
    simpa [hg, Complex.ofReal_re] using key
  -- `(p.β : ℂ)` is an accumulation point of the segment
  have hacc : AccPt (p.β : ℂ) (Filter.principal S) := by
    rw [accPt_iff_nhds]
    intro V hV
    obtain ⟨ρ, hρ, hρV⟩ := Metric.mem_nhds_iff.mp hV
    set η : ℝ := min ρ δ with hη
    have hηpos : 0 < η := lt_min hρ hδpos
    set t : ℝ := p.β + η / 2 with ht_def
    have htβ : p.β < t := by rw [ht_def]; linarith
    have htIoo : t ∈ Set.Ioo (p.β - δ) (p.β + δ) := by
      refine ⟨by linarith, ?_⟩
      have hηδ : η ≤ δ := min_le_right ρ δ
      rw [ht_def]; linarith
    refine ⟨(t : ℂ), ⟨?_, ?_⟩, ?_⟩
    · -- `(t : ℂ) ∈ V`
      apply hρV
      rw [Metric.mem_ball, Complex.isometry_ofReal.dist_eq, Real.dist_eq]
      have habs : |t - p.β| = η / 2 := by
        rw [show t - p.β = η / 2 by rw [ht_def]; ring, abs_of_pos (by linarith)]
      have hηρ : η ≤ ρ := min_le_left ρ δ
      rw [habs]; linarith
    · -- `(t : ℂ) ∈ S`
      exact ⟨t, htIoo, rfl⟩
    · -- `(t : ℂ) ≠ (p.β : ℂ)`
      exact fun h => (ne_of_gt htβ) (Complex.ofReal_inj.mp h)
  -- apply Vitali–Porter (via its correlation consumer) and identify the value at `p.β`
  obtain ⟨f, hfdiff, hconv, _hEqOn⟩ :=
    correlationComplexAlongExhaustion_analytic_limit_of_volume_uniform
      G Λ A (p.J : ℂ) (p.h : ℂ) hU hUconn hZ hbdd hSU hβU hacc hpt
  have hid := correlationComplexAlongExhaustion_vitali_identified_at_real_of_ne_zero
    G Λ p hf A hU hZ hβU hconv
  exact ⟨f, hid.1, hconv, hid.2⟩

end Ambient

end IsingModel

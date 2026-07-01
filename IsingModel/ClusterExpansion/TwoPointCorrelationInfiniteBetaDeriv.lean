import IsingModel.ClusterExpansion.TwoPointCorrelationInfiniteAnalytic
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Infinite-volume general-observable β-derivative at high temperature (GJ Thm 17.6.1, brick K5)

This module is brick **K5**, the FINAL brick, of the high-temperature-window portion of
Glimm–Jaffe Theorem 17.6.1 (p.~313; §18) for a **general observable** `A`.  It upgrades the
complex analyticity established in K4
(`correlationInfinite_latticeGraph_general_analytic_high_temp`) to a genuine **real** `β`-derivative
of the infinite-volume correlation `correlationInfinite (latticeGraph d) Λ ⟨J, 0, ·⟩ A` on the
Kotecký–Preiss high-temperature window `(0, r)`.

The proof restricts the already-holomorphic Vitali limit `f` (from K4) to the real axis:
at an interior real point `↑β` of the ball `ball 0 r`, `f` is complex-differentiable, hence
`β' ↦ (f ↑β').re` has a real `HasDerivAt`; and on the window `(f ↑β').re = correlationInfinite(β')`
(the window identity, from `correlationComplexAlongExhaustion_tendsto_at_real` + uniqueness of
limits).  No new analytic machinery is introduced — it is a mathlib composition of K4.

## Main results
* `correlationInfinite_latticeGraph_general_hasDerivAt_beta_high_temp` — the named real
  `HasDerivAt` form (derivative value `(deriv f ↑β).re` for the K4 witness `f`).
* `correlationInfinite_latticeGraph_general_differentiableAt_beta_high_temp` — the primary
  `DifferentiableAt ℝ` conclusion.

## Honest scope
K5 delivers the **β-direction, KP high-temperature-window, general-observable** differentiability
only.  It is **unconditional / axiom-free** on the window `(0, r)` (with `r` inherited from K4).
It is **NOT**: (1) the full GJ Theorem 17.6.1 analyticity throughout `σ < σ_c` (issue #4386, which
needs uniform Ornstein–Zernike control and is out of scope); (2) the `h`-direction `∂/∂h`.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), Theorem 17.6.1, p.~313; §18.
-/

namespace IsingModel

namespace Ambient

open Filter Topology

/-- **GJ Theorem 17.6.1 brick K5 (named-derivative form).**  On the KP high-temperature window
`(0, r)` the infinite-volume general-observable correlation
`β' ↦ correlationInfinite (latticeGraph d) Λ ⟨J, 0, β'⟩ A` has a real derivative at every interior
point `β`.  The derivative equals `(deriv f ↑β).re`, where `f` is the K4 Vitali witness; the value
is packaged existentially so the `β`-dependent witness is not exposed in the statement. -/
theorem correlationInfinite_latticeGraph_general_hasDerivAt_beta_high_temp
    (d : ℕ) (Λ : Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ : 0 ≤ J) (A : Finset (Fin d → ℤ)) :
    ∃ r > 0, ∀ β : ℝ, 0 < β → β < r →
      ∃ g' : ℝ,
        HasDerivAt
          (fun β' => correlationInfinite (latticeGraph d) Λ
            (⟨J, 0, β'⟩ : IsingParams ℝ) A) g' β := by
  classical
  obtain ⟨r, hrpos, hK4⟩ :=
    correlationInfinite_latticeGraph_general_analytic_high_temp d Λ J hJ A
  refine ⟨r, hrpos, ?_⟩
  intro β hβpos hβlt
  obtain ⟨f, hfdiff, hconv, _hident⟩ := hK4 β hβpos hβlt
  -- Membership of a positive real below `r` in the complex ball `ball 0 r`.
  have hmem : ∀ β' : ℝ, 0 < β' → β' < r → (β' : ℂ) ∈ Metric.ball (0 : ℂ) r := by
    intro β' hβ'pos hβ'lt
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hβ'pos]
    exact hβ'lt
  -- Window identity: on `(0, r)` the holomorphic limit `f` agrees with the real correlation.
  have hwindow : ∀ β' : ℝ, 0 < β' → β' < r →
      f (β' : ℂ) = ((correlationInfinite (latticeGraph d) Λ
        (⟨J, 0, β'⟩ : IsingParams ℝ) A : ℝ) : ℂ) := by
    intro β' hβ'pos hβ'lt
    have hstage := hconv.tendsto_at (hmem β' hβ'pos hβ'lt)
    have hferro : Ferromagnetic (⟨J, 0, β'⟩ : IsingParams ℝ) := ⟨hJ, le_rfl, hβ'pos⟩
    have hbridge :=
      correlationComplexAlongExhaustion_tendsto_at_real (latticeGraph d) Λ
        (⟨J, 0, β'⟩ : IsingParams ℝ) hferro A
    have hseq :
        (fun n => correlationComplexAlongExhaustion (latticeGraph d) Λ A
            ((⟨J, 0, β'⟩ : IsingParams ℝ).J : ℂ)
            ((⟨J, 0, β'⟩ : IsingParams ℝ).h : ℂ)
            ((⟨J, 0, β'⟩ : IsingParams ℝ).β : ℂ) n)
          = fun n => correlationComplexAlongExhaustion (latticeGraph d) Λ A
              (J : ℂ) 0 (β' : ℂ) n := by
      simp
    rw [hseq] at hbridge
    exact tendsto_nhds_unique hstage hbridge
  -- `f` is complex-differentiable at the interior real point `↑β`.
  have hβU : (β : ℂ) ∈ Metric.ball (0 : ℂ) r := hmem β hβpos hβlt
  have hfda : DifferentiableAt ℂ f (β : ℂ) :=
    hfdiff.differentiableAt (Metric.isOpen_ball.mem_nhds hβU)
  -- Restrict to the real axis and take real parts.
  have hcomp : HasDerivAt (fun y : ℝ => f (y : ℂ)) (deriv f (β : ℂ)) β :=
    hfda.hasDerivAt.comp_ofReal
  have hre : HasDerivAt (fun y : ℝ => (f (y : ℂ)).re) (deriv f (β : ℂ)).re β := by
    have hcompose := Complex.reCLM.hasFDerivAt.comp_hasDerivAt β hcomp
    simpa [Complex.reCLM_apply, Function.comp_def] using hcompose
  -- Eventual equality with the real correlation on the open window.
  have heq :
      (fun β' => correlationInfinite (latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) A)
        =ᶠ[𝓝 β] fun y : ℝ => (f (y : ℂ)).re := by
    filter_upwards [Ioo_mem_nhds hβpos hβlt] with β' hβ'
    rw [hwindow β' hβ'.1 hβ'.2, Complex.ofReal_re]
  exact ⟨(deriv f (β : ℂ)).re, hre.congr_of_eventuallyEq heq⟩

/-- **GJ Theorem 17.6.1 brick K5 (primary form).**  On the KP high-temperature window `(0, r)` the
infinite-volume general-observable correlation
`β' ↦ correlationInfinite (latticeGraph d) Λ ⟨J, 0, β'⟩ A` is real-differentiable at every interior
point `β`.  This is the FINAL brick completing the β-direction high-temperature-window portion of
GJ Theorem 17.6.1 for general observables; it is unconditional / axiom-free on the window. -/
theorem correlationInfinite_latticeGraph_general_differentiableAt_beta_high_temp
    (d : ℕ) (Λ : Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ : 0 ≤ J) (A : Finset (Fin d → ℤ)) :
    ∃ r > 0, ∀ β : ℝ, 0 < β → β < r →
      DifferentiableAt ℝ
        (fun β' => correlationInfinite (latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) A) β := by
  obtain ⟨r, hrpos, hHD⟩ :=
    correlationInfinite_latticeGraph_general_hasDerivAt_beta_high_temp d Λ J hJ A
  refine ⟨r, hrpos, ?_⟩
  intro β hβpos hβlt
  obtain ⟨g', hg'⟩ := hHD β hβpos hβlt
  exact hg'.differentiableAt

end Ambient

end IsingModel

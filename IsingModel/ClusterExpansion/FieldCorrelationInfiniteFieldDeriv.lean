import IsingModel.ClusterExpansion.FieldTwoPointCorrelationInfiniteAnalytic
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Infinite-volume reduced-field derivative at small coupling

This module derives the real reduced-field derivative of the infinite-volume
general-observable correlation from the F6c holomorphic local limit.  For fixed
`0 < r < π / 2`, sufficiently small coupling `a = βJ`, and every `b ∈ (0, r)`,
the map
`b' ↦ correlationInfinite (latticeGraph d) Λ ⟨a, b', 1⟩ A`
has a real derivative at `b`.

The proof follows the real-axis restriction used by the beta-direction K5
module.  F6c supplies one holomorphic witness with locally uniform convergence
on the whole ball.  At every positive real point in the ball, uniqueness
between that convergence and
`fieldCorrelationℂAlongExhaustion_tendsto_at_real` identifies the same witness
with the physical infinite-volume correlation.  Complex differentiability is
then restricted along `Complex.ofReal`, composed with `Complex.reCLM`, and
transferred through eventual equality on `Set.Ioo 0 r`.

The differentiated variable is the reduced field `b = βh` in the normalized
parameterization `⟨a, b, 1⟩`; this is not a full-parameter field derivative.
The endpoint `b = 0`, the full nonperturbative range, and a derivative-series
identity, sign, or uniform bound are not proved here.

References: Glimm--Jaffe, *Quantum Physics* (2nd ed., Springer, 1987),
Theorem 17.6.1, p. 313, motivates the field derivative.  The upstream
small-coupling polymer analyticity uses Friedli--Velenik, *Statistical
Mechanics of Lattice Systems* (CUP, 2017), Exercise 5.8 and Sections 5.4--5.5.
The final real-axis derivative bridge is a project-specific refinement.
-/

namespace IsingModel

namespace Ambient

open Filter Topology

/-- **Small-coupling real reduced-field derivative.**  For a nonempty general
observable `A`, a radius `0 < r < π / 2`, and sufficiently small coupling
`a = βJ`, the infinite-volume correlation in normalized parameters
`⟨a, b, 1⟩` has a real derivative with respect to the reduced field `b = βh`
at every `b ∈ (0, r)`.

The derivative is the real part of the complex derivative of an F6c
holomorphic witness.  Locally uniform convergence on the full complex ball
and uniqueness against the physical real-axis limit identify that witness on
the open real interval before the derivative is transferred.  This theorem
does not cover `b = 0`, arbitrary physical inverse temperature, the full
nonperturbative range, or a derivative formula, sign, or uniform bound.

Reference: Glimm--Jaffe, *Quantum Physics* (2nd ed.), Theorem 17.6.1,
p. 313; the precise reduced-field bridge is project-specific. -/
theorem correlationInfinite_latticeGraph_general_hasDerivAt_field_high_temp
    (d : ℕ) (Λ : Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (latticeGraph d) (Λ.volume n)).edgeSet]
    (A : Finset (Fin d → ℤ)) (hA : A.Nonempty)
    {r : ℝ} (hr0 : 0 < r) (hrpi : r < Real.pi / 2) :
    ∃ a₀ > 0, ∀ a : ℝ, 0 ≤ a → a < a₀ →
      ∀ b : ℝ, 0 < b → b < r →
        ∃ g' : ℝ,
          HasDerivAt
            (fun b' => correlationInfinite (latticeGraph d) Λ
              (⟨a, b', 1⟩ : IsingParams ℝ) A) g' b := by
  classical
  obtain ⟨a₀, ha₀pos, hF6c⟩ :=
    fieldCorrelationInfinite_latticeGraph_analytic_high_temp
      d Λ A hA hr0 hrpi
  refine ⟨a₀, ha₀pos, ?_⟩
  intro a ha0 halt b hbpos hblt
  obtain ⟨f, hfdiff, hconv, _hident⟩ :=
    hF6c a ha0 halt b (le_of_lt hbpos) hblt
  have hmem : ∀ b' : ℝ, 0 < b' → b' < r →
      (b' : ℂ) ∈ Metric.ball (0 : ℂ) r := by
    intro b' hb'pos hb'lt
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hb'pos]
    exact hb'lt
  have hwindow : ∀ b' : ℝ, 0 < b' → b' < r →
      f (b' : ℂ) = ((correlationInfinite (latticeGraph d) Λ
        (⟨a, b', 1⟩ : IsingParams ℝ) A : ℝ) : ℂ) := by
    intro b' hb'pos hb'lt
    have hstage := hconv.tendsto_at (hmem b' hb'pos hb'lt)
    have hphysical :=
      fieldCorrelationℂAlongExhaustion_tendsto_at_real
        (latticeGraph d) Λ A a b' ha0 (le_of_lt hb'pos)
    exact tendsto_nhds_unique hstage hphysical
  have hbU : (b : ℂ) ∈ Metric.ball (0 : ℂ) r :=
    hmem b hbpos hblt
  have hfda : DifferentiableAt ℂ f (b : ℂ) :=
    hfdiff.differentiableAt (Metric.isOpen_ball.mem_nhds hbU)
  have hcomp : HasDerivAt (fun y : ℝ => f (y : ℂ))
      (deriv f (b : ℂ)) b :=
    hfda.hasDerivAt.comp_ofReal
  have hre : HasDerivAt (fun y : ℝ => (f (y : ℂ)).re)
      (deriv f (b : ℂ)).re b := by
    have hcompose := Complex.reCLM.hasFDerivAt.comp_hasDerivAt b hcomp
    simpa [Complex.reCLM_apply, Function.comp_def] using hcompose
  have heq :
      (fun b' => correlationInfinite (latticeGraph d) Λ
          (⟨a, b', 1⟩ : IsingParams ℝ) A)
        =ᶠ[𝓝 b] fun y : ℝ => (f (y : ℂ)).re := by
    filter_upwards [Ioo_mem_nhds hbpos hblt] with b' hb'
    rw [hwindow b' hb'.1 hb'.2, Complex.ofReal_re]
  exact ⟨(deriv f (b : ℂ)).re, hre.congr_of_eventuallyEq heq⟩

/-- **Small-coupling real reduced-field differentiability.**  Under the same
general-observable and normalized-parameter hypotheses as
`correlationInfinite_latticeGraph_general_hasDerivAt_field_high_temp`, the
infinite-volume correlation is real-differentiable in `b = βh` at every
`b ∈ (0, r)`.

This wrapper does not add an endpoint result at `b = 0`, a full-parameter
rescaling theorem, or any derivative formula or bound.

Reference: Glimm--Jaffe, *Quantum Physics* (2nd ed.), Theorem 17.6.1,
p. 313; the precise reduced-field bridge is project-specific. -/
theorem correlationInfinite_latticeGraph_general_differentiableAt_field_high_temp
    (d : ℕ) (Λ : Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (latticeGraph d) (Λ.volume n)).edgeSet]
    (A : Finset (Fin d → ℤ)) (hA : A.Nonempty)
    {r : ℝ} (hr0 : 0 < r) (hrpi : r < Real.pi / 2) :
    ∃ a₀ > 0, ∀ a : ℝ, 0 ≤ a → a < a₀ →
      ∀ b : ℝ, 0 < b → b < r →
        DifferentiableAt ℝ
          (fun b' => correlationInfinite (latticeGraph d) Λ
            (⟨a, b', 1⟩ : IsingParams ℝ) A) b := by
  obtain ⟨a₀, ha₀pos, hHD⟩ :=
    correlationInfinite_latticeGraph_general_hasDerivAt_field_high_temp
      d Λ A hA hr0 hrpi
  refine ⟨a₀, ha₀pos, ?_⟩
  intro a ha0 halt b hbpos hblt
  obtain ⟨g', hg'⟩ := hHD a ha0 halt b hbpos hblt
  exact hg'.differentiableAt

end Ambient

end IsingModel

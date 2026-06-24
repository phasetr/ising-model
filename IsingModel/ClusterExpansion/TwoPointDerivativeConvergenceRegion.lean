import IsingModel.ClusterExpansion.TwoPointConvergenceRegion
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Locally-uniform convergence of two-point β-derivatives on the convergence sub-window

Toward eliminating the last declared axiom (§17.5 derivative-limit provider, Issue #4289 PR4a):
this file upgrades the locally-uniform convergence of the complex two-point correlations on the
convergence region `U` (`correlationInfinite_latticeGraph_two_point_analytic_on_U`, axiom-free) to
locally-uniform convergence of the **real β-derivatives** of the finite-volume correlations on the
real trace of `U`.

The mathematical content is the complex Weierstrass theorem
(`TendstoLocallyUniformlyOn.deriv`: locally-uniform convergence of holomorphic functions implies
locally-uniform convergence of their derivatives), composed with the real/complex derivative bridge
(`HasDerivAt.real_of_complex`) and the real-axis reduction
(`correlationComplexAlongExhaustion_at_real_eq_ofReal`).

This is the genuine, axiom-free sub-window form of the
`Lemma_17_5_2_DerivativeLimitProvider` input.  The cluster expansion converges only on `U`, whose
real trace `Ioo 0 β*` (with `tanh (β*·J) = twoPointHTActivityRadius (2d)`) is a *proper*
subinterval of the formal high-temperature interval `Ioo 0 (1/(J·2d))`; consuming this in the
§17.5 sharp-HLS capstone requires rescoping that capstone to `Ioo 0 β*` (Issue #4289 PR4b).

**Reference:** Glimm–Jaffe, *Quantum Physics* (2nd ed.), §17.5 pp. 311–312, §18.6–18.7. -/

namespace IsingModel
namespace ConvergenceRegion

open Filter Topology Set Ambient

/-- **Locally-uniform convergence of the two-point β-derivatives on a real sub-window of `U`**
(GJ §17.5 / §18.6–18.7).  Let `Ioo 0 c` be a real interval whose `ofReal`-image lies in the
convergence region `U d J`.  Then the finite-volume β-derivative profiles
`β ↦ ∂_β correlationAlongExhaustion ⟨J,0,β⟩ {i,j} n` converge locally uniformly on `Ioo 0 c` to the
real part of the derivative of the holomorphic infinite-volume limit.

The proof: §18 analyticity (`correlationInfinite_latticeGraph_two_point_analytic_on_U`) gives a
holomorphic limit `f` with locally-uniform convergence of the complex stage correlations on `U`;
the complex Weierstrass theorem (`TendstoLocallyUniformlyOn.deriv`) promotes this to locally-uniform
convergence of the complex derivatives; precomposing with `ofReal` and taking real parts
(uniformly continuous) restricts to `Ioo 0 c`; and the real/complex derivative bridge identifies the
restricted complex derivative's real part with the real β-derivative stage by stage. -/
theorem derivativeLimit_on_real_subinterval
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J : ℝ) (hJ : 0 ≤ J)
    {i j : Fin d → ℤ} (hij : i ≠ j) {c : ℝ} (hc : 0 < c)
    (hsub : ∀ β ∈ Set.Ioo (0 : ℝ) c, (β : ℂ) ∈ U d J) :
    ∃ g' : ℝ → ℝ,
      TendstoLocallyUniformlyOn
        (fun n β =>
          deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) ({i, j} : Finset (Fin d → ℤ)) n) β)
        g' Filter.atTop (Set.Ioo (0 : ℝ) c) := by
  classical
  -- A witness real point in the subinterval and its membership in `U`.
  have hchalf : c / 2 ∈ Set.Ioo (0 : ℝ) c := ⟨by linarith, by linarith⟩
  have hβ0U : ((c / 2 : ℝ) : ℂ) ∈ U d J := hsub _ hchalf
  -- §18 analyticity: holomorphic limit `f` and locally-uniform convergence on `U`.
  obtain ⟨f, _hf_diff, hconv, -⟩ :=
    correlationInfinite_latticeGraph_two_point_analytic_on_U d Λ J hJ hij
      (by linarith : (0 : ℝ) < c / 2) hβ0U
  -- Per-stage non-vanishing of the complex partition function on `U`.
  have hZ : ∀ n, ∀ β ∈ U d J,
      Ambient.partitionFunctionComplexAlongExhaustion (IsingModel.latticeGraph d) Λ
        (J : ℂ) 0 β n ≠ 0 := fun n β hβ =>
    partitionFunctionComplexAlongExhaustion_ne_zero_on_U d Λ J n β hβ
  -- Per-stage holomorphicity on `U` (Weierstrass differentiability hypothesis).
  have hF : ∀ᶠ n in Filter.atTop, DifferentiableOn ℂ
      (fun z => Ambient.correlationComplexAlongExhaustion (IsingModel.latticeGraph d) Λ
        ({i, j} : Finset (Fin d → ℤ)) (J : ℂ) 0 z n) (U d J) :=
    Filter.Eventually.of_forall fun n =>
      Ambient.correlationComplexAlongExhaustion_differentiableOn_of_ne_zero
        (IsingModel.latticeGraph d) Λ ({i, j} : Finset (Fin d → ℤ)) (J : ℂ) 0 hZ n
  -- Complex Weierstrass: derivatives converge locally uniformly on `U`.
  have hderiv_c :
      TendstoLocallyUniformlyOn
        (deriv ∘ fun n z =>
          Ambient.correlationComplexAlongExhaustion (IsingModel.latticeGraph d) Λ
            ({i, j} : Finset (Fin d → ℤ)) (J : ℂ) 0 z n)
        (deriv f) Filter.atTop (U d J) :=
    hconv.deriv hF (isOpen_U d J)
  -- Precompose with `ofReal` onto `Ioo 0 c`, then take real parts (uniformly continuous).
  have hmaps : Set.MapsTo ((↑) : ℝ → ℂ) (Set.Ioo (0 : ℝ) c) (U d J) := fun β hβ => hsub β hβ
  have hpre := hderiv_c.comp ((↑) : ℝ → ℂ) hmaps Complex.continuous_ofReal.continuousOn
  have hre := Complex.uniformContinuous_re.comp_tendstoLocallyUniformlyOn hpre
  -- Identify the restricted complex-derivative real part with the real β-derivative on `Ioo 0 c`.
  refine ⟨_, hre.congr (fun n β hβ => ?_)⟩
  -- The complex stage function and its differentiability at the real point.
  have hβU : (β : ℂ) ∈ U d J := hsub β hβ
  have hGn_diff : DifferentiableAt ℂ
      (fun z => Ambient.correlationComplexAlongExhaustion (IsingModel.latticeGraph d) Λ
        ({i, j} : Finset (Fin d → ℤ)) (J : ℂ) 0 z n) (β : ℂ) :=
    (Ambient.correlationComplexAlongExhaustion_differentiableOn_of_ne_zero
        (IsingModel.latticeGraph d) Λ ({i, j} : Finset (Fin d → ℤ)) (J : ℂ) 0 hZ n
      (β : ℂ) hβU).differentiableAt ((isOpen_U d J).mem_nhds hβU)
  have hGd := hGn_diff.hasDerivAt
  -- Real-axis reduction: the real part of the complex stage equals the real stage correlation.
  have hbridge : (fun x : ℝ =>
        (Ambient.correlationComplexAlongExhaustion (IsingModel.latticeGraph d) Λ
          ({i, j} : Finset (Fin d → ℤ)) (J : ℂ) 0 (x : ℂ) n).re)
      = fun x : ℝ => Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, x⟩ : IsingParams ℝ) ({i, j} : Finset (Fin d → ℤ)) n := by
    funext x
    have hofr := Ambient.correlationComplexAlongExhaustion_at_real_eq_ofReal
      (IsingModel.latticeGraph d) Λ (⟨J, 0, x⟩ : IsingParams ℝ)
      ({i, j} : Finset (Fin d → ℤ)) n
    rw [show (Ambient.correlationComplexAlongExhaustion (IsingModel.latticeGraph d) Λ
          ({i, j} : Finset (Fin d → ℤ)) (J : ℂ) (0 : ℂ) (x : ℂ) n)
        = (((Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, x⟩ : IsingParams ℝ) ({i, j} : Finset (Fin d → ℤ)) n : ℝ)) : ℂ) from hofr,
      Complex.ofReal_re]
  -- Transport the complex derivative to the real β-derivative.
  have hg := hGd.real_of_complex
  rw [hbridge] at hg
  exact (hg.deriv).symm

end ConvergenceRegion
end IsingModel

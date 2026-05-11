import IsingModel.Concrete.LatticeGraphBED
import IsingModel.ComplexAnalyticity
import IsingModel.AmbientComplexAnalyticity

/-!
# Concrete Complex log-branch construction wrappers

Narrow child module for concrete log Z / freeEnergyComplex local-branch
construction wrappers on `latticeGraph d`. 11 theorems including
`partitionFunctionComplex_ne_zero_on_leeYangSubdomain_latticeGraph`,
`partitionFunctionComplex_mapsTo_ne_zero_leeYangDomain_latticeGraph`,
`freeEnergyComplex_analyticOnNhd_slitPlane_locus_latticeGraph`,
`isOpen_freeEnergy_analyticity_locus_latticeGraph`,
`exists_logZ_branch_on_ball_of_leeYangDomain_latticeGraph`,
`exists_logZ_holomorphic_branch_on_ball_latticeGraph`,
`exists_logZ_analytic_branch_on_ball_latticeGraph`,
`exists_logZ_analyticAt_of_leeYangDomain_latticeGraph`,
`exists_freeEnergyComplex_analyticAt_branch_of_leeYangDomain_latticeGraph`,
`exists_freeEnergyComplex_analyticOnNhd_ball_latticeGraph`, and
`exists_freeEnergyComplex_differentiableOn_ball_latticeGraph`. The
theorem names are unchanged from the former `Complex` declarations.
-/

namespace IsingModel
namespace Ambient


/-- **ℤ^d `Z_ℂ ≠ 0` on `leeYangSubdomain`** (Λ-induced, ferromagnetic). -/
theorem partitionFunctionComplex_ne_zero_on_leeYangSubdomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) {h : ℂ}
    (hh : h ∈ IsingModel.leeYangSubdomain β (Fintype.card (↑Λ : Type _))) :
    IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (J : ℂ) h (β : ℂ) ≠ 0 :=
  IsingModel.partitionFunctionComplex_ne_zero_on_leeYangSubdomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ hh

/-- **ℤ^d `Z_ℂ MapsTo ≠ 0` on `leeYangDomain`** (Λ-induced,
ferromagnetic): `Set.MapsTo` restatement of the Lee-Yang
non-vanishing. -/
theorem partitionFunctionComplex_mapsTo_ne_zero_leeYangDomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) :
    Set.MapsTo (fun h : ℂ => IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) (J : ℂ) h (β : ℂ))
      IsingModel.leeYangDomain {z : ℂ | z ≠ 0} :=
  IsingModel.partitionFunctionComplex_mapsTo_ne_zero_leeYangDomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ

/-- **ℤ^d `freeEnergyComplex` `AnalyticOnNhd` on the principal-branch
`slitPlane` analyticity locus** (Λ-induced). -/
theorem freeEnergyComplex_analyticOnNhd_slitPlane_locus_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℂ) :
    AnalyticOnNhd ℂ (fun h => IsingModel.freeEnergyComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β)
      {h : ℂ | IsingModel.partitionFunctionComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β
        ∈ Complex.slitPlane} :=
  IsingModel.freeEnergyComplex_analyticOnNhd_slitPlane_locus
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β

/-- **ℤ^d `freeEnergy` analyticity locus is open** (Λ-induced). -/
theorem isOpen_freeEnergy_analyticity_locus_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℂ) :
    IsOpen {h : ℂ | IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β
        ∈ Complex.slitPlane} :=
  IsingModel.isOpen_freeEnergy_analyticity_locus
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β

/-- **ℤ^d local log-branch of `Z` on a ball in `leeYangDomain`**
(Λ-induced, ferromagnetic): primitive of `Z'/Z`. -/
theorem exists_logZ_branch_on_ball_of_leeYangDomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} {r : ℝ} (hsub : Metric.ball h₀ r ⊆ IsingModel.leeYangDomain) :
    ∃ g : ℂ → ℂ, ∀ z ∈ Metric.ball h₀ r, HasDerivAt g
        (deriv (fun h'' => IsingModel.partitionFunctionComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (J : ℂ) h'' (β : ℂ)) z
          / IsingModel.partitionFunctionComplex
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
              (J : ℂ) z (β : ℂ)) z :=
  IsingModel.exists_logZ_branch_on_ball_of_leeYangDomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ hsub

/-- **ℤ^d holomorphic log-branch of `Z` on a ball in `leeYangDomain`**
(Λ-induced, ferromagnetic): `exp g = Z` on the ball,
`g h₀ = Complex.log(Z h₀)`. -/
theorem exists_logZ_holomorphic_branch_on_ball_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hsub : Metric.ball h₀ r ⊆ IsingModel.leeYangDomain) :
    ∃ g : ℂ → ℂ,
        (∀ z ∈ Metric.ball h₀ r, Complex.exp (g z)
          = IsingModel.partitionFunctionComplex
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
              (J : ℂ) z (β : ℂ))
      ∧ g h₀ = Complex.log
          (IsingModel.partitionFunctionComplex
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
            (J : ℂ) h₀ (β : ℂ))
      ∧ ∀ z ∈ Metric.ball h₀ r, HasDerivAt g
            (deriv (fun h'' => IsingModel.partitionFunctionComplex
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
              (J : ℂ) h'' (β : ℂ)) z
              / IsingModel.partitionFunctionComplex
                  (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
                  (J : ℂ) z (β : ℂ)) z :=
  IsingModel.exists_logZ_holomorphic_branch_on_ball
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ hr hsub

/-- **ℤ^d analytic log-branch of `Z` on a ball in `leeYangDomain`**
(Λ-induced, ferromagnetic): `AnalyticOnNhd` refinement. -/
theorem exists_logZ_analytic_branch_on_ball_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hsub : Metric.ball h₀ r ⊆ IsingModel.leeYangDomain) :
    ∃ g : ℂ → ℂ,
        (∀ z ∈ Metric.ball h₀ r, Complex.exp (g z)
          = IsingModel.partitionFunctionComplex
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
              (J : ℂ) z (β : ℂ))
      ∧ g h₀ = Complex.log
          (IsingModel.partitionFunctionComplex
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
            (J : ℂ) h₀ (β : ℂ))
      ∧ AnalyticOnNhd ℂ g (Metric.ball h₀ r) :=
  IsingModel.exists_logZ_analytic_branch_on_ball
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ hr hsub

/-- **ℤ^d pointwise analytic `log Z` branch at every `h₀ ∈ leeYangDomain`**
(Λ-induced, ferromagnetic). -/
theorem exists_logZ_analyticAt_of_leeYangDomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} (hmem : h₀ ∈ IsingModel.leeYangDomain) :
    ∃ g : ℂ → ℂ,
        AnalyticAt ℂ g h₀
      ∧ Complex.exp (g h₀)
          = IsingModel.partitionFunctionComplex
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
              (J : ℂ) h₀ (β : ℂ)
      ∧ g h₀ = Complex.log
          (IsingModel.partitionFunctionComplex
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
            (J : ℂ) h₀ (β : ℂ)) :=
  IsingModel.exists_logZ_analyticAt_of_leeYangDomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ hmem

/-- **ℤ^d GJ §4.6 Thm 4.6.2 finite-volume (branch form)** (Λ-induced,
nonempty `Λ`, ferromagnetic): at every `h₀ ∈ leeYangDomain` there is an
`AnalyticAt` representative `f` with `exp(|Λ|·f) = Z` and
`f h₀ = freeEnergyComplex …`. -/
theorem exists_freeEnergyComplex_analyticAt_branch_of_leeYangDomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Nonempty (↑Λ : Type _)]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} (hmem : h₀ ∈ IsingModel.leeYangDomain) :
    ∃ f : ℂ → ℂ,
        AnalyticAt ℂ f h₀
      ∧ Complex.exp ((Fintype.card (↑Λ : Type _) : ℂ) * f h₀)
          = IsingModel.partitionFunctionComplex
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
              (J : ℂ) h₀ (β : ℂ)
      ∧ f h₀ = IsingModel.freeEnergyComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (J : ℂ) h₀ (β : ℂ) :=
  IsingModel.exists_freeEnergyComplex_analyticAt_branch_of_leeYangDomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ hmem

/-- **ℤ^d `freeEnergyComplex` local branch `AnalyticOnNhd ball`**
(Λ-induced, nonempty `Λ`, ferromagnetic). -/
theorem exists_freeEnergyComplex_analyticOnNhd_ball_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Nonempty (↑Λ : Type _)]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hsub : Metric.ball h₀ r ⊆ IsingModel.leeYangDomain) :
    ∃ f : ℂ → ℂ,
        AnalyticOnNhd ℂ f (Metric.ball h₀ r)
      ∧ ∀ z ∈ Metric.ball h₀ r,
          Complex.exp ((Fintype.card (↑Λ : Type _) : ℂ) * f z)
            = IsingModel.partitionFunctionComplex
                (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
                (J : ℂ) z (β : ℂ) :=
  IsingModel.exists_freeEnergyComplex_analyticOnNhd_ball
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ hr hsub

/-- **ℤ^d `freeEnergyComplex` local branch `DifferentiableOn ball`**
(Λ-induced, nonempty `Λ`, ferromagnetic). -/
theorem exists_freeEnergyComplex_differentiableOn_ball_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Nonempty (↑Λ : Type _)]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hsub : Metric.ball h₀ r ⊆ IsingModel.leeYangDomain) :
    ∃ f : ℂ → ℂ,
        DifferentiableOn ℂ f (Metric.ball h₀ r)
      ∧ ∀ z ∈ Metric.ball h₀ r,
          Complex.exp ((Fintype.card (↑Λ : Type _) : ℂ) * f z)
            = IsingModel.partitionFunctionComplex
                (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
                (J : ℂ) z (β : ℂ) :=
  IsingModel.exists_freeEnergyComplex_differentiableOn_ball
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ hr hsub

end Ambient

end IsingModel

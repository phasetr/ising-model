import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.ComplexAnalyticity.Branches

/-!
# ℤ^d logarithmic branches of the complex partition function

Instantiates at the subgraph induced on a fixed finite volume `Λ : Finset (Fin d → ℤ)` of
`IsingModel.latticeGraph d` the construction of a logarithm of the complex partition function
in the external field: on a ball contained in `leeYangDomain` as a primitive of the
logarithmic derivative, then as a genuine logarithm normalised at the centre by
`Complex.log`, in a form carrying the derivative identity and in a form carrying analyticity
on a neighbourhood of the ball; and, pointwise, as a germ analytic at a point of
`leeYangDomain` whose exponential and whose value reproduce the partition function and its
principal logarithm there. Every statement assumes `0 < β` and `0 < J`. The primitive form
assumes only containment of the ball in `leeYangDomain`, with no positivity of the radius;
the normalised forms assume that containment together with a positive radius; the pointwise
form assumes membership of the base point in `leeYangDomain`.
-/

namespace IsingModel
namespace Ambient

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


end Ambient
end IsingModel

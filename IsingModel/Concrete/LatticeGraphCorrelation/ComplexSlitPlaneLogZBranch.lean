import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.ComplexAnalyticity.Locus

/-!
# ℤ^d logarithm of the partition function at real parameters and on a ball

Instantiates at the subgraph induced on a fixed finite volume `Λ : Finset (Fin d → ℤ)` of
`IsingModel.latticeGraph d` statements about the logarithm of the complex partition function,
at real parameters and on a ball. At the image of a real parameter record the principal
logarithm is the cast of the real logarithm, which carries no hypothesis, and the exponential
of the cardinality of `Λ` times the complex free-energy density is the cast of the real
partition function, which assumes `Λ` nonempty and nothing else. On a ball contained in
`leeYangDomain` there is a logarithm of the partition function analytic on a neighbourhood of
the ball, one continuous on it, and one complex differentiable on it; each of those assumes
`0 < β`, `0 < J`, a positive radius and containment of the ball in `leeYangDomain`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d log-branch at real basepoint** (Λ-induced):
`Complex.log (Z_ℂ ↑p) = ↑(Real.log (Z_ℝ p))` at real parameters. -/
theorem logZ_branch_at_real_basepoint_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    Complex.log (IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (p.J : ℂ) (p.h : ℂ) (p.β : ℂ))
      = ((Real.log (IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p)) : ℂ) :=
  IsingModel.logZ_branch_at_real_basepoint
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d `exp(|Λ| · f_ℂ) = Z_ℝ` at real parameters** (Λ-induced,
nonempty `Λ`). -/
theorem exp_card_mul_freeEnergyComplex_at_real_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Nonempty (↑Λ : Type _)]
    (p : IsingParams ℝ) :
    Complex.exp ((Fintype.card (↑Λ : Type _) : ℂ) *
        IsingModel.freeEnergyComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (p.J : ℂ) (p.h : ℂ) (p.β : ℂ))
      = (IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p : ℂ) :=
  IsingModel.exp_card_mul_freeEnergyComplex_at_real
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d log-branch `AnalyticOnNhd ball`** (Λ-induced, ferromagnetic). -/
theorem exists_logZ_analyticOnNhd_ball_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hsub : Metric.ball h₀ r ⊆ IsingModel.leeYangDomain) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (Metric.ball h₀ r)
      ∧ ∀ z ∈ Metric.ball h₀ r, Complex.exp (g z)
          = IsingModel.partitionFunctionComplex
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
              (J : ℂ) z (β : ℂ) :=
  IsingModel.exists_logZ_analyticOnNhd_ball
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ hr hsub

/-- **ℤ^d log-branch `ContinuousOn ball`** (Λ-induced, ferromagnetic). -/
theorem continuous_logZ_branch_on_ball_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hsub : Metric.ball h₀ r ⊆ IsingModel.leeYangDomain) :
    ∃ g : ℂ → ℂ, ContinuousOn g (Metric.ball h₀ r) ∧
        ∀ z ∈ Metric.ball h₀ r, Complex.exp (g z)
          = IsingModel.partitionFunctionComplex
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
              (J : ℂ) z (β : ℂ) :=
  IsingModel.continuous_logZ_branch_on_ball
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ hr hsub

/-- **ℤ^d log-branch `DifferentiableOn ball`** (Λ-induced,
ferromagnetic). -/
theorem exists_logZ_differentiableOn_ball_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hsub : Metric.ball h₀ r ⊆ IsingModel.leeYangDomain) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (Metric.ball h₀ r) ∧
        ∀ z ∈ Metric.ball h₀ r, Complex.exp (g z)
          = IsingModel.partitionFunctionComplex
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
              (J : ℂ) z (β : ℂ) :=
  IsingModel.exists_logZ_differentiableOn_ball
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ hr hsub


end Ambient
end IsingModel

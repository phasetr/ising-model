import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.ComplexAnalyticity.Locus

/-!
# ℤ^d free-energy branch on a ball inside the Lee-Yang domain

Instantiates at the subgraph induced on a fixed finite volume `Λ : Finset (Fin d → ℤ)` of
`IsingModel.latticeGraph d` the existence, on a ball contained in `leeYangDomain`, of a
branch of the complex free-energy density whose exponential, scaled by the cardinality of
`Λ`, reproduces the complex partition function on that ball. The branch is produced in an
`AnalyticOnNhd` form and in a `DifferentiableOn` form, and each form assumes `Λ` nonempty,
`0 < β`, `0 < J`, a positive radius, and containment of the ball in `leeYangDomain`.
-/

namespace IsingModel
namespace Ambient

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

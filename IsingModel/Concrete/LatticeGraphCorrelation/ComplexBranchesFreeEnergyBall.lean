import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.ComplexAnalyticity.Locus

/-!
# ℤ^d `freeEnergyComplex` local-branch ball wrappers

Narrow child module for two ℤ^d
`exists_freeEnergyComplex_{analyticOnNhd,differentiableOn}_ball_latticeGraph`
wrappers extracted from `ComplexBranches.lean`. Each wrapper is a thin
pass-through to the corresponding ambient `IsingModel.exists_freeEnergyComplex_*`
lemma at `IsingModel.latticeGraph d`, conditional on `Metric.ball h₀ r ⊆ leeYangDomain`.
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

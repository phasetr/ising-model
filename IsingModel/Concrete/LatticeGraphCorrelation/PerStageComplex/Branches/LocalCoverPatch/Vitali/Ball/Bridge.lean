import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.Branches.VitaliBridge

/-!
# Local-cover Vitali ball bridge wrappers

This module contains the ball-level Vitali bridge wrapper split from
`PerStageComplex.Branches.LocalCoverPatch.Vitali.Ball`.
-/

namespace IsingModel
namespace Ambient

/-! #### Local branch-family Vitali assembly on Lee-Yang balls -/

/-- **ℤ^d local branch-family Vitali bridge on a ball**: if a chosen
per-stage branch family is analytic on a ball and converges locally uniformly
there, then its limit is holomorphic on that ball. The branch hypothesis keeps
the ball-wide exponential identity and centre normalisation in the same shape
as the strong Lee-Yang branch witnesses. -/
theorem freeEnergyComplexAlongExhaustion_branchFamily_vitali_bridge_ball_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ) {h₀ : ℂ} {r : ℝ}
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hbranch : ∀ n,
      AnalyticOnNhd ℂ (F n) (Metric.ball h₀ r)
        ∧ (∀ z ∈ Metric.ball h₀ r,
            Complex.exp ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * F n z)
              = Ambient.partitionFunctionComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ J z β n)
        ∧ F n h₀ = Ambient.freeEnergyComplexAlongExhaustion
            (IsingModel.latticeGraph d) Λ J h₀ β n)
    (hconv : TendstoLocallyUniformlyOn F f Filter.atTop (Metric.ball h₀ r)) :
    DifferentiableOn ℂ f (Metric.ball h₀ r) :=
  Ambient.freeEnergyComplexAlongExhaustion_branchFamily_vitali_bridge_ball
    (IsingModel.latticeGraph d) Λ J β hbranch hconv

end Ambient

end IsingModel

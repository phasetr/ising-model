import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.Bounds.LeeYangLower.LowerLog

/-!
# ℤ^d Lee-Yang locally bounded free-energy bounds

Part of the split per-stage complex bounds layer for the GJ §4.6 Vitali route.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d compact Lee-Yang locally bounded free-energy family**: on compact
`K ⊆ leeYangDomain`, the root-product polynomial lower bound removes the
explicit polynomial-witness hypothesis and yields `‖f_n(h)‖ ≤ C + π`. -/
theorem exists_norm_freeEnergyComplexAlongExhaustion_le_leeYang_latticeGraph_of_isCompact
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {K : Set ℂ} (hK : IsCompact K) (hKsub : K ⊆ IsingModel.leeYangDomain) :
    ∃ C : ℝ, ∀ n, ∀ h ∈ K,
      ‖Ambient.freeEnergyComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n‖ ≤ C + Real.pi :=
  Ambient.exists_norm_freeEnergyComplexAlongExhaustion_le_leeYang_of_isCompact
    (IsingModel.latticeGraph d) Λ hBED hβ hJ hK hKsub

/-- **ℤ^d ball-local Lee-Yang locally bounded free-energy family**: a closed
ball contained in `leeYangDomain` gives `‖f_n(h)‖ ≤ C + π` on the
corresponding open ball without any remaining polynomial-witness hypothesis. -/
theorem exists_norm_freeEnergyComplexAlongExhaustion_le_leeYang_latticeGraph_on_ball
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    {β J ρ : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} (hsub : Metric.closedBall h₀ ρ ⊆ IsingModel.leeYangDomain) :
    ∃ C : ℝ, ∀ n, ∀ h ∈ Metric.ball h₀ ρ,
      ‖Ambient.freeEnergyComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n‖ ≤ C + Real.pi :=
  Ambient.exists_norm_freeEnergyComplexAlongExhaustion_le_leeYang_on_ball
    (IsingModel.latticeGraph d) Λ hBED hβ hJ hsub

/-- **ℤ^d point-local Lee-Yang locally bounded free-energy family**: every
point of `leeYangDomain` has a ball on which the finite-volume free-energy
family is uniformly bounded, with polynomial lower-log control discharged by
the root-product estimate. -/
theorem exists_norm_freeEnergyComplexAlongExhaustion_le_leeYang_latticeGraph_around
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} (hmem : h₀ ∈ IsingModel.leeYangDomain) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, ∀ n, ∀ h ∈ Metric.ball h₀ ρ,
      ‖Ambient.freeEnergyComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n‖ ≤ C + Real.pi :=
  Ambient.exists_norm_freeEnergyComplexAlongExhaustion_le_leeYang_around
    (IsingModel.latticeGraph d) Λ hBED hβ hJ hmem

end Ambient
end IsingModel

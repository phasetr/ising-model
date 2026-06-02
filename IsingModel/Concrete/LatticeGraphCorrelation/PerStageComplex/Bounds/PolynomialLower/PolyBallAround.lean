import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.Bounds.PolynomialLower.PolyLocalBounded

/-!
# ℤ^d polynomial-witness ball-local and point-local bounds

Part of the split polynomial-witness lower-log and local boundedness layer.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d ball-local Lee-Yang locally bounded free-energy family from
polynomial lower witnesses**: a polynomial-witness lower normalised-log input
on a closed Lee-Yang ball gives `‖f_n(h)‖ ≤ C + π` on the corresponding open
ball. -/
theorem exists_norm_freeEnergyComplexAlongExhaustion_le_poly_lower_ly_latticeGraph_on_ball
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    {β J ρ : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} (hsub : Metric.closedBall h₀ ρ ⊆ IsingModel.leeYangDomain)
    (hPolyLower : ∃ Lε : ℝ, ∀ n, ∀ h ∈ Metric.closedBall h₀ ρ,
      ∃ ε : ℝ, 0 < ε ∧
        ε ≤ ‖(IsingModel.isingEdgePoly
          (IsingModel.graphToEdgeList
            (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
            (Real.exp (-2 * β * J)))).eval
          (IsingModel.leeYangFugacityVec (β : ℂ) h)‖ ∧
        -Lε ≤ Real.log ε / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)) :
    ∃ C : ℝ, ∀ n, ∀ h ∈ Metric.ball h₀ ρ,
      ‖Ambient.freeEnergyComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n‖ ≤ C + Real.pi :=
  Ambient.exists_norm_freeEnergyComplexAlongExhaustion_le_poly_lower_leeYang_on_ball
    (IsingModel.latticeGraph d) Λ hBED hβ hJ hsub hPolyLower

/-- **ℤ^d point-local Lee-Yang locally bounded free-energy family from
polynomial lower witnesses**: around any Lee-Yang point, a radius-dependent
polynomial-witness lower normalised-log input on a closed Lee-Yang ball gives
`‖f_n(h)‖ ≤ C + π` on the corresponding open ball. -/
theorem exists_norm_freeEnergyComplexAlongExhaustion_le_poly_lower_ly_latticeGraph_around
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} (hmem : h₀ ∈ IsingModel.leeYangDomain)
    (hPolyLower : ∀ ρ : ℝ, 0 < ρ →
      Metric.closedBall h₀ ρ ⊆ IsingModel.leeYangDomain →
      ∃ Lε : ℝ, ∀ n, ∀ h ∈ Metric.closedBall h₀ ρ,
        ∃ ε : ℝ, 0 < ε ∧
          ε ≤ ‖(IsingModel.isingEdgePoly
            (IsingModel.graphToEdgeList
              (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
              (Real.exp (-2 * β * J)))).eval
            (IsingModel.leeYangFugacityVec (β : ℂ) h)‖ ∧
          -Lε ≤ Real.log ε / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, ∀ n, ∀ h ∈ Metric.ball h₀ ρ,
      ‖Ambient.freeEnergyComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n‖ ≤ C + Real.pi :=
  Ambient.exists_norm_freeEnergyComplexAlongExhaustion_le_poly_lower_leeYang_around
    (IsingModel.latticeGraph d) Λ hBED hβ hJ hmem hPolyLower

end Ambient
end IsingModel

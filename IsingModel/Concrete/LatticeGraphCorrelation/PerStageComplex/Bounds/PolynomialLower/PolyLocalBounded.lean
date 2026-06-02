import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.Bounds.PolynomialLower.PolyLower

/-!
# ℤ^d polynomial-witness locally bounded compact wrappers

Part of the split polynomial-witness lower-log and local boundedness layer.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d Lee-Yang compact locally bounded free-energy family from polynomial
lower witnesses**: on compact `K ⊆ leeYangDomain`, a uniform lower
normalised-log bound for polynomial-factor witnesses yields one constant `C`
with `‖f_n(h)‖ ≤ C + π` for all stages and all `h ∈ K`. -/
theorem exists_norm_freeEnergyComplexAlongExhaustion_le_poly_lower_ly_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    {β J R : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {K : Set ℂ} (hK : IsCompact K) (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hR : ∀ h ∈ K, |h.re| ≤ R)
    (hPolyLower : ∃ Lε : ℝ, ∀ n, ∀ h ∈ K,
      ∃ ε : ℝ, 0 < ε ∧
        ε ≤ ‖(IsingModel.isingEdgePoly
          (IsingModel.graphToEdgeList
            (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
            (Real.exp (-2 * β * J)))).eval
          (IsingModel.leeYangFugacityVec (β : ℂ) h)‖ ∧
        -Lε ≤ Real.log ε / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)) :
    ∃ C : ℝ, ∀ n, ∀ h ∈ K,
      ‖Ambient.freeEnergyComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n‖ ≤ C + Real.pi :=
  Ambient.exists_norm_freeEnergyComplexAlongExhaustion_le_poly_lower_leeYang
    (IsingModel.latticeGraph d) Λ hBED hβ hJ hK hKsub hR hPolyLower

/-- **ℤ^d compact Lee-Yang locally bounded free-energy family from polynomial
lower witnesses**: compactness supplies the real-part bound, so only the
polynomial-witness lower normalised-log input remains as an explicit
hypothesis. -/
theorem exists_norm_freeEnergyComplexAlongExhaustion_le_poly_lower_ly_latticeGraph_of_isCompact
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {K : Set ℂ} (hK : IsCompact K) (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hPolyLower : ∃ Lε : ℝ, ∀ n, ∀ h ∈ K,
      ∃ ε : ℝ, 0 < ε ∧
        ε ≤ ‖(IsingModel.isingEdgePoly
          (IsingModel.graphToEdgeList
            (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
            (Real.exp (-2 * β * J)))).eval
          (IsingModel.leeYangFugacityVec (β : ℂ) h)‖ ∧
        -Lε ≤ Real.log ε / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)) :
    ∃ C : ℝ, ∀ n, ∀ h ∈ K,
      ‖Ambient.freeEnergyComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n‖ ≤ C + Real.pi :=
  Ambient.exists_norm_freeEnergyComplexAlongExhaustion_le_poly_lower_leeYang_of_isCompact
    (IsingModel.latticeGraph d) Λ hBED hβ hJ hK hKsub hPolyLower

end Ambient
end IsingModel

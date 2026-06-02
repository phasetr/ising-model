import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.Bounds.PolynomialLower

/-!
# ℤ^d Lee-Yang lower-log discharge bounds

Part of the split per-stage complex bounds layer for the GJ §4.6 Vitali route.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d compact Lee-Yang polynomial lower witnesses**: compact containment
in `leeYangDomain` supplies the stage-uniform lower normalised-log bound for
the Lee-Yang polynomial witnesses via the root-product estimate. -/
theorem exists_poly_lower_norm_isingEdgePoly_eval_leeYangFugacityVec_latticeGraph_on_isCompact
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {K : Set ℂ} (hK : IsCompact K) (hKsub : K ⊆ IsingModel.leeYangDomain) :
    ∃ Lε : ℝ, ∀ n, ∀ h ∈ K,
      ∃ ε : ℝ, 0 < ε ∧
        ε ≤ ‖(IsingModel.isingEdgePoly
          (IsingModel.graphToEdgeList
            (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
            (Real.exp (-2 * β * J)))).eval
          (IsingModel.leeYangFugacityVec (β : ℂ) h)‖ ∧
        -Lε ≤ Real.log ε / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) :=
  Ambient.exists_poly_lower_norm_isingEdgePoly_eval_leeYangFugacityVec_on_isCompact
    (IsingModel.latticeGraph d) Λ hβ hJ hK hKsub

/-- **ℤ^d compact Lee-Yang lower normalised-log bound**: the root-product
polynomial lower bound discharges the lower normalised-log hypothesis on
compact subsets of `leeYangDomain`. -/
theorem exists_lower_log_norm_partitionFunctionComplexAlongExhaustion_ly_latticeGraph_of_isCompact
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    {β J R : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {K : Set ℂ} (hK : IsCompact K) (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hR : ∀ h ∈ K, |h.re| ≤ R) :
    ∃ L : ℝ, ∀ n, ∀ h ∈ K,
      -L ≤ Real.log ‖Ambient.partitionFunctionComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n‖
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) :=
  Ambient.exists_lower_log_norm_partitionFunctionComplexAlongExhaustion_leeYang_of_isCompact
    (IsingModel.latticeGraph d) Λ hβ hJ hK hKsub hR

end Ambient
end IsingModel

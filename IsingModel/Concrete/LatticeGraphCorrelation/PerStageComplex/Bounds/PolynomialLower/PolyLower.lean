import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.Bounds.PolynomialLower.LeeYangUpperLower

/-!
# ℤ^d polynomial-witness lower-log bridge

Part of the split polynomial-witness lower-log and local boundedness layer.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d lower normalised-log handoff from polynomial-factor witnesses**:
if every stage and field in `K` has a positive Lee-Yang polynomial-factor
lower witness whose normalised logarithm is uniformly bounded below, then the
complex partition functions satisfy the lower normalised-log hypothesis used
by the Lee-Yang locally bounded family handoff. -/
theorem exists_lower_log_norm_partitionFunctionComplexAlongExhaustion_of_poly_lower_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    {β J R : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) {K : Set ℂ}
    (hR : ∀ h ∈ K, |h.re| ≤ R)
    (hPolyLower : ∃ Lε : ℝ, ∀ n, ∀ h ∈ K,
      ∃ ε : ℝ, 0 < ε ∧
        ε ≤ ‖(IsingModel.isingEdgePoly
          (IsingModel.graphToEdgeList
            (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
            (Real.exp (-2 * β * J)))).eval
          (IsingModel.leeYangFugacityVec (β : ℂ) h)‖ ∧
        -Lε ≤ Real.log ε / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)) :
    ∃ L : ℝ, ∀ n, ∀ h ∈ K,
      -L ≤ Real.log ‖Ambient.partitionFunctionComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n‖
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) :=
  Ambient.exists_lower_log_norm_partitionFunctionComplexAlongExhaustion_of_poly_lower
    (IsingModel.latticeGraph d) Λ hβ hJ hR hPolyLower

end Ambient
end IsingModel

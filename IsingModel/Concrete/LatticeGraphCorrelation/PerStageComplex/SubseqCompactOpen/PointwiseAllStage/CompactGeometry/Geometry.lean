import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.SubseqCompactOpen.PointwiseAllStage.RealCover

/-!
# Pointwise-normalised all-stage compact geometry extraction wrappers

Part of the split pointwise-normalised all-stage packaging layer.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d compact real finite-cover geometry from pointwise-normalised
all-stage data**: compactness extracts finitely many all-stage Lee-Yang balls
covering `K`, with a selected centre at the real field. -/
theorem
    exists_pointwiseNormAllStageCompactRealFinGeometry_of_isCompact_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)) :
    Nonempty (Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
      (IsingModel.latticeGraph d) Λ p K data) :=
  Ambient.exists_pointwiseNormAllStageCompactRealFinGeometry_of_isCompact
    (IsingModel.latticeGraph d) Λ p hK hKsub hpK data

end Ambient
end IsingModel

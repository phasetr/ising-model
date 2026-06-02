import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.Branches.RealCompact.CompactGeometry.EventualDataGeometry.Structured

/-!
# Compact geometry wrapper for pointwise-normalised eventual-overlap data

This module contains the compact local-cover `Fin n` geometry wrapper for
pointwise-normalised eventual-overlap data split from
`PerStageComplex.Branches.RealCompact.CompactGeometry.EventualDataGeometry`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d compact local-cover `Fin n` geometry from pointwise-normalised
eventual-overlap branch data**: pointwise-normalised real eventual-overlap data
projects to the structured real package, then compactness extracts and
enumerates a finite local-cover geometry over `K`. -/
theorem exists_compactLocalCoverFinGeometry_of_pointwiseNormEventualData_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : Ambient.LeeYangRealPointwiseNormalisedEventualOverlapBranchData
      (IsingModel.latticeGraph d) Λ p) :
    Nonempty (Ambient.LeeYangCompactLocalCoverFinGeometry
      (IsingModel.latticeGraph d) Λ p K) :=
  Ambient.exists_compactLocalCoverFinGeometry_of_pointwiseNormEventualData
    (IsingModel.latticeGraph d) Λ p hK hKsub hpK data

end Ambient

end IsingModel

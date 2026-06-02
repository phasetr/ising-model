import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.Branches.RealCompact.CompactGeometry.FinGeometry

/-!
# Compact geometry wrapper for structured eventual-overlap data

This module contains the compact local-cover `Fin n` geometry wrapper for
structured eventual-overlap data split from
`PerStageComplex.Branches.RealCompact.CompactGeometry.EventualDataGeometry`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d compact local-cover `Fin n` geometry from structured
eventual-overlap branch data**: structured real-centred eventual-overlap branch
data first packages into a real branch-limit family, then compactness extracts
and enumerates a finite local-cover geometry over `K`. -/
theorem exists_compactLocalCoverFinGeometry_of_realEventualOverlapBranchData_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : Ambient.LeeYangRealEventualOverlapBranchData
      (IsingModel.latticeGraph d) Λ p) :
    Nonempty (Ambient.LeeYangCompactLocalCoverFinGeometry
      (IsingModel.latticeGraph d) Λ p K) :=
  Ambient.exists_compactLocalCoverFinGeometry_of_realEventualOverlapBranchData
    (IsingModel.latticeGraph d) Λ p hK hKsub hpK data

end Ambient

end IsingModel

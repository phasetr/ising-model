import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.Branches.RealCompact.CompactGeometry.FinsetCover

/-!
# Real branch-family compact `Fin n` geometry wrapper

This module contains the compact local-cover finite-geometry wrapper split from
`PerStageComplex.Branches.RealCompact.CompactGeometry`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d compact local-cover finite geometry from a real-centred packaged
Lee-Yang local cover**: the finite subcover of a compact target is enumerated
over `Fin n`, retaining positive radii, Lee-Yang ball containment, target
coverage, and a selected real-centre index. -/
theorem exists_compactLocalCoverFinGeometry_of_leeYangRealBranchLimitFamily_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (realFamily : Ambient.LeeYangRealBranchLimitFamily
      (IsingModel.latticeGraph d) Λ p) :
    Nonempty (Ambient.LeeYangCompactLocalCoverFinGeometry
      (IsingModel.latticeGraph d) Λ p K) :=
  Ambient.exists_compactLocalCoverFinGeometry_of_leeYangRealBranchLimitFamily
    (IsingModel.latticeGraph d) Λ p hK hKsub hpK realFamily

end Ambient

end IsingModel

import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.Branches.RealCompact.StructuredPatch

/-!
# Compact finite subcover wrapper for local branch-limit families

This module contains the finite-subcover wrapper for packaged local-cover
families split from
`PerStageComplex.Branches.RealCompact.CompactGeometry.FinsetCover`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d compact finite subcover from a packaged Lee-Yang local-cover
family**: a compact target in `leeYangDomain` is covered by finitely many of
the packaged Lee-Yang local-cover balls. -/
theorem exists_finset_cover_of_isCompact_leeYangLocalBranchLimitFamily_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ) {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (family : Ambient.LeeYangLocalBranchLimitFamily
      (IsingModel.latticeGraph d) Λ J β) :
    ∃ t : Finset {h : ℂ // h ∈ IsingModel.leeYangDomain},
      K ⊆ ⋃ h₀ ∈ t,
        Metric.ball (h₀ : ℂ) (family.data h₀).radius :=
  Ambient.exists_finset_cover_of_isCompact_leeYangLocalBranchLimitFamily
    (IsingModel.latticeGraph d) Λ J β hK hKsub family

end Ambient

end IsingModel

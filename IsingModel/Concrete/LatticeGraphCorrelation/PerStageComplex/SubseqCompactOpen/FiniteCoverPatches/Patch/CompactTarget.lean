import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.SubseqCompactOpen.FiniteCoverPatches.Patch.RealCover

/-!
# SubseqCompactOpen split — compact finite real-centred cover patch wrappers

Part of the split `IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.SubseqCompactOpen`
development.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d compact finite real-centred Lee-Yang cover patching**: a compact
target set covered by a finite real-centred Lee-Yang cover inherits the
finite-cover patch, restricted to differentiability on the compact target,
while preserving the real-centre identification. -/
theorem freeEnergyComplexAlongExhaustion_compactFiniteRealCover_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    (K : Set ℂ) (n : ℕ)
    {center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain}}
    {r : Fin n → ℝ}
    (compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
      (IsingModel.latticeGraph d) Λ p K n center r) :
    ∃ g : ℂ → ℂ,
      (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
        (Metric.ball ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i))) ∧
      DifferentiableOn ℂ g K ∧
      g (p.h : ℂ) =
        ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_compactFiniteRealCover_patch
    (IsingModel.latticeGraph d) Λ p hBED hd K n compactCover

end Ambient
end IsingModel

import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.SubseqCompactOpen.FiniteCoverPatches.Patch.FiniteCover

/-!
# SubseqCompactOpen split — finite real-centred Lee-Yang cover patch wrappers

Part of the split `IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.SubseqCompactOpen`
development.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d finite real-centred Lee-Yang cover branch-limit patching**: a finite
Lee-Yang cover package with a bundled real-centre index patches to one
differentiable function on the finite union, with value
`↑Ambient.freeEnergyInfinite` at the real centre. -/
theorem freeEnergyComplexAlongExhaustion_finiteRealCoverFamily_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    (n : ℕ)
    {center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain}}
    {r : Fin n → ℝ}
    (realCover : Ambient.LeeYangFiniteRealCoverBranchLimitFamily
      (IsingModel.latticeGraph d) Λ p n center r) :
    ∃ g : ℂ → ℂ,
      (∀ i, Set.EqOn g (realCover.cover.family.limitFun i)
        (Metric.ball ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i))) ∧
      DifferentiableOn ℂ g
        (⋃ i : Fin n,
          Metric.ball ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)) ∧
      g (p.h : ℂ) =
        ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_finiteRealCoverFamily_patch
    (IsingModel.latticeGraph d) Λ p hBED hd n realCover

end Ambient
end IsingModel

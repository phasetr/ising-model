import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.Branches.LocalCoverPatch.StructuredPatch.Real.Data

/-!
# Structured local-cover real-axis family patch wrappers

This module contains the packaged structured local-cover family real-axis patch
wrapper split from `PerStageComplex.Branches.LocalCoverPatch.StructuredPatch.Real`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d packaged structured local-cover branch-limit patching with real-axis
identification**: a compatible `Ambient.LeeYangLocalBranchLimitFamily` patches
to a differentiable function on `leeYangDomain`, and a real-centre
normalisation identifies the patched value with `↑freeEnergyInfinite`. -/
theorem freeEnergyComplexAlongExhaustion_branchLimitFamily_localCover_real_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    (hp : (p.h : ℂ) ∈ IsingModel.leeYangDomain)
    (family : Ambient.LeeYangLocalBranchLimitFamily
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ))
    (hcenter : ∀ n,
      (family.data ⟨(p.h : ℂ), hp⟩).branchFamily n (p.h : ℂ)
        = Ambient.freeEnergyComplexAlongExhaustion
            (IsingModel.latticeGraph d) Λ
            (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) n) :
    ∃ g : ℂ → ℂ,
      (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
        Set.EqOn g (family.data h₀).limitFun
          (Metric.ball (h₀ : ℂ) (family.data h₀).radius)) ∧
      DifferentiableOn ℂ g IsingModel.leeYangDomain ∧
      g (p.h : ℂ) =
        ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_branchLimitFamily_localCover_real
    (IsingModel.latticeGraph d) Λ p hBED hd hp family hcenter

end Ambient

end IsingModel

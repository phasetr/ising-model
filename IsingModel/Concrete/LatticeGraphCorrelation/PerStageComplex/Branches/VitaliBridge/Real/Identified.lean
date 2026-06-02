import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.Branches.VitaliBridge.Real.Limit

/-!
# Conditional Vitali bridge identified real-axis wrappers

This module contains the real-axis identified Vitali bridge wrapper split from
`PerStageComplex.Branches.VitaliBridge.Real`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d conditional Vitali assembly with real-axis identification**:
combines holomorphicity of the Lee-Yang locally uniform limit with its
identification at a real parameter by `freeEnergyInfinite`. -/
theorem freeEnergyComplexAlongExhaustion_vitali_bridge_leeYangDomain_identified_at_real_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {f : ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ
      (fun h => Ambient.freeEnergyComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ
        (p.J : ℂ) h (p.β : ℂ) n)
      IsingModel.leeYangDomain)
    (hp : (p.h : ℂ) ∈ IsingModel.leeYangDomain)
    (hconv : TendstoLocallyUniformlyOn
      (fun n h => Ambient.freeEnergyComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ
        (p.J : ℂ) h (p.β : ℂ) n)
      f Filter.atTop IsingModel.leeYangDomain) :
    DifferentiableOn ℂ f IsingModel.leeYangDomain ∧
      f (p.h : ℂ) =
        ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_vitali_bridge_leeYangDomain_identified_at_real
    (IsingModel.latticeGraph d) Λ p hBED hd hF hp hconv

end Ambient

end IsingModel

import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.Branches.VitaliBridge.Bridge.OpenSet

/-!
# Conditional Vitali bridge Lee-Yang-domain wrapper

This module contains the Lee-Yang-domain conditional Vitali bridge wrapper
split from `PerStageComplex.Branches.VitaliBridge.Bridge`.
-/

namespace IsingModel
namespace Ambient

/-! #### Conditional Vitali assembly on the Lee-Yang domain -/

/-- **ℤ^d conditional Vitali assembly on `leeYangDomain`** for
`freeEnergyComplexAlongExhaustion`. This is the concrete Step 5 handoff
for the infinite-volume proof of GJ §4.6 Thm 4.6.2. -/
theorem freeEnergyComplexAlongExhaustion_vitali_bridge_leeYangDomain_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ) {f : ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ
      (fun h => Ambient.freeEnergyComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ J h β n)
      IsingModel.leeYangDomain)
    (hconv : TendstoLocallyUniformlyOn
      (fun n h => Ambient.freeEnergyComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ J h β n)
      f Filter.atTop IsingModel.leeYangDomain) :
    DifferentiableOn ℂ f IsingModel.leeYangDomain :=
  Ambient.freeEnergyComplexAlongExhaustion_vitali_bridge_leeYangDomain
    (IsingModel.latticeGraph d) Λ J β hF hconv

end Ambient

end IsingModel

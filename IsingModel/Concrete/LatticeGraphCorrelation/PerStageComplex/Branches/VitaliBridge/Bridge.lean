import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.Branches.StageLeeYang

/-!
# Conditional Vitali bridge wrappers

This module contains the non-real conditional Vitali bridge wrappers split from
`PerStageComplex.Branches.VitaliBridge`.
-/

namespace IsingModel
namespace Ambient

/-! #### Conditional Vitali assembly for the complex free-energy limit -/

/-- **ℤ^d conditional Vitali assembly on an open set** for
`freeEnergyComplexAlongExhaustion`: a locally uniform limit of the
per-stage holomorphic complex free energies is holomorphic on the same
open set. -/
theorem freeEnergyComplexAlongExhaustion_vitali_bridge_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    {U : Set ℂ} (hU : IsOpen U) (J β : ℂ) {f : ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ
      (fun h => Ambient.freeEnergyComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ J h β n) U)
    (hconv : TendstoLocallyUniformlyOn
      (fun n h => Ambient.freeEnergyComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ J h β n)
      f Filter.atTop U) :
    DifferentiableOn ℂ f U :=
  Ambient.freeEnergyComplexAlongExhaustion_vitali_bridge
    (IsingModel.latticeGraph d) Λ hU J β hF hconv

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

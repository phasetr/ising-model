import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplexAlongEx

/-!
# ℤ^d per-stage complex partition-function continuity

Part of the split per-stage complex bounds layer for the GJ §4.6 Vitali route.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d per-stage `Continuous` in `h`** for
`partitionFunctionComplexAlongExhaustion`. -/
theorem partitionFunctionComplexAlongExhaustion_continuous_h_stage_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ) :
    Continuous
      (fun h => Ambient.partitionFunctionComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ J h β n) :=
  Ambient.partitionFunctionComplexAlongExhaustion_continuous_h_stage
    (IsingModel.latticeGraph d) Λ J β n

end Ambient
end IsingModel

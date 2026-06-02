import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.Branches.StageLeeYang.BranchData

/-!
# Real-axis Lee-Yang branch convergence wrapper

Real-limit wrapper split from `PerStageComplex.Branches.StageLeeYang`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d real-axis convergence of `freeEnergyComplexAlongExhaustion`**
(under `DisjointTowerHypotheses` + `BoundedEdgeDensity`): at real
parameters, the complex along-exhaustion sequence converges (in `ℂ`) to
`↑(freeEnergyInfinite G Λ p)`. Pass-through of the abstract lemma. -/
theorem freeEnergyComplexAlongExhaustion_tendsto_at_real_of_disjointTowerHypotheses_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p) :
    Filter.Tendsto
      (fun n => Ambient.freeEnergyComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ
        (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) n)
      Filter.atTop
      (nhds ((Ambient.freeEnergyInfinite
        (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ)) :=
  Ambient.freeEnergyComplexAlongExhaustion_tendsto_at_real_of_disjointTowerHypotheses
    (IsingModel.latticeGraph d) Λ p hBED hd

end Ambient
end IsingModel

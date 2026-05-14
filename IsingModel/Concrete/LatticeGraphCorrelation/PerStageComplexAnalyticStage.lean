import IsingModel.Concrete.LatticeGraphBED
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.ComplexAnalyticity
import IsingModel.PeierlsInfinite
import IsingModel.AmbientComplexAnalyticity
import IsingModel.AmbientFKG
import IsingModel.AmbientLattice.SpecialCases.InfiniteVolume

/-!
# ℤ^d partitionFunctionComplexAlongEx per-stage analyticAt wrappers

Narrow child module for four ℤ^d
`partitionFunctionComplexAlongExhaustion_analyticAt_*_stage_latticeGraph`
wrappers extracted from `PerStageComplex.lean`:

* `_analyticAt_h_stage_latticeGraph`,
* `_analyticAt_J_stage_latticeGraph`,
* `_analyticAt_beta_stage_latticeGraph`,
* `_analyticAt_joint_stage_latticeGraph`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d per-stage entire in `h`** for `partitionFunctionComplexAlongExhaustion`. -/
theorem partitionFunctionComplexAlongExhaustion_analyticAt_h_stage_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ) (h₀ : ℂ) :
    AnalyticAt ℂ
      (fun h => Ambient.partitionFunctionComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ J h β n) h₀ :=
  Ambient.partitionFunctionComplexAlongExhaustion_analyticAt_h_stage
    (IsingModel.latticeGraph d) Λ J β n h₀

/-- **ℤ^d per-stage entire in `J`** for `partitionFunctionComplexAlongExhaustion`. -/
theorem partitionFunctionComplexAlongExhaustion_analyticAt_J_stage_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (h β : ℂ) (n : ℕ) (J₀ : ℂ) :
    AnalyticAt ℂ
      (fun J => Ambient.partitionFunctionComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ J h β n) J₀ :=
  Ambient.partitionFunctionComplexAlongExhaustion_analyticAt_J_stage
    (IsingModel.latticeGraph d) Λ h β n J₀

/-- **ℤ^d per-stage entire in `β`** for `partitionFunctionComplexAlongExhaustion`. -/
theorem partitionFunctionComplexAlongExhaustion_analyticAt_beta_stage_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J h : ℂ) (n : ℕ) (β₀ : ℂ) :
    AnalyticAt ℂ
      (fun β => Ambient.partitionFunctionComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ J h β n) β₀ :=
  Ambient.partitionFunctionComplexAlongExhaustion_analyticAt_beta_stage
    (IsingModel.latticeGraph d) Λ J h n β₀

/-- **ℤ^d per-stage joint entire** for `partitionFunctionComplexAlongExhaustion`. -/
theorem partitionFunctionComplexAlongExhaustion_analyticAt_joint_stage_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (n : ℕ) (z₀ : ℂ × ℂ × ℂ) :
    AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ =>
      Ambient.partitionFunctionComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ z.1 z.2.1 z.2.2 n) z₀ :=
  Ambient.partitionFunctionComplexAlongExhaustion_analyticAt_joint_stage
    (IsingModel.latticeGraph d) Λ n z₀

end Ambient
end IsingModel

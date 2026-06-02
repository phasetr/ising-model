import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.Branches.EventualOverlap.EventuallyEqOn

/-!
# Structured eventual-overlap branch-data family wrappers

This module contains the structured eventual-overlap branch-data family
wrappers split from `PerStageComplex.Branches.EventualOverlap.StructuredFamily`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d packaged local-cover branch-limit family from structured
eventual-overlap branch data**: the structured local-cover input packages
directly into `Ambient.LeeYangLocalBranchLimitFamily`. -/
theorem exists_leeYangLocalBranchLimitFamily_of_eventualOverlapBranchData_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ)
    (data : Ambient.LeeYangEventualOverlapBranchData
      (IsingModel.latticeGraph d) Λ J β) :
    Nonempty (Ambient.LeeYangLocalBranchLimitFamily
      (IsingModel.latticeGraph d) Λ J β) :=
  Ambient.exists_leeYangLocalBranchLimitFamily_of_eventualOverlapBranchData
    (IsingModel.latticeGraph d) Λ J β data

/-- **ℤ^d real-centred packaged local-cover branch-limit family from
structured eventual-overlap branch data**: the real-centred structured
local-cover input packages directly into `Ambient.LeeYangRealBranchLimitFamily`.
-/
theorem exists_leeYangRealBranchLimitFamily_of_realEventualOverlapBranchData_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (data : Ambient.LeeYangRealEventualOverlapBranchData
      (IsingModel.latticeGraph d) Λ p) :
    Nonempty (Ambient.LeeYangRealBranchLimitFamily
      (IsingModel.latticeGraph d) Λ p) :=
  Ambient.exists_leeYangRealBranchLimitFamily_of_realEventualOverlapBranchData
    (IsingModel.latticeGraph d) Λ p data

end Ambient

end IsingModel

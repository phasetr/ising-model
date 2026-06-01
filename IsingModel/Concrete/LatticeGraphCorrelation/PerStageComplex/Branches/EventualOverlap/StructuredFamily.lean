import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.Branches.EventualOverlap.EventuallyEqOn

/-!
# Structured eventual-overlap family wrappers

This module contains the structured and pointwise-normalised branch-family
wrappers.
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

/-- **ℤ^d packaged local-cover branch-limit family from pointwise-normalised
eventual-overlap branch data**: the pointwise-normalised package exposes the
underlying structured eventual-overlap branch data, which packages directly
into `Ambient.LeeYangLocalBranchLimitFamily`. -/
theorem exists_leeYangLocalBranchLimitFamily_of_pointwiseNormEventualData_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ)
    (data : Ambient.LeeYangPointwiseNormalisedEventualOverlapBranchData
      (IsingModel.latticeGraph d) Λ J β) :
    Nonempty (Ambient.LeeYangLocalBranchLimitFamily
      (IsingModel.latticeGraph d) Λ J β) :=
  Ambient.exists_leeYangLocalBranchLimitFamily_of_pointwiseNormEventualData
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

/-- **ℤ^d real-centred packaged local-cover branch-limit family from
pointwise-normalised eventual-overlap branch data**: pointwise-normalised real
eventual-overlap data projects to the structured real package, then packages
directly into `Ambient.LeeYangRealBranchLimitFamily`. -/
theorem exists_leeYangRealBranchLimitFamily_of_pointwiseNormEventualData_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (data : Ambient.LeeYangRealPointwiseNormalisedEventualOverlapBranchData
      (IsingModel.latticeGraph d) Λ p) :
    Nonempty (Ambient.LeeYangRealBranchLimitFamily
      (IsingModel.latticeGraph d) Λ p) :=
  Ambient.exists_leeYangRealBranchLimitFamily_of_pointwiseNormEventualData
    (IsingModel.latticeGraph d) Λ p data

end Ambient

end IsingModel

import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.Branches.StageLeeYang.AllStages

/-!
# All-stage Lee-Yang branch-data constructors

Branch-data wrappers split from `PerStageComplex.Branches.StageLeeYang`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d pointwise-normalised all-stage Lee-Yang branch data from positive
real parameters**: pass-through of the ambient pre-Montel branch-choice
package constructor at `latticeGraph d`. -/
theorem exists_leeYangPointwiseNormalisedAllStageBranchData_of_positive_real_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) :
    Nonempty
      (Ambient.LeeYangPointwiseNormalisedAllStageBranchData
        (IsingModel.latticeGraph d) Λ (J : ℂ) (β : ℂ)) :=
  Ambient.exists_leeYangPointwiseNormalisedAllStageBranchData_of_positive_real
    (IsingModel.latticeGraph d) Λ hβ hJ

/-- **ℤ^d closed-ball pointwise-normalised all-stage Lee-Yang branch data from
positive real parameters**: pass-through of the ambient closed-ball
pre-Montel branch-choice package constructor at `latticeGraph d`. -/
theorem
    exists_leeYangClosedBallPointwiseNormalisedAllStageBranchData_of_positive_real_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) :
    Nonempty
      (Ambient.LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        (IsingModel.latticeGraph d) Λ (J : ℂ) (β : ℂ)) :=
  Ambient.exists_leeYangClosedBallPointwiseNormalisedAllStageBranchData_of_positive_real
    (IsingModel.latticeGraph d) Λ hβ hJ

end Ambient
end IsingModel

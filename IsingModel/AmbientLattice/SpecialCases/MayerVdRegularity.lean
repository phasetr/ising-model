import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.MayerVdRegularityDifferentiable
import IsingModel.AmbientLattice.SpecialCases.MayerVdRegularityTanh
import IsingModel.AmbientLattice.SpecialCases.MayerVdRegularityVdPolymer
import IsingModel.AmbientLattice.SpecialCases.MayerVdRegularityExpansionTerm

/-!
# Continuity of the Mayer partial sum in the activity, along an exhaustion

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

At every truncation order `N`, the Mayer partial sum of the stage subgraph is continuous in
the activity on `ℝ`, and continuous on an arbitrary subset of `ℝ`.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: `mayerPartialSum` is `Continuous`**. -/
theorem mayerPartialSumAlongExhaustion_continuous
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (n : ℕ) :
    Continuous (fun t : ℝ =>
        IsingModel.mayerPartialSum
          (inducedGraph G (Λ.volume n)) N t) :=
  mayerPartialSum_Λ_continuous G (Λ.volume n) N

/-- **Along-ex: `mayerPartialSum` is `ContinuousOn`**. -/
theorem mayerPartialSumAlongExhaustion_continuousOn
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (n : ℕ) (s : Set ℝ) :
    ContinuousOn (fun t : ℝ =>
        IsingModel.mayerPartialSum
          (inducedGraph G (Λ.volume n)) N t) s :=
  mayerPartialSum_Λ_continuousOn G (Λ.volume n) N s

end Ambient
end IsingModel

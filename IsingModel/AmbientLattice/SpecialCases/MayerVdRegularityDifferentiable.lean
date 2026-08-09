import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.MayerVdRegularityDifferentiableExpansionTerm

/-!
# Differentiability of the Mayer partial sum in the activity, along an exhaustion

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

At every truncation order `N`, the Mayer partial sum of the stage subgraph is differentiable
over `ℝ` in the activity, and differentiable on an arbitrary subset of `ℝ`.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: `mayerPartialSum` is `Differentiable ℝ`**. -/
theorem mayerPartialSumAlongExhaustion_differentiable
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (n : ℕ) :
    Differentiable ℝ (fun t : ℝ =>
        IsingModel.mayerPartialSum
          (inducedGraph G (Λ.volume n)) N t) :=
  mayerPartialSum_Λ_differentiable G (Λ.volume n) N

/-- **Along-ex: `mayerPartialSum` is `DifferentiableOn ℝ`**. -/
theorem mayerPartialSumAlongExhaustion_differentiableOn
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (n : ℕ) (s : Set ℝ) :
    DifferentiableOn ℝ (fun t : ℝ =>
        IsingModel.mayerPartialSum
          (inducedGraph G (Λ.volume n)) N t) s :=
  mayerPartialSum_Λ_differentiableOn G (Λ.volume n) N s

end Ambient
end IsingModel

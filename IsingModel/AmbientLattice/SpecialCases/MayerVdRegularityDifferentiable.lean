import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion

/-!
# Mayer `Differentiable` along-ex wrappers

Narrow child module for the three §18.6 along-exhaustion
`mayerPartialSum` / `mayerExpansionTerm` `Differentiable` /
`DifferentiableOn` wrappers. Each wrapper is a thin pass-through
to the corresponding `mayer*_Λ_differentiable*` ambient lemma.
Theorem names are unchanged from the former `MayerVdRegularity`
declarations.
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

/-- **Along-ex: `mayerExpansionTerm` is `Differentiable ℝ`**. -/
theorem mayerExpansionTermAlongExhaustion_differentiable
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (k : ℕ) (n : ℕ) :
    Differentiable ℝ (fun t : ℝ =>
        IsingModel.mayerExpansionTerm
          (inducedGraph G (Λ.volume n)) k t) :=
  mayerExpansionTerm_Λ_differentiable G (Λ.volume n) k

end Ambient
end IsingModel

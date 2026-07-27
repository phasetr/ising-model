import IsingModel.AmbientLattice.SpecialCases.MayerVdRegularity
import IsingModel.Lattice

/-!
# Concrete Mayer and polymer-family regularity wrappers

Narrow child module for concrete `ℤ^d` wrappers around `mayerPartialSum`,
`mayerExpansionTerm`, and `vdPolymerFamilies_sum` regularity and tanh
forwarders. This keeps callers that only need these wrappers out of the
monolithic lattice-correlation module.
-/

namespace IsingModel
namespace Ambient

open Finset Real

/-! ### §18.6 mayerPartialSum regularity ℤ^d wraps -/

/-! ## Moved: Λ-direct mayerPartialSum regularity wrappers

The four wrappers
`mayerPartialSum_Λ_latticeGraph_continuous`,
`mayerPartialSum_Λ_latticeGraph_differentiable`,
`mayerPartialSum_Λ_latticeGraph_continuousOn`,
`mayerPartialSum_Λ_latticeGraph_differentiableOn` now live in
`MayerVdRegularityLambda.lean`. -/


/-- **ℤ^d along-ex: mayerPartialSum Continuous**. -/
theorem mayerPartialSumAlongExhaustion_latticeGraph_continuous
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (N : ℕ) (n : ℕ) :
    Continuous (fun t : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N t) :=
  Ambient.mayerPartialSumAlongExhaustion_continuous
    (IsingModel.latticeGraph d) Λ N n

/-- **ℤ^d along-ex: mayerPartialSum Differentiable ℝ**. -/
theorem mayerPartialSumAlongExhaustion_latticeGraph_differentiable
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (N : ℕ) (n : ℕ) :
    Differentiable ℝ (fun t : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N t) :=
  Ambient.mayerPartialSumAlongExhaustion_differentiable
    (IsingModel.latticeGraph d) Λ N n

/-- **ℤ^d along-ex: mayerPartialSum ContinuousOn**. -/
theorem mayerPartialSumAlongExhaustion_latticeGraph_continuousOn
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (N : ℕ) (n : ℕ) (s : Set ℝ) :
    ContinuousOn (fun t : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N t) s :=
  Ambient.mayerPartialSumAlongExhaustion_continuousOn
    (IsingModel.latticeGraph d) Λ N n s

/-- **ℤ^d along-ex: mayerPartialSum DifferentiableOn ℝ**. -/
theorem mayerPartialSumAlongExhaustion_latticeGraph_differentiableOn
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (N : ℕ) (n : ℕ) (s : Set ℝ) :
    DifferentiableOn ℝ (fun t : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N t) s :=
  Ambient.mayerPartialSumAlongExhaustion_differentiableOn
    (IsingModel.latticeGraph d) Λ N n s

/-! ## Moved: mayerExpansionTerm regularity wrappers

The four `mayerExpansionTerm_{Λ,AlongExhaustion}_latticeGraph_{continuous,differentiable}`
wrappers now live in `MayerVdRegularityExpansionTerm.lean`. -/



/-! ## Moved: ℤ^d Mayer tanh-variant regularity wrappers

The 12 ℤ^d `mayerPartialSumAlongExhaustion_latticeGraph_tanh_*`,
`mayerExpansionTerm_Λ_latticeGraph_tanh_*`, and
`mayerExpansionTermAlongExhaustion_latticeGraph_tanh_*` wrappers
(continuous/differentiable in β/J) live in
`MayerVdRegularityTanhAlongEx.lean`,
`MayerVdRegularityTanhExpansionTermLambda.lean`, and
`MayerVdRegularityTanhExpansionTermAlongEx.lean` respectively.
-/


/-! ## Moved: ℤ^d vdPolymerFamilies regularity wrappers

The 12 ℤ^d `vdPolymerFamilies_sum_Λ_latticeGraph_*` and
`vdPolymerFamilies_sumAlongExhaustion_latticeGraph_*` wrappers
(Continuous/Differentiable/HasDerivAt in t, plus tanh-variants in
β/J) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.MayerVdRegularityPolymer`.
The earlier import path is preserved by re-importing the new child.
-/

end Ambient
end IsingModel

import IsingModel.AmbientLattice.SpecialCases.MayerVdRegularity
import IsingModel.Lattice

/-!
# Concrete along-exhaustion mayerPartialSum regularity wrappers

Narrow child module for the four concrete `ℤ^d`
`mayerPartialSumAlongExhaustion_latticeGraph_*` regularity wrappers
(Continuous/Differentiable/ContinuousOn/DifferentiableOn in t). The
Λ-direct `mayerPartialSum`, the `mayerExpansionTerm`, the tanh-variant
and the `vdPolymerFamilies_sum` wrappers that this module used to carry
now live in the sibling narrow children named in the "Moved" notes
below. This keeps callers that only need these wrappers out of the
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

/-! ## Deleted: mayerExpansionTerm regularity wrappers

The four ℤ^d `mayerExpansionTerm` `Continuous` / `Differentiable` in `t`
wrappers at the Λ and along-exhaustion layers were deleted; no consumer
of them was found in this repository. -/



/-! ## Moved: ℤ^d Mayer tanh-variant regularity wrappers

The four remaining ℤ^d `mayerPartialSumAlongExhaustion_latticeGraph_tanh_*`
wrappers (continuous/differentiable in β/J) live in
`MayerVdRegularityTanhAlongEx.lean`. The eight ℤ^d `mayerExpansionTerm`
tanh `Continuous` / `Differentiable` counterparts at the Λ and
along-exhaustion layers were deleted; no consumer of them was found in
this repository.
-/


/-! ## Moved: ℤ^d vdPolymerFamilies regularity wrappers

The seven remaining ℤ^d
`vdPolymerFamilies_sumAlongExhaustion_latticeGraph_*` wrappers
(Continuous/Differentiable/HasDerivAt in t, plus tanh-variants in
β/J) now live in `MayerVdRegularityPolymerAlongEx.lean` (3, along-ex
in t) and `MayerVdRegularityPolymerTanhAlongEx.lean` (4, along-ex tanh
in β/J). The seven Λ-direct counterparts of the same two groups were
deleted; no consumer of them was found in this repository.
-/

end Ambient
end IsingModel

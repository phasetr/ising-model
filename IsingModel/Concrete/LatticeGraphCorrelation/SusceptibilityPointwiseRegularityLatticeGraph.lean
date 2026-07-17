import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.SusceptibilityPointwiseRegularityAtDifferentiableAtBeta
import IsingModel.AmbientLattice.SpecialCases.SusceptibilityPointwiseRegularityAtContinuousAtBeta

/-!
# Concrete ℤ^d-specialized susceptibilityAlongExhaustion pointwise wrappers

Narrow child module for six ℤ^d
`susceptibilityAlongExhaustion_latticeGraph_*` wrappers
(`{continuousAt,differentiableAt}_{beta_general_h,field,J}`),
each a thin pass-through to the corresponding ambient
`susceptibilityAlongExhaustion_{continuousAt,differentiableAt}_*` lemma
at `IsingModel.latticeGraph d`.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-! ### ℤ^d along-ex pointwise susceptibility wrappers -/

/-- **ℤ^d along-ex: `susceptibilityAlongExhaustion` ContinuousAt β at general h**. -/
theorem susceptibilityAlongExhaustion_latticeGraph_continuousAt_beta_general_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    ContinuousAt (fun β' =>
      Ambient.susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β'⟩ : IsingParams ℝ) i n) β :=
  Ambient.susceptibilityAlongExhaustion_continuousAt_beta_gen
    (IsingModel.latticeGraph d) Λ J h β i n

/-- **ℤ^d along-ex: `susceptibilityAlongExhaustion` DifferentiableAt β at general h**. -/
theorem susceptibilityAlongExhaustion_latticeGraph_differentiableAt_beta_general_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    DifferentiableAt ℝ (fun β' =>
      Ambient.susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β'⟩ : IsingParams ℝ) i n) β :=
  Ambient.susceptibilityAlongExhaustion_differentiableAt_beta_gen
    (IsingModel.latticeGraph d) Λ J h β i n

/-! ## Moved: field/J pointwise wrappers

The four wrappers
`susceptibilityAlongExhaustion_latticeGraph_continuousAt_field`,
`susceptibilityAlongExhaustion_latticeGraph_differentiableAt_field`,
`susceptibilityAlongExhaustion_latticeGraph_continuousAt_J`,
`susceptibilityAlongExhaustion_latticeGraph_differentiableAt_J` now
live in `SusceptibilityPointwiseRegularityLatticeGraphFieldJ.lean`. -/


end Ambient
end IsingModel

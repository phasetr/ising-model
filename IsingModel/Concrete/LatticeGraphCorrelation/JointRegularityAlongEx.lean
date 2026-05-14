import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.JointRegularity

/-!
# Concrete along-exhaustion joint regularity wrappers

Narrow child module for six ℤ^d along-exhaustion joint regularity
wrappers (`*_continuous_joint` / `*_differentiable_joint` for
`correlation`, `magnetization`, and `susceptibility`). Each wrapper is
a thin pass-through to the corresponding ambient
`*AlongExhaustion_{continuous,differentiable}_joint*` lemma at
`IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: correlationAlongExhaustion jointly Continuous in `(β, J, h)`**. -/
theorem correlationAlongExhaustion_latticeGraph_continuous_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (A : Finset (Fin d → ℤ)) (n : ℕ) :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨p.2.1, p.2.2, p.1⟩ A n) :=
  Ambient.correlationAlongExhaustion_continuous_joint_gen
    (IsingModel.latticeGraph d) Λ A n

/-- **ℤ^d along-ex: correlationAlongExhaustion jointly Differentiable ℝ in `(β, J, h)`**. -/
theorem correlationAlongExhaustion_latticeGraph_differentiable_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (A : Finset (Fin d → ℤ)) (n : ℕ) :
    Differentiable ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨p.2.1, p.2.2, p.1⟩ A n) :=
  Ambient.correlationAlongExhaustion_differentiable_joint_gen
    (IsingModel.latticeGraph d) Λ A n

/-! ## Moved: AlongEx joint mag + susc wrappers

The four wrappers
`magnetizationAlongExhaustion_latticeGraph_continuous_joint`,
`magnetizationAlongExhaustion_latticeGraph_differentiable_joint`,
`susceptibilityAlongExhaustion_latticeGraph_continuous_joint`,
`susceptibilityAlongExhaustion_latticeGraph_differentiable_joint` now
live in `JointRegularityAlongExMagSusc.lean`. -/


end Ambient
end IsingModel

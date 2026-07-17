import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaJoint

/-!
# Concrete joint regularity wrappers

This module contains concrete `latticeGraph` specializations of joint
`Continuous`, `Differentiable`, `ContinuousAt`, and `DifferentiableAt` APIs for
correlation, magnetization, and susceptibility. It is split out of the original
concrete correlation module so downstream users can depend on a narrower child
path.
-/

namespace IsingModel
namespace Ambient

/-! ### ℤ^d Λ-layer and along-exhaustion joint wrappers -/

/-- **ℤ^d Λ: correlationΛ jointly Continuous in `(β, J, h)`**. -/
theorem correlationΛ_latticeGraph_continuous_joint
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (A : Finset (↑Λ : Type _)) :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      Ambient.correlationΛ (IsingModel.latticeGraph d) Λ ⟨p.2.1, p.2.2, p.1⟩ A) :=
  Ambient.correlationΛ_continuous_joint (IsingModel.latticeGraph d) Λ A

/-- **ℤ^d Λ: correlationΛ jointly Differentiable ℝ in `(β, J, h)`**. -/
theorem correlationΛ_latticeGraph_differentiable_joint
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (A : Finset (↑Λ : Type _)) :
    Differentiable ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.correlationΛ (IsingModel.latticeGraph d) Λ ⟨p.2.1, p.2.2, p.1⟩ A) :=
  Ambient.correlationΛ_differentiable_joint (IsingModel.latticeGraph d) Λ A

/-! ## Moved: ℤ^d Λ-layer mag + susc joint regularity wrappers

The four wrappers
`magnetizationΛ_latticeGraph_{continuous,differentiable}_joint` and
`susceptibilityΛ_latticeGraph_{continuous,differentiable}_joint`
now live in `JointRegularityMagSusc.lean`. -/


/-! ## Moved: along-exhaustion joint regularity wrappers

The six wrappers
`correlationAlongExhaustion_latticeGraph_{continuous,differentiable}_joint`,
`magnetizationAlongExhaustion_latticeGraph_{continuous,differentiable}_joint`,
and `susceptibilityAlongExhaustion_latticeGraph_{continuous,differentiable}_joint`
now live in `JointRegularityAlongEx.lean`. -/

/-! ## Moved: pointwise joint regularity wrappers

The twelve `*_continuousAt_joint` / `*_differentiableAt_joint` wrappers
for `correlation`, `magnetization`, and `susceptibility` on the
Λ-layer and along-exhaustion variants now live in
`JointRegularityPointwise.lean`. -/


end Ambient
end IsingModel

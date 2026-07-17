import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaMagSuscep

/-!
# Concrete pointwise joint regularity wrappers

Narrow child module for six ℤ^d Λ-layer pointwise
`{correlation,magnetization,susceptibility}Λ_latticeGraph_*_joint`
wrappers (with `continuousAt` and `differentiableAt`). Each wrapper is a
thin pass-through to the corresponding ambient lemma at
`IsingModel.latticeGraph d`. The six AlongExhaustion variants now live in
`JointRegularityPointwiseAlongEx.lean`.
-/

namespace IsingModel
namespace Ambient


/-! ### ℤ^d joint pointwise wrappers -/

/-- **ℤ^d Λ: correlationΛ jointly ContinuousAt**. -/
theorem correlationΛ_latticeGraph_continuousAt_joint
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (A : Finset (↑Λ : Type _)) (p : ℝ × ℝ × ℝ) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ =>
      Ambient.correlationΛ (IsingModel.latticeGraph d) Λ ⟨q.2.1, q.2.2, q.1⟩ A) p :=
  Ambient.correlationΛ_continuousAt_joint (IsingModel.latticeGraph d) Λ A p

/-- **ℤ^d Λ: correlationΛ jointly DifferentiableAt**. -/
theorem correlationΛ_latticeGraph_differentiableAt_joint
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (A : Finset (↑Λ : Type _)) (p : ℝ × ℝ × ℝ) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ × ℝ =>
      Ambient.correlationΛ (IsingModel.latticeGraph d) Λ ⟨q.2.1, q.2.2, q.1⟩ A) p :=
  Ambient.correlationΛ_differentiableAt_joint (IsingModel.latticeGraph d) Λ A p

/-! ## Moved: joint pointwise mag + susc wrappers

The four wrappers
`magnetizationΛ_latticeGraph_continuousAt_joint`,
`magnetizationΛ_latticeGraph_differentiableAt_joint`,
`susceptibilityΛ_latticeGraph_continuousAt_joint`,
`susceptibilityΛ_latticeGraph_differentiableAt_joint` now live in
`JointRegularityPointwiseMagSusc.lean`. -/


/-! ## Moved: AlongExhaustion joint pointwise wrappers

The six AlongExhaustion joint pointwise wrappers
(`{correlation,magnetization,susceptibility}AlongExhaustion_latticeGraph_*_joint`
with `continuousAt` and `differentiableAt`) now live in
`JointRegularityPointwiseAlongEx.lean`. -/



end Ambient
end IsingModel
